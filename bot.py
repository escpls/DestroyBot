# Единый Telegram-бот: заявки, жалобы и модерация.
# Один процесс, один data.json.
# Зависимости: pip install "python-telegram-bot[job-queue]>=20.7"
#
# Переменные окружения:
#   BOT_TOKEN, OWNER_ID, ADMIN_CHAT_ID, MAIN_CHAT_ID  — обязательные
#   DATA_FILE (data.json), BOT_TZ (Europe/Moscow), CONTACT_HANDLE (@escpls)
#   NICKNAME_HINT — текст подсказки при некорректном никнейме
#   WARNING_TTL_DAYS (7) — через сколько дней предупреждения сгорают
import asyncio
import itertools
import string
import base64
import io
import copy
import html
from html.parser import HTMLParser
import json
import random
import logging
import os
import re
import shutil
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from types import SimpleNamespace

try:
    from zoneinfo import ZoneInfo
except ImportError:  # Python < 3.9
    ZoneInfo = None

from telegram import (BotCommand, BotCommandScopeAllGroupChats, BotCommandScopeAllPrivateChats,
                      InputMediaPhoto, InputSticker, InputFile, ReplyKeyboardRemove)
from telegram import (
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MessageEntity,
    Update,
    User,
)
from telegram.constants import ChatMemberStatus, ChatType, ParseMode
from telegram.error import BadRequest, NetworkError, TelegramError, TimedOut
from telegram.ext import (
    ApplicationHandlerStop,
    Application,
    ExtBot,
    CallbackQueryHandler,
    ChatJoinRequestHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    PersistenceInput,
    PicklePersistence,
    filters,
)

try:  # PTB >= 21
    from telegram import LinkPreviewOptions

    NO_PREVIEW = {"link_preview_options": LinkPreviewOptions(is_disabled=True)}
except ImportError:  # PTB 20.x
    NO_PREVIEW = {"disable_web_page_preview": True}

# =====================================================================
# HTML -> ТЕКСТ + ENTITIES
# Ссылка на профиль без @username делается сущностью text_mention:
# так клиент открывает профиль, даже если у человека нет username.
# Бот сам переводит наш HTML в текст + entities при каждой отправке.
# =====================================================================
def _utf16_len(text):
    return len(text.encode("utf-16-le")) // 2


class _HtmlToEntities(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.plain = ""
        self.entities = []
        self._open = []  # (тег, атрибуты, смещение utf-16, смещение в python-строке)

    def handle_starttag(self, tag, attrs):
        self._open.append((tag, dict(attrs), _utf16_len(self.plain), len(self.plain)))

    def handle_endtag(self, tag):
        for index in range(len(self._open) - 1, -1, -1):
            if self._open[index][0] == tag:
                name, attrs, offset, py_start = self._open.pop(index)
                length = _utf16_len(self.plain) - offset
                entity = self._make_entity(name, attrs, offset, length, self.plain[py_start:])
                if entity is not None:
                    self.entities.append(entity)
                return

    def handle_data(self, data):
        self.plain += data

    @staticmethod
    def _make_entity(name, attrs, offset, length, inner_text):
        if length <= 0:
            return None
        simple = {"b": "bold", "strong": "bold", "i": "italic", "em": "italic", "u": "underline",
                  "s": "strikethrough", "code": "code", "pre": "pre"}
        if name in simple:
            return MessageEntity(type=simple[name], offset=offset, length=length)
        if name == "tg-emoji":
            emoji_id = attrs.get("emoji-id") or ""
            if emoji_id:
                return MessageEntity(type="custom_emoji", offset=offset, length=length, custom_emoji_id=emoji_id)
            return None
        if name == "a":
            href = attrs.get("href") or ""
            if href.startswith("tg://user?id="):
                user_id = int(href.split("=", 1)[1])
                user = User(id=user_id, first_name=inner_text or "Пользователь", is_bot=False)
                return MessageEntity(type="text_mention", offset=offset, length=length, user=user)
            if href:
                return MessageEntity(type="text_link", offset=offset, length=length, url=href)
        return None  # blockquote и прочие теги оставляем просто текстом


def html_to_entities(text):
    parser = _HtmlToEntities()
    parser.feed(text)
    parser.close()
    return parser.plain, parser.entities


class HtmlBot(ExtBot):
    """Перехватывает отправку: если передан parse_mode=HTML, превращает текст в entities."""

    @staticmethod
    def _convert(kwargs, text_key, entities_key):
        if kwargs.get("parse_mode") != ParseMode.HTML:
            return kwargs
        kwargs = dict(kwargs)
        kwargs.pop("parse_mode", None)
        value = kwargs.get(text_key)
        if value is None:
            return kwargs
        plain, entities = html_to_entities(value)
        kwargs[text_key] = plain
        if entities:
            kwargs[entities_key] = entities
        return kwargs

    async def send_message(self, chat_id, text, *args, **kwargs):
        kwargs = self._convert({"text": text, **kwargs}, "text", "entities")
        text = kwargs.pop("text")
        return await super().send_message(chat_id, text, *args, **kwargs)

    async def edit_message_text(self, text, *args, **kwargs):
        kwargs = self._convert({"text": text, **kwargs}, "text", "entities")
        text = kwargs.pop("text")
        return await super().edit_message_text(text, *args, **kwargs)

    async def send_photo(self, chat_id, photo, *args, **kwargs):
        kwargs = self._convert(kwargs, "caption", "caption_entities")
        return await super().send_photo(chat_id, photo, *args, **kwargs)

    async def edit_message_caption(self, *args, **kwargs):
        kwargs = self._convert(kwargs, "caption", "caption_entities")
        return await super().edit_message_caption(*args, **kwargs)

    async def copy_message(self, chat_id, from_chat_id, message_id, *args, **kwargs):
        kwargs = self._convert(kwargs, "caption", "caption_entities")
        return await super().copy_message(chat_id, from_chat_id, message_id, *args, **kwargs)


logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
# httpx на уровне INFO пишет в лог URL с токеном бота — глушим.
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)
logger = logging.getLogger(__name__)


# =====================================================================
# НАСТРОЙКИ
# =====================================================================
MUTE_DURATIONS = {
    "1h": ("1 час", timedelta(hours=1)),
    "6h": ("6 часов", timedelta(hours=6)),
    "1d": ("1 день", timedelta(days=1)),
    "3d": ("3 дня", timedelta(days=3)),
    "7d": ("7 дней", timedelta(days=7)),
    "30d": ("30 дней", timedelta(days=30)),
}


def _env_int(name, default=0):
    raw = os.getenv(name, "").strip()
    if not raw:
        return default
    try:
        return int(raw)
    except ValueError:
        raise RuntimeError(f"Переменная окружения {name} должна быть числом")


BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
OWNER_ID = _env_int("OWNER_ID")
ADMIN_CHAT_ID = _env_int("ADMIN_CHAT_ID")
MAIN_CHAT_ID = _env_int("MAIN_CHAT_ID")
DATA_FILE = Path(os.getenv("DATA_FILE", "data.json"))
DATABASE_URL = os.getenv("DATABASE_URL", "").strip()  # если задана, данные хранятся в PostgreSQL
CONTACT_HANDLE = os.getenv("CONTACT_HANDLE", "@escpls")
# Minecraft Java Edition: 3–16 символов, только латинские буквы, цифры и _ .
# Не переопределяем это правило через NICKNAME_REGEX в настройках хостинга.
NICKNAME_RE = re.compile(r"[A-Za-z0-9_]{3,16}")
NICKNAME_HINT = os.getenv(
    "NICKNAME_HINT", "Допустимы латинские буквы, цифры и «_», длина 3–16 символов."
)

APPLICATION_COOLDOWN = 60                       # сек между заявками одного человека
COMPLAINT_COOLDOWN = 30                         # сек между жалобами одного человека
INVITE_TTL = timedelta(days=1)                  # срок жизни ссылки-приглашения
CONTACT_TTL = timedelta(hours=24)               # диалог с пользователем гаснет сам
APPLICATION_MAX_AGE = timedelta(days=7)         # заявка без решения закрывается сама
WARNING_TTL = timedelta(days=_env_int("WARNING_TTL_DAYS", 7))
MAP_LIMIT = 5000                                # лимит записей в таблицах message_id -> ...


def _load_tz():
    name = os.getenv("BOT_TZ", "Europe/Moscow")
    if ZoneInfo is not None:
        try:
            return ZoneInfo(name)
        except Exception:
            logger.warning("Часовой пояс %s не найден (pip install tzdata), использую UTC", name)
    return timezone.utc


TZ = _load_tz()

DEFAULT_TEMPLATE = (
    "Привет! Чтобы подать заявку на вступление в беседу, "
    "отправь свою фотографию, а следующим сообщением "
    "напиши свой никнейм."
)
DEFAULT_DATA = {
    "template_text": DEFAULT_TEMPLATE,
    "template_photo": None,
    "admins": [],
    "admin_chats": {},
    "applications": {},
    "admin_message_map": {},       # id сообщения-карточки заявки -> id заявки
    "contact_message_map": {},     # id сообщений диалога с пользователем -> id заявки
    "next_application_id": 1,
    "blocked_users": [],
    "user_blocks": {},
    "admin_log": [],
    "last_submission_at": {},
    "complaint_number": 0,
    "blocked_reports": [],
    "warnings": {},
    "warning_expires": {},         # когда у участника сгорают предупреждения
    "punishments": {},
    "complaints": {},
    "users": {},
    "expiry_queue": [],            # истекшие мут/предупреждения, ждут уведомления админам
}


# =====================================================================
# ХРАНИЛИЩЕ
# =====================================================================
_last_backup = 0.0


_pg_conn = None


def _pg_connect():
    global _pg_conn
    import psycopg  # нужен только при DATABASE_URL
    _pg_conn = psycopg.connect(DATABASE_URL, autocommit=True)
    with _pg_conn.cursor() as cur:
        cur.execute("CREATE TABLE IF NOT EXISTS bot_state ("
                    "id INT PRIMARY KEY, payload JSONB NOT NULL, "
                    "updated_at TIMESTAMPTZ NOT NULL DEFAULT now())")
    return _pg_conn


def _pg_run(action):
    """Выполняет запрос к базе; при обрыве соединения переподключается один раз."""
    import psycopg
    global _pg_conn
    for attempt in (1, 2):
        try:
            if _pg_conn is None or _pg_conn.closed:
                _pg_connect()
            return action(_pg_conn)
        except psycopg.OperationalError:
            _pg_conn = None
            if attempt == 2:
                raise


def _pg_load():
    def action(conn):
        with conn.cursor() as cur:
            cur.execute("SELECT payload FROM bot_state WHERE id = 1")
            row = cur.fetchone()
        return row[0] if row else None
    return _pg_run(action)


def _pg_save(payload):
    from psycopg.types.json import Jsonb

    def action(conn):
        with conn.cursor() as cur:
            cur.execute(
                "INSERT INTO bot_state (id, payload, updated_at) VALUES (1, %s, now()) "
                "ON CONFLICT (id) DO UPDATE SET payload = EXCLUDED.payload, updated_at = now()",
                (Jsonb(payload),),
            )
    _pg_run(action)


def _write_json(obj):
    if DATABASE_URL:
        _pg_save(obj)
        return
    DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    temp_file = DATA_FILE.with_suffix(DATA_FILE.suffix + ".tmp")
    with temp_file.open("w", encoding="utf-8") as file:
        json.dump(obj, file, ensure_ascii=False, indent=2)
    temp_file.replace(DATA_FILE)


def save_data():
    """Атомарная запись + резервная копия data.json.bak не чаще раза в 10 минут."""
    global _last_backup
    if not DATABASE_URL and DATA_FILE.exists() and time.time() - _last_backup > 600:
        try:
            shutil.copy2(DATA_FILE, DATA_FILE.with_suffix(DATA_FILE.suffix + ".bak"))
            _last_backup = time.time()
        except OSError:
            logger.warning("Не удалось создать резервную копию данных")
    _write_json(data)


def load_data():
    result = copy.deepcopy(DEFAULT_DATA)
    stored = _pg_load() if DATABASE_URL else None
    if stored is None:
        if not DATA_FILE.exists():
            _write_json(result)
            return result
        if DATABASE_URL:
            logger.info("База пуста: переносим данные из %s", DATA_FILE)
        try:
            with DATA_FILE.open("r", encoding="utf-8") as file:
                stored = json.load(file)
        except (OSError, json.JSONDecodeError) as exc:
            raise RuntimeError(f"Не удалось прочитать {DATA_FILE}. Файл не был перезаписан: {exc}") from exc
    if not isinstance(stored, dict):
        raise RuntimeError("Данные должны быть JSON-объектом. Ничего не перезаписано.")
    result.update(stored)
    for key, default in DEFAULT_DATA.items():
        if key == "template_photo":
            if result.get(key) is not None and not isinstance(result.get(key), str):
                result[key] = None
            continue
        if key not in result or not isinstance(result[key], type(default)):
            result[key] = copy.deepcopy(default)
    admins = []
    for item in result.get("admins", []):
        try:
            item = int(item)
        except (TypeError, ValueError):
            continue
        if item not in admins:
            admins.append(item)
    result["admins"] = admins
    return result


data = load_data()


# =====================================================================
# ОБЩИЕ ПОМОЩНИКИ
# =====================================================================
def esc(value):
    return html.escape(str(value), quote=True)


def now_utc():
    return datetime.now(timezone.utc)


def parse_dt(text):
    if not text:
        return None
    try:
        dt = datetime.fromisoformat(text)
    except (TypeError, ValueError):
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


MONTHS_GEN = ["января", "февраля", "марта", "апреля", "мая", "июня",
              "июля", "августа", "сентября", "октября", "ноября", "декабря"]


def fmt_dt(dt):
    local = dt.astimezone(TZ)
    return f"{local.day} {MONTHS_GEN[local.month - 1]} {local.year}, {local:%H:%M}"


def is_owner(user_id):
    return bool(OWNER_ID) and user_id == OWNER_ID


def admin_ids():
    return {int(x) for x in data.get("admins", [])}


def has_access(user_id):
    if user_id is None:
        return False
    return is_owner(user_id) or int(user_id) in admin_ids()




async def safe_edit(message, text, **kwargs):
    """edit_text, который не падает на «message is not modified»."""
    try:
        await message.edit_text(text, **kwargs)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


def map_message(map_name, message_id, value):
    table = data.setdefault(map_name, {})
    table[str(message_id)] = value
    if len(table) > MAP_LIMIT:
        for key in list(table)[: len(table) - MAP_LIMIT]:
            table.pop(key, None)


def log_action(actor_id, action, target_id=None, app_id=None, details=None):
    """История действий Администрации (последние 500 событий)."""
    entry = {
        "at": now_utc().isoformat(),
        "actor_id": int(actor_id) if actor_id is not None else None,
        "action": str(action),
        "target_id": int(target_id) if target_id is not None else None,
        "app_id": int(app_id) if app_id is not None else None,
        "details": str(details) if details else None,
    }
    log = data.setdefault("admin_log", [])
    log.append(entry)
    del log[:-500]
    save_data()


ACTION_LABELS = {
    "application_accepted": "Заявка одобрена",
    "application_accepted_delivery_failed": "Заявка одобрена (ссылка не доставлена)",
    "application_rejected": "Заявка отклонена",
    "application_cancelled": "Заявка отменена (карточка удалена)",
    "application_expired": "Заявка закрыта: срок рассмотрения истек",
    "invite_revoked": "Ссылка отозвана",
    "invite_resent": "Ссылка выдана повторно",
    "member_joined": "Вступление в чат",
    "log_cleared": "Журнал очищен владельцем",
    "application_reset": "Заявка сброшена владельцем",
    "join_declined": "Отклонен чужой запрос на вступление",
    "contact_started": "Диалог с пользователем начат",
    "contact_ended": "Диалог с пользователем завершен",
    "applications_blocked": "Заблокирована подача заявок",
    "applications_unblocked": "Разблокирована подача заявок",
    "admin_access_granted": "Выданы права администратора",
    "admin_access_revoked": "Сняты права администратора",
    "warning_given": "Выдано предупреждение",
    "warning_removed": "Снято предупреждение",
    "warnings_cleared": "Сброшены предупреждения",
    "mute_given": "Выдан мут",
    "mute_removed": "Снят мут",
    "ban_given": "Выдана блокировка",
    "ban_removed": "Снята блокировка",
    "punishment_removed": "Снято наказание",
    "reports_blocked": "Запрещены жалобы",
    "reports_unblocked": "Разрешены жалобы",
}


# =====================================================================
# ПОЛЬЗОВАТЕЛИ И ССЫЛКИ НА ПРОФИЛИ
# =====================================================================
def user_name(user):
    if not user:
        return "Пользователь"
    if user.full_name:
        return user.full_name
    if user.username:
        return f"@{user.username}"
    return f"ID {user.id}"


def remember_user(user, save=True):
    if not user:
        return
    info = {"id": user.id, "name": user_name(user), "username": user.username}
    if data["users"].get(str(user.id)) != info:
        data["users"][str(user.id)] = info
        if save:
            save_data()


def remember_user_from_saved_id(user_id):
    user_id = int(user_id)
    if str(user_id) not in data["users"]:
        data["users"][str(user_id)] = {"id": user_id, "name": f"ID {user_id}", "username": None}


def build_profile_link(user_id, name, username=None):
    """Со username — https://t.me/username (открывается всегда), иначе tg://user?id=…"""
    safe_name = esc(name or "Пользователь")
    username = str(username).lstrip("@") if username else ""
    if username:
        return f'<a href="https://t.me/{esc(username)}">{safe_name}</a>'
    return f'<a href="tg://user?id={int(user_id)}">{safe_name}</a>'


def profile_link(user_id, name, username=None):
    try:
        user_id = int(user_id)
    except (TypeError, ValueError):
        return esc(name or "Пользователь")
    if not username:
        username = (data["users"].get(str(user_id)) or {}).get("username")
    return build_profile_link(user_id, name, username)


def mention_user(user):
    if not user:
        return "Пользователь"
    remember_user(user)
    return build_profile_link(user.id, user_name(user), user.username)


def saved_user_link(user_id, name=None, username=None):
    try:
        user_id = int(user_id)
    except (TypeError, ValueError):
        return esc(name or username or "Пользователь")
    if user_id < 0:  # чат или канал: tg://user для них не работает
        return esc(name or username or "Чат")
    saved = data["users"].get(str(user_id)) or {}
    display_name = (
    name
    or saved.get("first_name")
    or saved.get("name")
    or saved.get("username")
    or username
    or f"ID {user_id}"
)
    return build_profile_link(user_id, display_name, saved.get("username") or username)


def saved_user_link_with_id(user_id, name=None, username=None):
    """Как saved_user_link, но если у человека нет username (ссылка по ID может не открываться),
    добавляет ID в <code> — его можно скопировать и найти профиль вручную."""
    if int(user_id) < 0:
        return f"Чат (<code>{int(user_id)}</code>)"
    return saved_user_link(user_id, name, username)  # ID уже добавляется в build_profile_link


def plain_user_with_id(user_id, name=None):
    """Имя без ссылки + ID в <code>: его можно скопировать и найти профиль вручную."""
    return f"{esc(name or 'Пользователь')} (<code>{int(user_id)}</code>)"


def find_user_by_username(username):
    username = username.lower().lstrip("@")
    for user_id, info in data["users"].items():
        saved = info.get("username")
        if saved and saved.lower() == username:
            return int(user_id), info
    return None, None


def message_link(chat_id, message_id):
    chat_id_string = str(chat_id)
    if chat_id_string.startswith("-100"):
        return f"https://t.me/c/{chat_id_string[4:]}/{message_id}"
    return None


# =====================================================================
# ДОСТУП
# =====================================================================
async def require_staff(update, context, admin_chat_only=False):
    """Единая проверка прав для команд. В основном чате посторонним не отвечаем."""
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return False
    if chat.type == ChatType.PRIVATE:  # владелец проверяет команды в личке, не засоряя админ-чат
        user = update.effective_user
        return bool(user) and is_owner(user.id)
    allowed_chats = (ADMIN_CHAT_ID,) if admin_chat_only else (MAIN_CHAT_ID, ADMIN_CHAT_ID)
    if chat.id not in allowed_chats:
        return False

    sender_chat = message.sender_chat
    if sender_chat:
        if sender_chat.id == chat.id:
            await message.reply_text(
                "❗ Бот не видит, кто пишет от имени чата. "
                "Отключи анонимность администратора и повтори команду."
            )
            return False
        ok = sender_chat.id in admin_ids()
    else:
        user = update.effective_user
        ok = bool(user) and has_access(user.id)

    if not ok and chat.id == ADMIN_CHAT_ID:
        await message.reply_text("❌ Доступ запрещен.")
    return ok


async def is_main_chat_admin(context, user_id):
    try:
        member = await context.bot.get_chat_member(MAIN_CHAT_ID, user_id)
    except TelegramError:
        return False
    return member.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)


# =====================================================================
# БЛОКИРОВКИ ПОДАЧИ ЗАЯВОК
# =====================================================================
FOREVER = datetime.max.replace(tzinfo=timezone.utc)


def get_user_block(user_id):
    """Действующая блокировка или None."""
    user_id = int(user_id)
    if user_id in {int(x) for x in data.get("blocked_users", [])}:
        return {"until": None, "reason": "Бессрочная блокировка"}
    blocks = data.setdefault("user_blocks", {})
    block = blocks.get(str(user_id))
    if not block:
        return None
    if not block.get("until"):
        return block
    until = parse_dt(block["until"])
    if until is None:  # поврежденная дата не должна снимать блокировку
        return block
    if now_utc() >= until:
        blocks.pop(str(user_id), None)
        save_data()
        return None
    return block


def block_end(block):
    if not block.get("until"):
        return FOREVER
    return parse_dt(block["until"]) or FOREVER


def block_expiry_text(block):
    if not block.get("until"):
        return "навсегда"
    until = parse_dt(block["until"])
    return fmt_dt(until) if until else "срок неизвестен"


def apply_user_block(user_id, hours=24, reason="Отказ в заявке", blocked_by=None):
    user_id = int(user_id)
    until_text = None if hours is None else (now_utc() + timedelta(hours=hours)).isoformat()
    data.setdefault("user_blocks", {})[str(user_id)] = {
        "until": until_text,
        "reason": reason,
        "blocked_by": int(blocked_by) if blocked_by is not None else None,
        "created_at": now_utc().isoformat(),
    }
    save_data()
    return data["user_blocks"][str(user_id)]


def extend_user_block(user_id, hours, reason, blocked_by=None):
    """Ставит блокировку, только если она длиннее действующей."""
    existing = get_user_block(user_id)
    new_end = FOREVER if hours is None else now_utc() + timedelta(hours=hours)
    if existing and block_end(existing) >= new_end:
        return existing
    return apply_user_block(user_id, hours, reason, blocked_by)


# =====================================================================
# ЗАЯВКИ: ПОИСК И КЛАВИАТУРЫ
# =====================================================================
def pending_application_for_user(user_id):
    for key, app in data["applications"].items():
        if int(app.get("user_id", 0)) == int(user_id) and app.get("status") == "pending":
            return int(key), app
    return None, None


def find_application(message_id):
    """Заявка по id сообщения-карточки."""
    app_id = data["admin_message_map"].get(str(message_id))
    if app_id is not None:
        app = data["applications"].get(str(app_id))
        if app:
            return int(app_id), app
    for key, app in data["applications"].items():
        if app.get("admin_message_id") == message_id:
            return int(key), app
    return None, None


def find_contact_app(message_id):
    """Заявка по id сообщения диалога (сообщения пользователя / приглашение к диалогу)."""
    app_id = data["contact_message_map"].get(str(message_id))
    if app_id is None:
        return None, None
    app = data["applications"].get(str(app_id))
    return (int(app_id), app) if app else (None, None)


def find_complaint_by_message(message_id):
    for key, complaint in data["complaints"].items():
        if message_id in (complaint.get("admin_message_id"), complaint.get("copied_message_id")):
            return int(key), complaint
    return None, None


APP_STATUS_LABELS = {
    "pending": "⏳ На рассмотрении",
    "processing": "⏳ Обрабатывается",
    "accepted": "✅ Одобрена",
    "reset": "🔄 Сброшена владельцем",
    "rejected": "❌ Отклонена",
    "cancelled": "🚫 Отменена (карточка удалена)",
}


def application_caption(app):
    uid = app["user_id"]
    username = f"@{app['username']}" if app.get("username") else "не указан"
    text = (
        f"📨 <b>Заявка №{app['id']}</b>\n\n"
        f"🎮 Никнейм: <code>{esc(app['nickname'])}</code>\n"
        f"🦊 Пользователь: {profile_link(uid, app.get('user_name'), app.get('username'))}\n"
        f"🔗 Username: {esc(username)}\n"
        f"🆔 ID пользователя: <code>{uid}</code>"
    )
    status = app.get("status", "pending")
    if status != "pending":
        text += f"\n\n💬 Статус: {APP_STATUS_LABELS.get(status, esc(status))}"
        if app.get("processed_by"):
            text += f" — {saved_user_link(app['processed_by'])}"
        if status == "rejected" and app.get("rejection_block"):
            text += f"\n⛔ Блокировка заявок: {esc(app['rejection_block'])}"
        if app.get("joined_at"):
            text += "\n🎉 Участник в чате"
    return text



def application_keyboard(app):
    status = app.get("status", "pending")
    app_id = app["id"]
    rows = []

    if status == "pending":
        rows.append([
            InlineKeyboardButton("✅ Принять", callback_data=f"app:accept:{app_id}"),
            InlineKeyboardButton("❌ Отклонить", callback_data=f"app:reject:{app_id}"),
        ])

    elif status == "accepted" and not app.get("joined_at"):
        if app.get("invite_link") and not app.get("invite_revoked"):
            rows.append([
                InlineKeyboardButton(
                    "🚫 Отозвать ссылку",
                    callback_data=f"app:revoke:{app_id}"
                )
            ])
        rows.append([
            InlineKeyboardButton(
                "🔁 Выдать ссылку заново",
                callback_data=f"app:resend:{app_id}"
            )
        ])

    rows.append([
        InlineKeyboardButton(
            "💬 Написать пользователю",
            callback_data=f"app:contact:{app_id}"
        )
    ])

    return InlineKeyboardMarkup(rows)


async def refresh_application_card(context, app):
    message_id = app.get("admin_message_id")
    if not message_id:
        return
    try:
        await context.bot.edit_message_caption(
            chat_id=ADMIN_CHAT_ID,
            message_id=message_id,
            caption=application_caption(app),
            parse_mode=ParseMode.HTML,
            reply_markup=application_keyboard(app),
        )
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            logger.warning("Не удалось обновить карточку заявки: %s", exc)
    except TelegramError:
        logger.exception("Не удалось обновить карточку заявки")


def end_contact_for_app(app):
    app["contact_mode"] = False
    app["contact_started_by"] = None


def active_contact_app(user_id):
    """Активный диалог администрации с этим пользователем (с автозавершением по TTL)."""
    for key, app in data["applications"].items():
        if int(app.get("user_id", 0)) != int(user_id) or not app.get("contact_mode"):
            continue
        last = parse_dt(app.get("contact_at"))
        if last and now_utc() - last > CONTACT_TTL:
            end_contact_for_app(app)
            save_data()
            continue
        return int(key), app
    return None, None


# =====================================================================
# ЗАЯВКИ: ЛИЧНЫЕ СООБЩЕНИЯ С БОТОМ
# =====================================================================
def reset_application_flow(context):
    for key in ("awaiting_photo", "awaiting_nickname", "application_photo"):
        context.user_data.pop(key, None)


async def application_card_is_gone(context, app):
    """True, если карточка заявки удалена из админ-чата: заявка уже никто не рассмотрит."""
    message_id = app.get("admin_message_id")
    if not message_id:
        return False
    try:
        await context.bot.edit_message_reply_markup(
            chat_id=ADMIN_CHAT_ID, message_id=message_id, reply_markup=application_keyboard(app),
        )
    except BadRequest as exc:
        error = str(exc).lower()
        if "not modified" in error:
            return False
        return "not found" in error
    except TelegramError:
        return False  # сеть или права: не решаем за Администрацию
    return False


def cancel_lost_application(app_id, app):
    app["status"] = "cancelled"
    log_action(None, "application_cancelled", app["user_id"], app_id, "карточка удалена из админ-чата")


async def application_refusal(context, user_id):
    """Текст отказа, если человеку сейчас нельзя подавать заявку, иначе None."""
    block = get_user_block(user_id)
    if block:
        return (
            "❌ Подача заявок для тебя временно ограничена.\n"
            f"Причина: {block.get('reason', 'не указана')}\n"
            f"Блокировка действует до: {block_expiry_text(block)}."
        )
    app_id, app = pending_application_for_user(user_id)
    if app_id:
        if not await application_card_is_gone(context, app):
            return "⏳ У тебя уже есть заявка на рассмотрении. Дождись решения Администрации."
        cancel_lost_application(app_id, app)  # карточку удалили — заявка мертва, можно подать заново
    ban_text = f"❌ Подача заявок недоступна. Если это ошибка — напиши {CONTACT_HANDLE}."
    if (data["punishments"].get(str(user_id)) or {}).get("type") == "ban":
        return ban_text
    if str(user_id) in data.get("unverified", {}):
        return None  # уже в чате без заявки: подать заявку можно
    try:
        member = await context.bot.get_chat_member(MAIN_CHAT_ID, user_id)
    except TelegramError:
        return None  # не смогли проверить — не мешаем подать заявку
    if member.status in (ChatMemberStatus.MEMBER, ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER) or (
        member.status == ChatMemberStatus.RESTRICTED and getattr(member, "is_member", False)
    ):
        return "✅ Ты уже в чате, повторная заявка не нужна."
    if member.status == ChatMemberStatus.BANNED:
        return ban_text
    return None


def template_error(html_text, with_photo):
    """Текст ошибки, если шаблон не помещается в Telegram, иначе None."""
    plain = html_to_entities(html_text)[0]
    limit = 1024 if with_photo else 4096
    if len(plain) > limit:
        return f"❌ Текст слишком длинный: {len(plain)} из {limit} символов."
    return None


def current_template():
    return data.get("template_text") or DEFAULT_TEMPLATE, data.get("template_photo")


async def send_template_content(chat_id, context, text, photo):
    if photo:
        await context.bot.send_photo(chat_id=chat_id, photo=photo, caption=text, parse_mode=ParseMode.HTML)
    else:
        await context.bot.send_message(chat_id=chat_id, text=text, parse_mode=ParseMode.HTML, **NO_PREVIEW)


async def send_template(chat_id, context):
    text, photo = current_template()
    await send_template_content(chat_id, context, text, photo)


START_PAGE_SIZE = 10


def start_log_page(page):
    """Страница журнала нажатий /start (сначала новые)."""
    entries = list(reversed(data.get("start_log", [])))
    total_pages = max(1, -(-len(entries) // START_PAGE_SIZE))
    page = min(max(page, 0), total_pages - 1)
    lines = []
    for item in entries[page * START_PAGE_SIZE:(page + 1) * START_PAGE_SIZE]:
        dt = parse_dt(item.get("at"))
        at = fmt_dt(dt) if dt else ""
        link = build_profile_link(item["user_id"], item.get("name"), item.get("username"))
        username = f" · @{esc(item['username'])}" if item.get("username") else ""
        lines.append(f"• <code>{esc(at)}</code> — {link} · <code>{int(item['user_id'])}</code>{username}")
    text = (
        "🔔 <b>Нажатия /start</b>\n"
        f"<i>Страница {page + 1} из {total_pages} · записей: {len(entries)}</i>\n\n"
        + ("\n".join(lines) if lines else "Записей пока нет.")
    )
    return text, page, total_pages


def start_log_keyboard(page, total_pages):
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️ Новее", callback_data=f"st:{page - 1}"))
    nav.append(InlineKeyboardButton(f"{page + 1} / {total_pages}", callback_data=f"st:{page}"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton("Старше ▶️", callback_data=f"st:{page + 1}"))
    return InlineKeyboardMarkup([nav])


async def reset_application_command(update, context):
    """Только владелец: сбрасывает одобренную заявку, чтобы проверить вход без заявки."""
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id):
        return  # команда только для владельца, остальным не отвечаем
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Используй <code>/сбросзаявку</code> ответом на сообщение "
                                   "или <code>/сбросзаявку ID</code>.")
        return
    reset_keys = [key for key, app in data.get("applications", {}).items()
                  if str(app.get("user_id")) == str(target_id) and app.get("status") == "accepted"]
    if not reset_keys:
        await message.reply_text(
            f"ℹ️ <b>{saved_user_link(target_id)}</b> — одобренной заявки нет",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
        return
    for key in reset_keys:
        app = data["applications"][key]
        app["status"] = "reset"
        app["processed_by"] = user.id
        app["processed_at"] = now_utc().isoformat()
        log_action(user.id, "application_reset", target_id, int(key), "сброс владельцем")
        await refresh_application_card(context, app)
    await message.reply_text(
        f"✅ <b>{saved_user_link(target_id)}</b> — заявка сброшена\n"
        "<i>Теперь вход без заявки проверяется заново</i>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def start_log_command(update, context):
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id):
        return  # журнал нажатий только для владельца
    if not data.get("start_log"):
        await message.reply_text("🔔 Нажатий /start пока не было.")
        return
    text, page, total_pages = start_log_page(0)
    await message.reply_text(
        text, parse_mode=ParseMode.HTML, reply_markup=start_log_keyboard(page, total_pages), **NO_PREVIEW,
    )


async def start_log_callback(update, context):
    query = update.callback_query
    if not query:
        return
    if not is_owner(query.from_user.id):
        await query.answer("Нет доступа", show_alert=True)
        return
    await query.answer()
    try:
        page = int(query.data.split(":", 1)[1])
    except ValueError:
        return
    text, page, total_pages = start_log_page(page)
    try:
        await query.message.edit_text(
            text, parse_mode=ParseMode.HTML, reply_markup=start_log_keyboard(page, total_pages), **NO_PREVIEW,
        )
    except TelegramError:
        pass  # страница та же самая


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if not message or not user or not chat or chat.type != ChatType.PRIVATE:
        return
    dm_users = data.setdefault("dm_users", [])
    if int(user.id) not in dm_users:
        dm_users.append(int(user.id))
        save_data()
    if not is_owner(user.id):  # владелец узнает, кто нажал /start в личке бота
        log = data.setdefault("start_log", [])
        log.append({"at": now_utc().isoformat(), "user_id": user.id,
                    "name": user_name(user), "username": user.username})
        del log[:-500]
        save_data()
        try:
            await context.bot.send_message(
                OWNER_ID,
                "🔔 <b>Нажали /start</b>\n\n"
                f"🦊 {mention_user(user)}\n"
                f"🆔 <code>{user.id}</code>"
                + (f"\n🔗 @{esc(user.username)}" if user.username else ""),
                parse_mode=ParseMode.HTML, **NO_PREVIEW,
            )
        except TelegramError:
            logger.exception("Не удалось сообщить владельцу о /start")
    reset_application_flow(context)
    refusal = await application_refusal(context, user.id)
    if refusal:
        await message.reply_text(refusal)
        return
    context.user_data["awaiting_photo"] = True
    await send_template(chat.id, context)


async def private_photo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if not message or not user or not chat or chat.type != ChatType.PRIVATE:
        return

    if context.user_data.get("awaiting_photo"):
        refusal = await application_refusal(context, user.id)
        if refusal:
            reset_application_flow(context)
            await message.reply_text(refusal)
            return
        context.user_data.pop("awaiting_photo", None)
        context.user_data["application_photo"] = message.photo[-1].file_id
        context.user_data["awaiting_nickname"] = True
        await message.reply_text(
            "✅ Фотография получена!\n\n"
            "❗ Теперь отправь свой никнейм текстовым сообщением.\n\n"
            "<i>Пример: xSeezy</i>",
            parse_mode=ParseMode.HTML,
        )
        return

    if context.user_data.get("awaiting_nickname"):
        await message.reply_text("❗ Сейчас нужен никнейм текстом. Чтобы начать заново, отправь /start")
        return

    if await relay_user_message(update, context):
        return
    await message.reply_text("❗ Чтобы подать заявку на вступление в чат, отправь команду /start")


async def private_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if not message or not user or not chat or chat.type != ChatType.PRIVATE:
        return

    # Шаг заявки важнее диалога с администрацией — иначе никнейм улетит в пересылку.
    if context.user_data.get("awaiting_nickname"):
        await submit_application(update, context, (message.text or "").strip())
        return

    if await relay_user_message(update, context):
        return

    if context.user_data.get("awaiting_photo"):
        await message.reply_text("❗ Сначала отправь фотографию изображением.")
        return
    await message.reply_text("Чтобы подать заявку в чат DestroyCraft, отправь команду /start")


async def submit_application(update, context, nickname):
    message, user = update.effective_message, update.effective_user
    nickname = (nickname or "").strip()

    if not NICKNAME_RE.fullmatch(nickname):
        await message.reply_text(
            f"❗ Некорректный никнейм. {NICKNAME_HINT}\n\n"
            "Перепроверь и отправь еще раз!"
        )
        return

    photo_id = context.user_data.get("application_photo")
    if not photo_id:
        context.user_data.pop("awaiting_nickname", None)
        context.user_data["awaiting_photo"] = True
        await message.reply_text("❗ Сначала отправь фотографию.")
        return

    submitting = context.application.bot_data.setdefault("submitting", set())
    if user.id in submitting:  # двойная отправка пока предыдущая обрабатывается
        return
    submitting.add(user.id)
    try:
        refusal = await application_refusal(context, user.id)
        if refusal:
            reset_application_flow(context)
            await message.reply_text(refusal)
            return

        now = now_utc()
        previous = parse_dt(data["last_submission_at"].get(str(user.id)))
        if previous:
            seconds_left = APPLICATION_COOLDOWN - (now - previous).total_seconds()
            if seconds_left > 0:
                await message.reply_text(f"⏳ Подожди еще {int(seconds_left) + 1} сек. перед повторной подачей.")
                return

        remember_user(user, save=False)
        app_id = int(data["next_application_id"])
        data["next_application_id"] = app_id + 1
        app = {
            "id": app_id,
            "user_id": user.id,
            "user_name": user.full_name,
            "username": user.username,
            "nickname": nickname,
            "photo_id": photo_id,
            "status": "pending",
            "admin_message_id": None,
            "contact_mode": False,
            "created_at": now.isoformat(),
        }

        # Заявка попадает в базу только после успешной отправки карточки админам.
        try:
            sent = await context.bot.send_photo(
                chat_id=ADMIN_CHAT_ID,
                photo=photo_id,
                caption=application_caption(app),
                parse_mode=ParseMode.HTML,
                reply_markup=application_keyboard(app),
            )
        except TelegramError:
            logger.exception("Не удалось отправить карточку заявки в админ-чат")
            save_data()
            await message.reply_text("❌ Не удалось отправить заявку Администрации. Попробуй чуть позже.")
            return

        app["admin_message_id"] = sent.message_id
        data["applications"][str(app_id)] = app
        map_message("admin_message_map", sent.message_id, app_id)
        data["last_submission_at"][str(user.id)] = now.isoformat()
        save_data()
        reset_application_flow(context)
        await message.reply_text("✅ Твоя заявка отправлена на рассмотрение Администрации!")
    finally:
        submitting.discard(user.id)


async def relay_user_message(update, context):
    """Сообщение пользователя -> админ-чат, если с ним открыт диалог."""
    message, user = update.effective_message, update.effective_user
    if not message or not user:
        return False
    app_id, app = active_contact_app(user.id)
    if not app:
        return False

    header = (
        f"💬 <b>Сообщение по заявке №{app_id}</b>\n"
        f"🦊 {profile_link(user.id, user.full_name, user.username)}\n"
        f"🎮 Никнейм: <code>{esc(app['nickname'])}</code>\n"
        "<i>Ответь на это сообщение, чтобы написать пользователю.</i>"
    )
    try:
        header_msg = await context.bot.send_message(ADMIN_CHAT_ID, header, parse_mode=ParseMode.HTML, **NO_PREVIEW)
        copied = await context.bot.copy_message(
            chat_id=ADMIN_CHAT_ID, from_chat_id=user.id, message_id=message.message_id
        )
    except TelegramError:
        logger.exception("Не удалось передать сообщение пользователя")
        await message.reply_text("❌ Не удалось передать сообщение Администрации. Попробуй позже.")
        return True

    map_message("contact_message_map", header_msg.message_id, app_id)
    map_message("contact_message_map", copied.message_id, app_id)
    app["contact_at"] = now_utc().isoformat()
    save_data()
    await message.reply_text("✅ Сообщение передано Администрации.")
    return True


async def other_private_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, chat = update.effective_message, update.effective_chat
    if not message or not chat or chat.type != ChatType.PRIVATE:
        return
    if context.user_data.get("awaiting_nickname"):
        await message.reply_text("❗ Сейчас нужен никнейм обычным текстовым сообщением.")
        return
    if context.user_data.get("awaiting_photo"):
        await message.reply_text("❗ Пожалуйста, отправь фотографию изображением.")
        return
    if await relay_user_message(update, context):
        return
    await message.reply_text("❗ Чтобы подать заявку на вступление в чат, отправь команду /start")


async def admin_reply_relay(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Админ отвечает (reply) на сообщение диалога -> текст/медиа уходит пользователю.
    Остальные сообщения админ-чата пользователю НЕ пересылаются."""
    message, user = update.effective_message, update.effective_user
    if not message or not message.reply_to_message or not user or not has_access(user.id):
        return
    if message.text and message.text.startswith("/"):
        return
    app_id, app = find_contact_app(message.reply_to_message.message_id)
    if not app:
        return
    if not app.get("contact_mode"):
        await message.reply_text(
            "ℹ️ Диалог по этой заявке завершен. Нажми «💬 Написать пользователю» на карточке, чтобы начать заново."
        )
        return
    try:
        if message.text:
            await context.bot.send_message(app["user_id"], f"💬 Сообщение от Администрации:\n\n{message.text}")
        else:
            await context.bot.send_message(app["user_id"], "💬 Сообщение от Администрации:")
            await context.bot.copy_message(
                chat_id=app["user_id"], from_chat_id=ADMIN_CHAT_ID, message_id=message.message_id
            )
    except TelegramError:
        await message.reply_text("❌ Не удалось написать пользователю. Возможно, бот заблокирован пользователем.")
        return
    app["contact_at"] = now_utc().isoformat()
    save_data()
    await message.reply_text("✅ Сообщение отправлено.")


# =====================================================================
# ЗАЯВКИ: КНОПКИ АДМИНИСТРАЦИИ
# =====================================================================
async def create_invite(context, app_id):
    """Личная ссылка с запросом на вступление: бот сам одобрит только пользователя."""
    return await context.bot.create_chat_invite_link(
        chat_id=MAIN_CHAT_ID,
        name=f"application-{app_id}",
        expire_date=now_utc() + INVITE_TTL,
        creates_join_request=True,
    )


async def deliver_invite(context, app, link):
    hours = int(INVITE_TTL.total_seconds() // 3600)
    try:
        await context.bot.send_message(
            chat_id=app["user_id"],
            text=(
                "✅ <b>Заявка одобрена!</b>\n\n"
                "🔗 Твоя личная ссылка для вступления в чат:\n"
                f"{esc(link)}\n\n"
                f"⏳ Действует <b>{hours} ч</b>.\n"
                "👉 Нажми на ссылку и отправь запрос на вступление, бот одобрит запрос автоматически.\n\n"
                "🔔️ <b>Ссылка только для тебя.</b> Не передавай ее другим."
            ),
            parse_mode=ParseMode.HTML,
            **NO_PREVIEW,
        )
    except TelegramError:
        app["delivery_failed"] = True
        return False
    app["delivery_failed"] = False
    return True


REJECT_OPTIONS = {
    "reject24": (24, "24 часа"),
    "reject168": (168, "7 дней"),
    "rejectperm": (None, "навсегда"),
}


async def application_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query or not query.message:
        return
    if query.message.chat.id != ADMIN_CHAT_ID:
        await query.answer()
        return
    actor = query.from_user.id
    if not has_access(actor):
        await query.answer("❌ Нет доступа к управлению заявками.", show_alert=True)
        return

    try:
        _, action, app_id_text = query.data.split(":")
        app_id = int(app_id_text)
    except (ValueError, AttributeError):
        await query.answer()
        return

    app = data["applications"].get(str(app_id))
    if not app:
        await query.answer("❌ Заявка не найдена.", show_alert=True)
        return

    # --- выбор срока блокировки при отклонении ---
    if action == "reject":
        if app.get("status") != "pending":
            await query.answer("❗ Эта заявка уже обработана.", show_alert=True)
            return
        await query.answer()
        keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("⏱ 24 часа", callback_data=f"app:reject24:{app_id}"),
             InlineKeyboardButton("📅 7 дней", callback_data=f"app:reject168:{app_id}")],
            [InlineKeyboardButton("♾ Навсегда", callback_data=f"app:rejectperm:{app_id}"),
             InlineKeyboardButton("↩️ Отмена", callback_data=f"app:rejectcancel:{app_id}")],
        ])
        await query.message.reply_text(
            f"Выбери срок блокировки подачи заявок для пользователя по заявке №{app_id}:",
            reply_markup=keyboard,
        )
        return

    if action == "rejectcancel":
        await query.answer("Отменено.")
        try:
            await query.message.delete()
        except TelegramError:
            pass
        return

    # --- отзыв ссылки ---
    if action == "revoke":
        link = app.get("invite_link")
        if app.get("status") != "accepted" or not link or app.get("invite_revoked") or app.get("joined_at"):
            await query.answer("❌ Нет активной ссылки для отзыва.", show_alert=True)
            return
        await query.answer()
        app["invite_revoked"] = True  # ставим до await — защита от двойного клика
        try:
            await context.bot.revoke_chat_invite_link(chat_id=MAIN_CHAT_ID, invite_link=link)
        except TelegramError:
            app["invite_revoked"] = False
            logger.exception("Не удалось отозвать ссылку приглашения")
            await query.message.reply_text(
                "❌ Не удалось отозвать ссылку. Проверь права бота и не была ли ссылка уже отозвана."
            )
            return
        app["invite_revoked_at"] = now_utc().isoformat()
        app["invite_revoked_by"] = actor
        log_action(actor, "invite_revoked", app["user_id"], app_id)
        await refresh_application_card(context, app)
        await query.message.reply_text(f"🚫 Ссылка для заявки №{app_id} отозвана.")
        try:
            await context.bot.send_message(
                chat_id=app["user_id"],
                text=(
                    "ℹ️ Ранее выданная ссылка для вступления отозвана Администрацией. "
                    f"Если это ошибка, свяжись с: {CONTACT_HANDLE}"
                ),
            )
        except TelegramError:
            pass
        return

    # --- повторная выдача ссылки ---
    if action == "resend":
        if app.get("status") != "accepted" or app.get("joined_at"):
            await query.answer("❌ Ссылку можно выдать только одобренному пользователю, который еще не в чате.",
                               show_alert=True)
            return
        await query.answer()
        old_link = app.get("invite_link")
        if old_link and not app.get("invite_revoked"):
            try:
                await context.bot.revoke_chat_invite_link(chat_id=MAIN_CHAT_ID, invite_link=old_link)
            except TelegramError:
                pass
        try:
            invite = await create_invite(context, app_id)
        except TelegramError:
            logger.exception("Не удалось создать ссылку")
            await query.message.reply_text("❌ Не удалось создать ссылку. Проверь права бота в главной беседе.")
            return
        app["invite_link"] = invite.invite_link
        app["invite_revoked"] = False
        delivered = await deliver_invite(context, app, invite.invite_link)
        log_action(actor, "invite_resent", app["user_id"], app_id)
        await refresh_application_card(context, app)
        await query.message.reply_text(
            f"🔁 Новая ссылка выдана по заявке №{app_id}." if delivered
            else "🔔️ Ссылка создана, но бот не смог ее отправить. Возможно, бот заблокирован пользователем."
        )
        return

    # --- принять / отклонить ---
    if action == "accept" or action in REJECT_OPTIONS:
        if app.get("status") != "pending":
            await query.answer("❗ Эта заявка уже обработана.", show_alert=True)
            return
        await query.answer()
        app["status"] = "processing"  # занимаем заявку до первого await — защита от двойного клика

        if action == "accept":
            if str(app["user_id"]) in data.get("unverified", {}):
                # Уже в чате (вошел без заявки): ссылка не нужна, срок снимаем
                app.update(status="accepted", invite_link=None, invite_revoked=True,
                           processed_by=actor, processed_at=now_utc().isoformat())
                data["unverified"].pop(str(app["user_id"]), None)
                end_contact_for_app(app)
                delivered = await deliver_already_member(context, app)
                log_action(actor, "application_accepted_member", app["user_id"], app_id)
                result_text = "✅ Заявка одобрена. Участник уже в чате, ссылка не нужна."
            else:
                try:
                    invite = await create_invite(context, app_id)
                except Exception:
                    app["status"] = "pending"
                    logger.exception("Не удалось создать ссылку")
                    await query.message.reply_text("❌ Не удалось создать ссылку. Проверь права бота в главной беседе.")
                    return
                app.update(
                    invite_link=invite.invite_link,
                    invite_revoked=False,
                    status="accepted",
                    processed_by=actor,
                    processed_at=now_utc().isoformat(),
                )
                end_contact_for_app(app)
                delivered = await deliver_invite(context, app, invite.invite_link)
                log_action(
                    actor,
                    "application_accepted" if delivered else "application_accepted_delivery_failed",
                    app["user_id"], app_id,
                )
                result_text = (
                    "✅ Заявка одобрена." if delivered
                    else "🔔️ Заявка одобрена, но бот не смог отправить ссылку. Возможно, пользователь "
                         "бот заблокирован. Когда пользователь вернется — нажми «🔁 Выдать ссылку заново»."
                )

        else:
            hours, label = REJECT_OPTIONS[action]
            app.update(
                status="rejected",
                processed_by=actor,
                processed_at=now_utc().isoformat(),
                rejection_block=label,
            )
            end_contact_for_app(app)
            extend_user_block(app["user_id"], hours, f"Заявка №{app_id} отклонена", actor)
            log_action(actor, "application_rejected", app["user_id"], app_id, f"Блокировка: {label}")
            if str(app["user_id"]) in data.get("unverified", {}):
                await kick_unverified_member(
                    context, app["user_id"], "заявка отклонена",
                    public=int(app["user_id"]) in data.get("dm_users", []),
                )
            result_text = f"❌ Заявка отклонена. Блокировка: {label}."
            try:
                await context.bot.send_message(
                    chat_id=app["user_id"],
                    text=(
                        "❌ <b>Заявка отклонена</b>\n\n"
                        "К сожалению, Администрация не одобрила твою заявку.\n\n"
                        f"🚫 Повторная подача: <b>{esc(label)}</b>"
                    ),
                    parse_mode=ParseMode.HTML,
                )
            except TelegramError:
                pass

        save_data()
        await refresh_application_card(context, app)
        if query.message.message_id != app.get("admin_message_id"):
            try:  # убираем кнопки у сообщения с выбором срока
                await query.message.edit_reply_markup(reply_markup=None)
            except TelegramError:
                pass
        await query.message.reply_text(result_text)
        return

    # --- диалог с пользователем ---
    if action == "contact":
        await query.answer()
        try:
            await context.bot.send_message(
                chat_id=app["user_id"],
                text="💬 Администрация хочет связаться с тобой по поводу заявки. Напиши сюда свое сообщение.",
            )
        except TelegramError:
            await query.message.reply_text(
                "❌ Не удалось связаться с пользователем. Нужно открыть бота и нажать /start"
            )
            return
        app["contact_mode"] = True
        app["contact_started_by"] = actor
        app["contact_at"] = now_utc().isoformat()
        sent = await query.message.reply_text(
            f"💬 Диалог по заявке №{app_id} активирован.\n\n"
            "Чтобы написать пользователю, отвечай на ЭТО сообщение или на ЕГО сообщения. "
            "Все остальное в админ-чате останется внутри чата.\n"
            "❗ Завершить диалог: /конец"
        )
        map_message("contact_message_map", sent.message_id, app_id)
        log_action(actor, "contact_started", app["user_id"], app_id)


async def join_request_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Запрос на вступление по личной ссылке: одобряем только самого пользователя."""
    request = update.chat_join_request
    if not request or request.chat.id != MAIN_CHAT_ID or not request.invite_link:
        return
    link = request.invite_link.invite_link
    name = request.invite_link.name or ""

    app = next((a for a in data["applications"].values() if a.get("invite_link") == link), None)
    if app is None:
        match = re.fullmatch(r"application-(\d+)", name)
        if match:
            app = data["applications"].get(match.group(1))
    if app is None:
        # Запрос по чужой ссылке. Людей с одобренной заявкой (вернулись после выхода) пускаем тихо.
        # Остальных не трогаем: ждут ручного одобрения админом, после входа бот пишет в чат (on_member_change).
        if user_has_app_with_status(request.from_user.id, "accepted"):
            try:
                await request.approve()
            except TelegramError:
                logger.exception("Не удалось пропустить вернувшегося участника")
        return

    applicant = request.from_user
    if int(app["user_id"]) != applicant.id:
        try:
            await request.decline()
        except TelegramError:
            logger.exception("Не удалось отклонить чужой запрос")
        log_action(None, "join_declined", applicant.id, app["id"], "ссылка использована не пользователем")
        try:
            await context.bot.send_message(
                ADMIN_CHAT_ID,
                f"🔔️ По ссылке заявки №{app['id']} попытка вступить: {mention_user(applicant)}, "
                f"а заявка принадлежит {saved_user_link(app['user_id'])}. Запрос отклонен. "
                f"Ссылка отозвана, заявка отклонена, подача закрыта на 7 дней.",
                parse_mode=ParseMode.HTML, **NO_PREVIEW,
            )
        except TelegramError:
            pass
        # Ссылку передали другому человеку: отзываем ее, отклоняем заявку и закрываем подачу на 7 дней
        try:
            await context.bot.revoke_chat_invite_link(chat_id=MAIN_CHAT_ID, invite_link=link)
        except TelegramError:
            logger.exception("Не удалось отозвать ссылку после передачи другому человеку")
        app.update(
            status="rejected",
            invite_revoked=True,
            rejection_block="7 дней (ссылка передана другому)",
            processed_by=None,
            processed_at=now_utc().isoformat(),
        )
        end_contact_for_app(app)
        extend_user_block(app["user_id"], 168, f"Ссылка по заявке №{app['id']} передана другому человеку", None)
        save_data()
        await refresh_application_card(context, app)
        try:
            await context.bot.send_message(
                chat_id=app["user_id"],
                text=(
                    "⛔ <b>Заявка отклонена</b>\n\n"
                    "Твоя ссылка была передана другому человеку, поэтому заявка закрыта.\n\n"
                    "🚫 Повторная подача: <b>7 дней</b>"
                ),
                parse_mode=ParseMode.HTML,
            )
        except TelegramError:
            pass
        return

    if app.get("status") != "accepted" or app.get("invite_revoked"):
        try:
            await request.decline()
        except TelegramError:
            pass
        return

    try:
        await request.approve()
    except TelegramError:
        logger.exception("Не удалось одобрить запрос на вступление")
        return
    app["joined_at"] = now_utc().isoformat()
    try:  # ссылка больше не нужна
        await context.bot.revoke_chat_invite_link(chat_id=MAIN_CHAT_ID, invite_link=app["invite_link"])
        app["invite_revoked"] = True
    except TelegramError:
        pass
    log_action(None, "member_joined", applicant.id, app["id"])
    await refresh_application_card(context, app)
    try:
        # Без кнопки-ссылки на профиль: tg://user в кнопке Telegram отклоняет для закрытых профилей.
        # Имя в тексте уже ведет на профиль.
        await context.bot.send_message(
            ADMIN_CHAT_ID,
            f"🎉 {mention_user(applicant)} — вступление в чат по заявке №{app['id']}.",
            parse_mode=ParseMode.HTML,
            **NO_PREVIEW,
        )
    except TelegramError:
        logger.exception("Не удалось отправить уведомление о вступлении участника")
    try:
        await context.bot.send_message(request.user_chat_id, "Добро пожаловать в чат! 🖤")
    except TelegramError:
        pass


# =====================================================================
# ЦЕЛИ КОМАНД (reply / @username / ID)
# =====================================================================
def actor_id(update):
    message = update.effective_message
    if message and message.sender_chat:
        return message.sender_chat.id
    user = update.effective_user
    return user.id if user else None


def command_args(message):
    return (message.text or "").split()[1:]


def target_from_reply(message):
    """Пользователь по ответу: карточка заявки, сообщение диалога, карточка/копия жалобы
    или обычное сообщение участника (боты не считаются)."""
    replied = message.reply_to_message if message else None
    if not replied:
        return None
    _, app = find_application(replied.message_id)
    if app:
        return int(app["user_id"])
    _, app = find_contact_app(replied.message_id)
    if app:
        return int(app["user_id"])
    _, complaint = find_complaint_by_message(replied.message_id)
    if complaint:
        return int(complaint["target_id"])
    if replied.from_user and not replied.from_user.is_bot:
        return replied.from_user.id
    return None


def parse_user_token(token):
    if token.startswith("@"):
        return find_user_by_username(token)[0]
    if token.isdigit() and len(token) >= 6:  # короткие числа — это часы, а не ID
        return int(token)
    return None


def resolve_target(message, args):
    """(user_id | None, оставшиеся аргументы)."""
    target_id = target_from_reply(message)
    if target_id is not None:
        return target_id, args
    if args:
        target_id = parse_user_token(args[0])
        if target_id is not None:
            return target_id, args[1:]
    return None, args


async def reply_usage(message, text):
    await message.reply_text(f"📍 {text}", parse_mode=ParseMode.HTML)


# =====================================================================
# ДИАЛОГ С ЗАЯВИТЕЛЕМ, ШАБЛОН
# =====================================================================
async def end_contact(update, context):
    if not await require_staff(update, context, admin_chat_only=True):
        return
    message = update.effective_message
    actor = actor_id(update)
    apps = []
    if message.reply_to_message:
        replied_id = message.reply_to_message.message_id
        _, app = find_contact_app(replied_id)
        if not app:
            _, app = find_application(replied_id)
        if app and app.get("contact_mode"):
            apps = [app]
    if not apps:
        apps = [a for a in data["applications"].values()
                if a.get("contact_mode") and a.get("contact_started_by") == actor]
    if not apps:
        await message.reply_text("Нет активного диалога.")
        return
    for app in apps:
        end_contact_for_app(app)
        log_action(actor, "contact_ended", app.get("user_id"), app.get("id"))
        try:
            await context.bot.send_message(app["user_id"], "ℹ️ Диалог с Администрацией завершен.")
        except TelegramError:
            pass
    save_data()
    await message.reply_text("✅ Диалог завершен." if len(apps) == 1 else f"✅ Завершено диалогов: {len(apps)}.")


def template_menu_markup():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Изменить текст", callback_data="tpl:text"),
         InlineKeyboardButton("🖼 Изменить фото", callback_data="tpl:photo")],
        [InlineKeyboardButton("👀 Посмотреть", callback_data="tpl:show"),
         InlineKeyboardButton("🗑 Убрать фото", callback_data="tpl:remove")],
    ])


def template_preview_markup():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Сохранить", callback_data="tpl:save"),
         InlineKeyboardButton("❌ Отмена", callback_data="tpl:cancel")],
        [InlineKeyboardButton("✏️ Текст", callback_data="tpl:text"),
         InlineKeyboardButton("🖼 Фото", callback_data="tpl:photo")],
    ])


def template_cancel_markup():
    return InlineKeyboardMarkup([[InlineKeyboardButton("❌ Отмена", callback_data="tpl:cancel")]])


def clear_template_state(context):
    context.user_data.pop("tpl_draft", None)
    context.user_data.pop("tpl_step", None)


def get_draft(context):
    """Черновик шаблона: создается из текущего шаблона, пока не сохранен или не отменен."""
    if "tpl_draft" not in context.user_data:
        text, photo = current_template()
        context.user_data["tpl_draft"] = {"text": text, "photo": photo}
    return context.user_data["tpl_draft"]


async def send_menu(chat_id, context):
    _, photo = current_template()
    status = "есть" if photo else "нет"
    await context.bot.send_message(
        chat_id,
        "🛠 <b>Шаблон приветствия</b>\n\n"
        "Это сообщение получает каждый, кто подает заявку.\n\n"
        f"🖼 Фото: <b>{status}</b>",
        parse_mode=ParseMode.HTML,
        reply_markup=template_menu_markup(),
    )


async def send_draft_preview(chat_id, context):
    draft = context.user_data["tpl_draft"]
    await context.bot.send_message(chat_id, "👀 <b>Так будет выглядеть шаблон:</b>", parse_mode=ParseMode.HTML)
    await send_template_content(chat_id, context, draft["text"], draft["photo"])
    await context.bot.send_message(
        chat_id, "Сохранить изменения?", reply_markup=template_preview_markup())


async def template_command(update, context):
    if not await require_staff(update, context):
        return
    message, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not user or not is_owner(user.id):
        await message.reply_text("❌ Доступ запрещен.")
        return
    if chat.type != ChatType.PRIVATE:
        await message.reply_text("🔒 Шаблон меняется в личке с ботом: открой бота и отправь /шаблон.")
        return
    clear_template_state(context)
    await send_menu(chat.id, context)


async def template_callback(update, context):
    query = update.callback_query
    if not query:
        return
    if not is_owner(query.from_user.id):
        await query.answer("Нет доступа", show_alert=True)
        return
    await query.answer()
    action = query.data.split(":", 1)[1]
    chat_id = query.message.chat.id

    if action == "cancel":
        clear_template_state(context)
        await query.message.edit_text("❌ Изменения отменены.", reply_markup=None)
        return

    if action == "save":
        draft = context.user_data.get("tpl_draft")
        if not draft:
            await context.bot.send_message(chat_id, "Нечего сохранять. Открой /шаблон.")
            return
        data["template_text"] = draft["text"]
        data["template_photo"] = draft["photo"]
        save_data()
        clear_template_state(context)
        await query.message.edit_text("✅ <b>Шаблон сохранен.</b>", parse_mode=ParseMode.HTML, reply_markup=None)
        return

    if action == "show":
        text, photo = current_template()
        await send_template_content(chat_id, context, text, photo)
        await send_menu(chat_id, context)
        return

    if action == "remove":
        get_draft(context)["photo"] = None
        await send_draft_preview(chat_id, context)
        return

    if action == "text":
        get_draft(context)
        context.user_data["tpl_step"] = "text"
        await context.bot.send_message(
            chat_id,
            "✏️ <b>Пришли новый текст</b>\n\n"
            "Жирный и курсив сохранятся. Лимит: 4096 символов, а если есть фото, то 1024.",
            parse_mode=ParseMode.HTML,
            reply_markup=template_cancel_markup(),
        )
        return

    if action == "photo":
        get_draft(context)
        context.user_data["tpl_step"] = "photo"
        await context.bot.send_message(
            chat_id,
            "🖼 <b>Пришли фото</b>\n\nОно уйдет вместе с текстом шаблона.",
            parse_mode=ParseMode.HTML,
            reply_markup=template_cancel_markup(),
        )
        return


async def owner_private_text(update, context):
    """Текст владельца: либо ввод для шаблона, либо обычное сообщение заявки."""
    if context.user_data.get("shop_step"):
        return await shop_text_input(update, context)
    if context.user_data.get("tpl_step") != "text":
        return await private_text(update, context)
    message = update.effective_message
    draft = get_draft(context)
    html_text = (message.text_html or "").strip()
    if not html_text:
        await message.reply_text("Текст не может быть пустым. Пришли текст еще раз.")
        return
    error = template_error(html_text, with_photo=bool(draft["photo"]))
    if error:
        await message.reply_text(f"{error}\nСократи текст и пришли еще раз.")
        return
    draft["text"] = html_text
    context.user_data.pop("tpl_step", None)
    await send_draft_preview(message.chat.id, context)


async def owner_private_photo(update, context):
    """Фото владельца: фото товара (/шопс добавить), фото для шаблона или фото заявки."""
    caption = update.effective_message.caption or ""
    if re.match(r"(?i)^/шопс\s+добавить", caption):
        return await shop_photo_add(update.effective_message, caption)
    if re.match(r"(?i)^/приветствие\s+фото", caption):
        data["join_photo"] = update.effective_message.photo[-1].file_id
        save_data()
        await update.effective_message.reply_text("✅ Фото приветствия сохранено.")
        return
    mafia_photo_match = re.match(r"(?i)^/(набор|ночь|день|голосование|победа|казнь)\s+фото", caption)
    if mafia_photo_match:
        key = MAFIA_PHOTO_KEYS[mafia_photo_match.group(1).lower()]
        data.setdefault("mafia_photos", {})[key] = update.effective_message.photo[-1].file_id
        save_data()
        await update.effective_message.reply_text(f"✅ Картинка для фазы «{mafia_photo_match.group(1)}» сохранена.")
        return
    if re.match(r"(?i)^/промо\s+фото", caption):
        return await promo_command(update, context)
    if re.match(r"(?i)^/промо\s+coins\s+\d+", caption):
        return await promo_command(update, context)
    if re.match(r"(?i)^/сундучки\s+фото", caption):
        data["chest_photo"] = update.effective_message.photo[-1].file_id
        save_data()
        await update.effective_message.reply_text("✅ Картинка для сундучков сохранена.")
        return
    if context.user_data.get("shop_step"):
        return await shop_photo_input(update, context)
    if context.user_data.get("tpl_step") != "photo":
        return await private_photo(update, context)
    message = update.effective_message
    draft = get_draft(context)
    error = template_error(draft["text"], with_photo=True)
    if error:
        await message.reply_text(f"{error}\nСначала сократи текст, потом добавь фото.")
        return
    draft["photo"] = message.photo[-1].file_id
    context.user_data.pop("tpl_step", None)
    await send_draft_preview(message.chat.id, context)


# =====================================================================
# БЛОКИРОВКИ ЗАЯВОК, СПИСКИ, ЖУРНАЛ
# =====================================================================
def parse_hours(text):
    """('навсегда' | 1..8760) -> (ok, hours|None)."""
    text = text.strip().lower()
    if text in ("навсегда", "вечная", "бессрочно"):
        return True, None
    try:
        hours = int(text)
    except ValueError:
        return False, None
    return (1 <= hours <= 8760), hours


async def block_applications_command(update, context):
    if not await require_staff(update, context, admin_chat_only=True):
        return
    message = update.effective_message
    target_id, args = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(
            message,
            "Ответь командой /банзаявки на сообщение пользователя, карточку заявки или диалога "
            "(либо укажи @username или ID).\n"
            "Срок в часах: <code>/банзаявки 48</code>, бессрочно: <code>/банзаявки навсегда</code>",
        )
        return
    if target_id == OWNER_ID or target_id == context.bot.id:
        await message.reply_text("❌ Этого пользователя заблокировать нельзя.")
        return
    ok, hours = parse_hours(args[0]) if args else (True, 24)
    if not ok:
        await message.reply_text("❌ Укажи срок от 1 до 8760 часов или слово «навсегда».")
        return
    actor = actor_id(update)
    block = apply_user_block(target_id, hours=hours, reason="Блокировка Администрацией", blocked_by=actor)
    log_action(actor, "applications_blocked", target_id, details=block_expiry_text(block))
    await message.reply_text(
        f"🔒 <b>{saved_user_link(target_id)}</b> — подача заявок закрыта\n"
        f"<i>Срок: {esc(block_expiry_text(block))}</i>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def unblock_applications_command(update, context):
    if not await require_staff(update, context, admin_chat_only=True):
        return
    message = update.effective_message
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Ответь командой /разбанзаявки на сообщение пользователя, "
                                   "карточку заявки (либо укажи @username или ID).")
        return
    data["user_blocks"].pop(str(target_id), None)
    data["blocked_users"] = [int(x) for x in data.get("blocked_users", []) if int(x) != target_id]
    log_action(actor_id(update), "applications_unblocked", target_id)
    await message.reply_text(
        f"🔓 <b>{saved_user_link(target_id)}</b> — подача заявок открыта",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def list_application_bans(update, context):
    if not await require_staff(update, context, admin_chat_only=True):
        return
    all_ids = {str(int(x)) for x in data.get("blocked_users", [])}
    all_ids.update(data.get("user_blocks", {}).keys())
    active = []
    for user_id_text in sorted(all_ids, key=int):
        block = get_user_block(int(user_id_text))
        if block:
            active.append(
                f"• {saved_user_link(user_id_text)} (<code>{user_id_text}</code>) — "
                f"{esc(block_expiry_text(block))}; {esc(block.get('reason', 'причина не указана'))}"
            )
    if not active:
        await update.effective_message.reply_text("ℹ Сейчас нет заблокированных пользователей.")
        return
    await update.effective_message.reply_text(
        "🔒 <b>Заблокированные пользователи:</b>\n\n" + "\n".join(active),
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def list_pending_applications(update, context):
    if not await require_staff(update, context, admin_chat_only=True):
        return
    pending = sorted(
        (a for a in data["applications"].values() if a.get("status") == "pending"),
        key=lambda a: a.get("created_at", ""),
    )
    if not pending:
        await update.effective_message.reply_text("ℹ️ Заявок на рассмотрении нет.")
        return
    lines = []
    for app in pending[:30]:
        created = parse_dt(app.get("created_at"))
        link = message_link(ADMIN_CHAT_ID, app["admin_message_id"]) if app.get("admin_message_id") else None
        card = f' — <a href="{link}">карточка</a>' if link else ""
        lines.append(
            f"• №{app['id']} — <b>{esc(app['nickname'])}</b> "
            f"({saved_user_link(app['user_id'], app.get('user_name'), app.get('username'))}), "
            f"{esc(fmt_dt(created) if created else '?')}{card}"
        )
    extra = f"\n\n…и еще {len(pending) - 30}" if len(pending) > 30 else ""
    await update.effective_message.reply_text(
        f"📨 <b>Заявки на рассмотрении ({len(pending)}):</b>\n\n" + "\n".join(lines) + extra,
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


LOG_PAGE_SIZE = 10


def log_page(page):
    """Текст страницы журнала (сначала новые записи) и ее номер."""
    entries = list(reversed(data.get("admin_log", [])))
    total_pages = max(1, -(-len(entries) // LOG_PAGE_SIZE))
    page = min(max(page, 0), total_pages - 1)
    lines = []
    for item in entries[page * LOG_PAGE_SIZE:(page + 1) * LOG_PAGE_SIZE]:
        dt = parse_dt(item.get("at"))
        at = fmt_dt(dt) if dt else str(item.get("at", ""))
        action = ACTION_LABELS.get(item.get("action"), item.get("action", "действие"))
        parts = [f"<code>{esc(at)}</code> — <b>{esc(action)}</b>"]
        if item.get("actor_id"):
            parts.append(f"админ {saved_user_link(item['actor_id'])}")
        if item.get("target_id"):
            parts.append(f"участник {saved_user_link(item['target_id'])}")
        if item.get("app_id"):
            parts.append(f"заявка №{item['app_id']}")
        if item.get("details"):
            parts.append(esc(item["details"]))
        lines.append("• " + "; ".join(parts))
    text = (
        "📘 <b>Журнал действий</b>\n"
        f"<i>Страница {page + 1} из {total_pages} · записей: {len(entries)}</i>\n\n"
        + ("\n".join(lines) if lines else "Записей пока нет.")
    )
    return text, page, total_pages


def log_keyboard(page, total_pages, owner):
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️ Новее", callback_data=f"log:{page - 1}"))
    nav.append(InlineKeyboardButton(f"{page + 1} / {total_pages}", callback_data=f"log:{page}"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton("Старше ▶️", callback_data=f"log:{page + 1}"))
    rows = [nav]
    if owner:
        rows.append([InlineKeyboardButton("🗑 Очистить журнал", callback_data="log:clear")])
    return InlineKeyboardMarkup(rows)


async def show_admin_log(update, context):
    if not await require_staff(update, context, admin_chat_only=True):
        return
    if not data.get("admin_log"):
        await update.effective_message.reply_text("📘 Журнал пока пуст.")
        return
    text, page, total_pages = log_page(0)
    await update.effective_message.reply_text(
        text, parse_mode=ParseMode.HTML, reply_markup=log_keyboard(page, total_pages, is_owner(update.effective_user.id)),
        **NO_PREVIEW,
    )


async def log_callback(update, context):
    query = update.callback_query
    if not query:
        return
    user = query.from_user
    in_admin = query.message.chat.id == ADMIN_CHAT_ID
    in_owner_dm = query.message.chat.type == ChatType.PRIVATE and is_owner(user.id)
    if not has_access(user.id) or not (in_admin or in_owner_dm):
        await query.answer("Нет доступа", show_alert=True)
        return
    owner = is_owner(user.id)
    action = query.data.split(":", 1)[1]

    if action in ("clear", "clearyes") and not owner:
        await query.answer("Очищать журнал может только владелец.", show_alert=True)
        return

    if action == "clear":
        await query.answer()
        await query.message.edit_text(
            "🗑 <b>Очистить журнал?</b>\n\n"
            "Все записи пропадут. В журнале останется одна запись о самой очистке.",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ Да, очистить", callback_data="log:clearyes"),
                InlineKeyboardButton("❌ Нет", callback_data="log:0"),
            ]]),
        )
        return

    if action == "clearyes":
        data["admin_log"] = []
        log_action(user.id, "log_cleared")
        await query.answer("Журнал очищен")
        page = 0
    else:
        try:
            page = int(action)
        except ValueError:
            await query.answer()
            return
        await query.answer()

    text, page, total_pages = log_page(page)
    try:
        await query.message.edit_text(
            text, parse_mode=ParseMode.HTML, reply_markup=log_keyboard(page, total_pages, owner), **NO_PREVIEW,
        )
    except TelegramError:
        pass  # страница та же самая: Telegram не меняет сообщение


# =====================================================================
# ЖАЛОБЫ
# =====================================================================
def reports_are_blocked(user_id):
    return str(user_id) in {str(x) for x in data.get("blocked_reports", [])}


def complaint_keyboard(complaint_id):
    complaint = data["complaints"].get(str(complaint_id))
    if not complaint:
        return InlineKeyboardMarkup([])
    keyboard = []
    state = complaint.get("action")
    if state == "warning":
        keyboard.append([InlineKeyboardButton("🔄 Снять предупреждение", callback_data=f"remove_warning:{complaint_id}")])
    elif state == "mute":
        keyboard.append([InlineKeyboardButton("🔔 Снять мут", callback_data=f"unmute:{complaint_id}")])
    elif state == "ban":
        keyboard.append([InlineKeyboardButton("🔓 Снять блокировку", callback_data=f"unban:{complaint_id}")])
    else:
        keyboard.append([InlineKeyboardButton("🔔️ Выдать предупреждение", callback_data=f"warn:{complaint_id}")])
        keyboard.append([InlineKeyboardButton("🔕 Выдать мут", callback_data=f"mute:{complaint_id}")])
        keyboard.append([InlineKeyboardButton("⛔ Заблокировать", callback_data=f"ban:{complaint_id}")])


    profile_buttons = []

    for label, id_key, un_key in (
        ("👮 Профиль отправителя", "reporter_id", "reporter_username"),
    ):
        user_id = complaint.get(id_key)
        saved = data["users"].get(str(user_id)) or {}
        username = saved.get("username") or complaint.get(un_key)

        if username:
            username = str(username).lstrip("@")
            profile_buttons.append(
                InlineKeyboardButton(
                    label,
                    url=f"https://t.me/{username}",
                )
            )

    if profile_buttons:
        keyboard.append(profile_buttons)
    if complaint.get("message_link"):
        keyboard.append([InlineKeyboardButton("🔗 Открыть сообщение", url=complaint["message_link"])])
    return InlineKeyboardMarkup(keyboard)


def mute_keyboard(complaint_id):
    keyboard = [
        [InlineKeyboardButton(title, callback_data=f"mutetime:{key}:{complaint_id}")]
        for key, (title, _) in MUTE_DURATIONS.items()
    ]
    keyboard.append([InlineKeyboardButton("◀️ Назад", callback_data=f"back:{complaint_id}")])
    return InlineKeyboardMarkup(keyboard)


def complaint_text(complaint_id):
    complaint = data["complaints"].get(str(complaint_id))
    if not complaint:
        return "❌ Жалоба не найдена."
    offender = plain_user_with_id(complaint["target_id"], complaint.get("target_name"))
    reporter = saved_user_link_with_id(complaint["reporter_id"], complaint.get("reporter_name"), complaint.get("reporter_username"))
    state = complaint.get("action")
    title = "НОВАЯ ЖАЛОБА" if state is None and not complaint.get("handled_by") else "ЖАЛОБА"
    text = f"🔔 <b>{title} №{complaint_id}</b>\n\n🦊 Нарушитель: {offender}\n👮 Отправитель: {reporter}\n"
    if complaint.get("reason"):
        text += f"📝 Причина: {esc(complaint['reason'])}\n"
    if complaint.get("kind") in KIND_LABELS:
        text += f"📎 Вложение: {KIND_LABELS[complaint['kind']]}\n"
    if complaint.get("quote"):
        text += f"\n💬 <b>Сообщение:</b>\n<blockquote>{esc(complaint['quote'])}</blockquote>\n"

    if state == "warning":
        text += f"\n💬 Статус: 🔔️ Предупреждение {complaint.get('warning_count', 0)}/3"
        if complaint.get("auto_mute"):
            text += "\n🔕 Автоматический мут: 1 день\n🔄 Предупреждения аннулированы"
    elif state == "mute":
        text += f"\n💬 Статус: 🔕 Мут на {esc(complaint.get('mute_duration_name', 'неизвестный срок'))}"
    elif state == "ban":
        text += "\n💬 Статус: ⛔️ Пользователь заблокирован"
    elif state == "unmute":
        text += "\n💬 Статус: 🔔 Мут снят"
    elif state == "unban":
        text += "\n💬 Статус: 🔓 Блокировка снята"
    else:
        text += "\n💬 Статус: <b>На рассмотрении</b>"
    if complaint.get("handled_by"):
        text += f"\n⛔ Обработано: {saved_user_link(complaint['handled_by'])}"
    return text


async def edit_card(message, text, **kwargs):
    """Карточка жалобы бывает обычным сообщением или медиа с подписью."""
    if getattr(message, "text", None) is None and getattr(message, "caption", None) is not None:
        try:
            await message.edit_caption(caption=text, **kwargs)
        except BadRequest as exc:
            if "not modified" not in str(exc).lower():
                raise
    else:
        await safe_edit(message, text, **kwargs)


async def show_complaint(message, complaint_id, extra="", keyboard=None):
    is_caption = getattr(message, "text", None) is None and getattr(message, "caption", None) is not None
    await edit_card(
        message,
        complaint_text(complaint_id) + extra,
        parse_mode=ParseMode.HTML,
        reply_markup=keyboard or complaint_keyboard(complaint_id),
        **({} if is_caption else NO_PREVIEW),
    )


# Типы вложений: у этих copy_message умеет менять подпись, значит карточка = подпись к самому вложению.
CAPTION_KINDS = ("photo", "video", "animation", "document", "audio", "voice")
KIND_LABELS = {
    "photo": "фото", "video": "видео", "animation": "GIF", "document": "файл", "audio": "аудио",
    "voice": "голосовое", "sticker": "стикер", "video_note": "кружок",
}


def message_kind(msg):
    for kind in ("photo", "video", "animation", "voice", "audio", "document", "sticker", "video_note"):
        if getattr(msg, kind, None):
            return kind
    return "text" if getattr(msg, "text", None) else "other"


async def handle_complaint(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, reporter, chat = update.effective_message, update.effective_user, update.effective_chat
    if not message or not reporter or not chat or chat.id != MAIN_CHAT_ID:
        return
    text = message.text or message.caption or ""
    if not text.lower().startswith("#жалоба"):
        return
    remember_user(reporter)

    if reports_are_blocked(reporter.id):
        await message.reply_text(
            f"🚫 {mention_user(reporter)}, тебе запрещено подавать жалобы!", parse_mode=ParseMode.HTML
        )
        return

    target_message = message.reply_to_message
    if target_message is not None and getattr(target_message, "forum_topic_created", None):
        target_message = None  # в топиках «ответ» на корневое сообщение темы — не жалоба
    if target_message is None:
        await message.reply_text("🔔️ Чтобы подать жалобу, ответь на сообщение пользователя и напиши #жалоба")
        return
    if target_message.sender_chat:
        await message.reply_text("❌ Нельзя подать жалобу на сообщение от имени чата или канала.")
        return
    target = target_message.from_user
    if not target:
        await message.reply_text("❌ Не удалось определить пользователя.")
        return
    remember_user(target)

    if target.id == context.bot.id:
        await message.reply_text("🔔️ На бота нельзя подать жалобу.")
        return
    if target.id == reporter.id:
        await message.reply_text("🔔️ Нельзя подать жалобу на самого себя.")
        return
    if await is_main_chat_admin(context, target.id):
        await message.reply_text("🔔️ На Администрацию нельзя подать жалобу.")
        return

    for key, existing in data["complaints"].items():
        if existing.get("original_message_id") == target_message.message_id:
            await message.reply_text("ℹ️ На это сообщение уже поступила жалоба.")
            return

    times = context.application.bot_data.setdefault("complaint_times", {})
    wait = COMPLAINT_COOLDOWN - (time.time() - times.get(reporter.id, 0))
    if wait > 0:
        await message.reply_text(f"⏳ Подожди еще {int(wait) + 1} сек. перед следующей жалобой.")
        return
    times[reporter.id] = time.time()

    kind = message_kind(target_message)
    reason = text[len("#жалоба"):].strip()[:200]
    quote = (target_message.text or target_message.caption or "").strip()
    quote = quote[:200 if kind in CAPTION_KINDS else 700]
    data["complaint_number"] += 1
    complaint_id = data["complaint_number"]
    data["complaints"][str(complaint_id)] = {
        "target_id": target.id,
        "target_name": user_name(target),
        "target_username": target.username,
        "reporter_id": reporter.id,
        "reporter_name": user_name(reporter),
        "reporter_username": reporter.username,
        "original_message_id": target_message.message_id,
        "message_link": message_link(MAIN_CHAT_ID, target_message.message_id),
        "reason": reason,
        "kind": kind,
        "quote": quote,
        "action": None,
        "warning_count": 0,
        "auto_mute": False,
        "mute_duration_name": None,
        "admin_message_id": None,
        "copied_message_id": None,
        "handled_by": None,
    }
    complaint = data["complaints"][str(complaint_id)]
    card_text = complaint_text(complaint_id)
    keyboard = complaint_keyboard(complaint_id)

    # Одно сообщение на жалобу: вложение с карточкой в подписи, либо текст с цитатой.
    sent_id = None
    if kind in CAPTION_KINDS and len(card_text) <= 1024:
        try:
            copied = await context.bot.copy_message(
                chat_id=ADMIN_CHAT_ID, from_chat_id=MAIN_CHAT_ID, message_id=target_message.message_id,
                caption=card_text, parse_mode=ParseMode.HTML, reply_markup=keyboard,
            )
            sent_id = copied.message_id
        except TelegramError as exc:
            logger.error("Не удалось отправить вложение с карточкой: %s", exc)
    if sent_id is None:
        # Копирование исходного вложения — необязательное действие: оно может быть
        # запрещено настройками чата или недоступно для отдельных типов сообщений.
        # Даже если копия не удалась, все равно пытаемся отправить карточку жалобы.
        if kind not in ("text", *CAPTION_KINDS):
            try:
                copied = await context.bot.copy_message(
                    chat_id=ADMIN_CHAT_ID,
                    from_chat_id=MAIN_CHAT_ID,
                    message_id=target_message.message_id,
                )
                complaint["copied_message_id"] = copied.message_id
            except TelegramError:
                logger.exception(
                    "Не удалось скопировать сообщение-доказательство для жалобы №%s; отправляю карточку без копии",
                    complaint_id,
                )
        try:
            sent = await context.bot.send_message(
                chat_id=ADMIN_CHAT_ID,
                text=card_text,
                parse_mode=ParseMode.HTML,
                reply_markup=keyboard,
                **NO_PREVIEW,
            )
            sent_id = sent.message_id
        except TelegramError:
            logger.exception("Ошибка отправки карточки жалобы №%s в админ-чат", complaint_id)
            data["complaints"].pop(str(complaint_id), None)
            save_data()
            await message.reply_text("❌ Не удалось передать жалобу Администрации. Попробуй позже.")
            return

    if message.effective_attachment is not None and message_kind(message) != "text":
        try:  # доказательство, приложенное самим автором жалобы
            await context.bot.copy_message(ADMIN_CHAT_ID, MAIN_CHAT_ID, message.message_id)
        except TelegramError as exc:
            logger.error("Не удалось скопировать доказательство: %s", exc)

    complaint["admin_message_id"] = sent_id
    save_data()
    await message.reply_text(
        "🔔 Жалоба отправлена на рассмотрение Администрации!",
        parse_mode=ParseMode.HTML,
    )


# =====================================================================
# МОДЕРАЦИЯ: ПРЕДУПРЕЖДЕНИЯ, МУТЫ, БАНЫ
# =====================================================================
async def restrict_member(context, user_id, until_date):
    try:
        await context.bot.restrict_chat_member(
            chat_id=MAIN_CHAT_ID,
            user_id=int(user_id),
            permissions=ChatPermissions(can_send_messages=False),
            until_date=until_date,
        )
        return True
    except TelegramError as exc:
        logger.error("Ошибка выдачи мута: %s", exc)
        return False


async def default_permissions(context):
    """Права по умолчанию в чате — к ним возвращаем участника после мута."""
    try:
        chat = await context.bot.get_chat(MAIN_CHAT_ID)
        if chat.permissions:
            return chat.permissions
    except TelegramError:
        logger.exception("Не удалось получить права чата по умолчанию")
    return ChatPermissions(
        can_send_messages=True, can_send_audios=True, can_send_documents=True, can_send_photos=True,
        can_send_videos=True, can_send_video_notes=True, can_send_voice_notes=True, can_send_polls=True,
        can_send_other_messages=True, can_add_web_page_previews=True, can_invite_users=True,
    )


async def announce(context, text):
    try:
        await context.bot.send_message(MAIN_CHAT_ID, text, parse_mode=ParseMode.HTML, **NO_PREVIEW)
    except TelegramError:
        logger.exception("Не удалось отправить объявление в основной чат")


async def give_warning(user_id, context):
    """-> {'count': N, 'auto_mute': bool, 'mute_error': bool}"""
    user_id = int(user_id)
    key = str(user_id)
    remember_user_from_saved_id(user_id)
    count = int(data["warnings"].get(key, 0)) + 1
    link = saved_user_link(user_id)
    warn_until = now_utc() + WARNING_TTL

    if count >= 3:
        until = now_utc() + timedelta(days=1)
        if await restrict_member(context, user_id, until):
            data["warnings"][key] = 0
            data["warning_expires"].pop(key, None)
            data["punishments"][key] = {"type": "mute", "duration": "1 день", "until": until.isoformat()}
            save_data()
            await announce(
                context,
                f"🔔️ <b>{link}</b> — предупреждение (3/3)\n"
                f"<i>Мут на 1 день, истекает {fmt_dt(until)}</i>",
            )
            return {"count": 3, "auto_mute": True, "mute_error": False}
        data["warnings"][key] = 3  # мут не выдан — не обнуляем, админ решит вручную
        data["warning_expires"][key] = warn_until.isoformat()
        save_data()
        await announce(context, f"🔔️ <b>{link}</b> — предупреждение (3/3)\n<i>Истекает {fmt_dt(warn_until)}</i>")
        return {"count": 3, "auto_mute": False, "mute_error": True}

    data["warnings"][key] = count
    data["warning_expires"][key] = warn_until.isoformat()
    save_data()
    await announce(context, f"🔔️ <b>{link}</b> — предупреждение ({count}/3)\n<i>Истекает {fmt_dt(warn_until)}</i>")
    return {"count": count, "auto_mute": False, "mute_error": False}


async def give_mute(user_id, duration_key, context):
    if duration_key not in MUTE_DURATIONS:
        return False
    title, delta = MUTE_DURATIONS[duration_key]
    until = now_utc() + delta
    if not await restrict_member(context, user_id, until):
        return False
    data["punishments"][str(user_id)] = {"type": "mute", "duration": title, "until": until.isoformat()}
    save_data()
    await announce(
        context,
        f"🔕 <b>{saved_user_link(user_id)}</b> — мут на {esc(title)}\n<i>Истекает {fmt_dt(until)}</i>",
    )
    return True


async def remove_mute(user_id, context):
    try:
        await context.bot.restrict_chat_member(
            chat_id=MAIN_CHAT_ID, user_id=int(user_id), permissions=await default_permissions(context)
        )
    except TelegramError as exc:
        logger.error("Ошибка снятия мута: %s", exc)
        return False
    data["punishments"].pop(str(user_id), None)
    save_data()
    await announce(context, f"🔔 <b>{saved_user_link(user_id)}</b> — мут снят")
    return True


async def give_ban(user_id, context):
    try:
        await context.bot.ban_chat_member(chat_id=MAIN_CHAT_ID, user_id=int(user_id))
    except TelegramError as exc:
        logger.error("Ошибка блокировки: %s", exc)
        return False
    data["punishments"][str(user_id)] = {"type": "ban", "at": now_utc().isoformat()}
    save_data()
    await announce(context, f"⛔️ <b>{saved_user_link(user_id)}</b> — блокировка\n<i>Срок: бессрочно</i>")
    return True


async def remove_ban(user_id, context):
    try:
        await context.bot.unban_chat_member(chat_id=MAIN_CHAT_ID, user_id=int(user_id), only_if_banned=True)
    except TelegramError as exc:
        logger.error("Ошибка снятия блокировки: %s", exc)
        return False
    data["punishments"].pop(str(user_id), None)
    save_data()
    await announce(context, f"🔓 <b>{saved_user_link(user_id)}</b> — блокировка снята")
    return True


async def moderation_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query or not query.message:
        return
    if query.message.chat_id != ADMIN_CHAT_ID:
        await query.answer()
        return
    actor = query.from_user.id
    if not has_access(actor):
        await query.answer("❌ Нет доступа.", show_alert=True)
        return

    parts = (query.data or "").split(":")
    action = parts[0]
    try:
        duration_key, complaint_id = (parts[1], parts[2]) if action == "mutetime" else (None, parts[1])
    except IndexError:
        await query.answer()
        return
    complaint = data["complaints"].get(str(complaint_id))
    if not complaint:
        await query.answer("❌ Жалоба не найдена.", show_alert=True)
        return

    # Защита от «устаревших» кнопок: состояние карточки уже могло измениться.
    state = complaint.get("action")
    required = {"remove_warning": "warning", "unmute": "mute", "unban": "ban"}
    stale = (action in ("warn", "mute", "mutetime", "ban") and state in ("warning", "mute", "ban")) or (
        action in required and state != required[action]
    )
    if stale:
        await query.answer("🔔️ Состояние жалобы уже изменилось.", show_alert=True)
        await show_complaint(query.message, complaint_id)
        return

    busy = context.application.bot_data.setdefault("busy", set())
    lock = f"complaint:{complaint_id}"
    if lock in busy:
        await query.answer("⏳ Действие уже выполняется.")
        return
    busy.add(lock)
    try:
        await query.answer()
        await run_moderation_action(query, context, action, complaint_id, complaint, duration_key, actor)
    finally:
        busy.discard(lock)


async def run_moderation_action(query, context, action, complaint_id, complaint, duration_key, actor):
    target_id = int(complaint["target_id"])
    key = str(target_id)
    message = query.message

    if action == "back":
        await show_complaint(message, complaint_id)
        return

    if action == "mute":
        await show_complaint(message, complaint_id, "\n\n🔕 <b>Выбери длительность мута:</b>", mute_keyboard(complaint_id))
        return

    if action == "warn":
        result = await give_warning(target_id, context)
        complaint.update(action="warning", warning_count=result["count"], auto_mute=result["auto_mute"],
                         handled_by=actor)
        log_action(actor, "warning_given", target_id, details=f"жалоба №{complaint_id}, {result['count']}/3")
        await show_complaint(message, complaint_id)
        if result["mute_error"]:
            await message.reply_text("🔔️ Это 3-е предупреждение, но автомут выдать не удалось "
                                     "(проверь права бота). Выдай мут вручную.")
        return

    if action == "remove_warning":
        if complaint.get("auto_mute"):
            if not await remove_mute(target_id, context):
                await message.reply_text("❌ Не удалось снять автоматический мут.")
                return
            data["warnings"][key] = 2  # снимаем именно 3-е предупреждение
            data["warning_expires"][key] = (now_utc() + WARNING_TTL).isoformat()
        else:
            left = max(0, int(data["warnings"].get(key, 0)) - 1)
            data["warnings"][key] = left
            if left == 0:
                data["warning_expires"].pop(key, None)
        complaint.update(action=None, warning_count=0, auto_mute=False, handled_by=actor)
        log_action(actor, "warning_removed", target_id, details=f"жалоба №{complaint_id}")
        await announce(
            context,
            f"🔄 <b>{saved_user_link(target_id)}</b> — предупреждение снято\n"
            f"<i>Предупреждений: {data['warnings'][key]}/3</i>",
        )
        await show_complaint(message, complaint_id)
        return

    if action == "mutetime":
        if (data["punishments"].get(key) or {}).get("type") == "ban":
            await message.reply_text("ℹ️ Участник уже заблокирован.")
            return
        if not await give_mute(target_id, duration_key, context):
            await message.reply_text("❌ Не удалось выдать мут. Проверь права бота (и что участник не администратор).")
            return
        name = MUTE_DURATIONS[duration_key][0]
        complaint.update(action="mute", mute_duration_name=name, handled_by=actor)
        log_action(actor, "mute_given", target_id, details=f"жалоба №{complaint_id}, {name}")
        await show_complaint(message, complaint_id)
        return

    if action == "unmute":
        if not await remove_mute(target_id, context):
            await message.reply_text("❌ Не удалось снять мут.")
            return
        complaint.update(action="unmute", handled_by=actor)
        log_action(actor, "mute_removed", target_id, details=f"жалоба №{complaint_id}")
        await show_complaint(message, complaint_id)
        return

    if action == "ban":
        if not await give_ban(target_id, context):
            await message.reply_text("❌ Не удалось заблокировать участника.")
            return
        complaint.update(action="ban", handled_by=actor)
        log_action(actor, "ban_given", target_id, details=f"жалоба №{complaint_id}")
        await show_complaint(message, complaint_id)
        return

    if action == "unban":
        if not await remove_ban(target_id, context):
            await message.reply_text("❌ Не удалось снять блокировку.")
            return
        complaint.update(action="unban", handled_by=actor)
        log_action(actor, "ban_removed", target_id, details=f"жалоба №{complaint_id}")
        await show_complaint(message, complaint_id)


# =====================================================================
# КОМАНДЫ МОДЕРАЦИИ
# =====================================================================
def queue_expiry(user_id, kind, **details):
    data.setdefault("expiry_queue", []).append({"user_id": int(user_id), "kind": kind, **details})


def cleanup_expired():
    """Убирает истекшие муты, сгоревшие предупреждения и закончившиеся блокировки заявок.
    Истекшее ставит в очередь, чтобы админы получили уведомление."""
    now = now_utc()
    changed = False
    for key, punishment in list(data["punishments"].items()):
        if punishment.get("type") == "mute":
            until = parse_dt(punishment.get("until"))
            if until and until <= now:
                data["punishments"].pop(key, None)
                queue_expiry(key, "mute", duration=punishment.get("duration"))
                changed = True
    for key, expires in list(data["warning_expires"].items()):
        expire_dt = parse_dt(expires)
        if expire_dt and expire_dt <= now:
            count = int(data["warnings"].get(key, 0))
            if count > 0:
                queue_expiry(key, "warnings", count=count)
            data["warnings"][key] = 0
            data["warning_expires"].pop(key, None)
            changed = True
    for key in list(data["user_blocks"]):
        get_user_block(int(key))  # сам удаляет истекшие
    if changed:
        save_data()
    return changed


async def send_expiry_notices(context):
    """Отправляет админам уведомления об истекших мутах и предупреждениях."""
    queue = data.get("expiry_queue") or []
    if not queue:
        return
    data["expiry_queue"] = []
    save_data()
    for item in queue:
        link = saved_user_link_with_id(item["user_id"])
        if item["kind"] == "mute":
            text = f"🔔 <b>Мут истек</b>\n\n🦊 {link}\n⏱ Срок: {esc(item.get('duration') or 'неизвестно')}"
        else:
            text = f"🔔 <b>Предупреждения сгорели</b>\n\n🦊 {link}\n📊 Было: {int(item.get('count', 0))}/3"
        try:
            await context.bot.send_message(ADMIN_CHAT_ID, text, parse_mode=ParseMode.HTML, **NO_PREVIEW)
        except TelegramError:
            logger.exception("Не удалось отправить уведомление об истечении")


async def stale_applications_job(context: ContextTypes.DEFAULT_TYPE):
    """Раз в час: закрывает заявки, карточка которых удалена, и заявки, висящие дольше срока."""
    now = now_utc()
    for key, app in list(data["applications"].items()):
        if app.get("status") != "pending":
            continue
        created = parse_dt(app.get("created_at"))
        if created and now - created > APPLICATION_MAX_AGE:
            app["status"] = "cancelled"
            log_action(None, "application_expired", app["user_id"], int(key), "срок рассмотрения истек")
            await refresh_application_card(context, app)
            try:
                await context.bot.send_message(
                    int(app["user_id"]),
                    f"⌛ Срок рассмотрения заявки №{key} истек. Можешь подать новую.",
                )
            except TelegramError:
                pass  # пользователь мог заблокировать бота
            continue
        if await application_card_is_gone(context, app):
            cancel_lost_application(int(key), app)


BACKGROUND_TICK_SECONDS = 60
_background_task = None


UNVERIFIED_TTL = timedelta(hours=24)            # срок на подачу заявки после входа


def user_has_app_with_status(user_id, status):
    return any(str(a.get("user_id")) == str(user_id) and a.get("status") == status
               for a in data.get("applications", {}).values())


def bot_link(bot):
    username = getattr(bot, "username", None)
    return f"@{username}" if username else "@bot"


async def read_member_tag(context, user_id, member):
    """Возвращает (поддерживается_ли_тег, тег). Без поддержки библиотеки никого не наказываем."""
    if hasattr(member, "tag"):
        return True, member.tag
    try:
        full = await context.bot.get_chat_member(MAIN_CHAT_ID, user_id)
    except TelegramError:
        return False, None
    if hasattr(full, "tag"):
        return True, full.tag
    return False, None


JOIN_BATCH = {"items": [], "task": None}
JOIN_BATCH_DELAY = 90  # сек.: кто вошел за это время, попадает в одно приветствие


async def join_batch_add(context, link, dl):
    JOIN_BATCH["items"].append((link, dl))
    task = JOIN_BATCH["task"]
    if task is None or task.done():
        JOIN_BATCH["task"] = asyncio.create_task(join_batch_flush(context))


async def join_batch_flush(context):
    await asyncio.sleep(JOIN_BATCH_DELAY)
    items = list(JOIN_BATCH["items"])
    JOIN_BATCH["items"].clear()
    JOIN_BATCH["task"] = None
    if not items:
        return
    names = ", ".join(link for link, _dl in items)
    text = (f"👋🏼 <b>Добро пожаловать, {names}</b>\n\n"
            "❗️ <b>Чтобы остаться в чате, подай заявку в боте</b>\n"
            "— Нажми кнопку «📝 Подать заявку» ниже\n"
            "— Следуй инструкциям в боте\n\n"
            "⏳ Имей в виду, если заявка не будет оставлена в течение суток, то бот автоматически исключит из чата!")
    username = getattr(context.bot, "username", None)
    markup = None
    if username:
        markup = InlineKeyboardMarkup([[InlineKeyboardButton(
            "📝 Подать заявку", url=f"https://t.me/{username}?start=apply")]])
    photo = data.get("join_photo")
    if photo:
        try:
            sent = await context.bot.send_photo(MAIN_CHAT_ID, photo, caption=text, parse_mode=ParseMode.HTML,
                                                reply_markup=markup)
            schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, 24 * 3600)
            return
        except TelegramError:
            logger.exception("Не удалось отправить фото приветствия")
    try:
        sent = await context.bot.send_message(MAIN_CHAT_ID, text, parse_mode=ParseMode.HTML,
                                              reply_markup=markup, **NO_PREVIEW)
        schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, 24 * 3600)
    except TelegramError:
        logger.exception("Не удалось отправить приветствие")


async def on_member_change(update, context):
    """Вход в основной чат без одобренной заявки: ставим срок на подачу заявки."""
    change = update.chat_member
    if not change:
        return
    logger.info("chat_member: чат %s, пользователь %s, %s -> %s", change.chat.id,
                change.new_chat_member.user.id, change.old_chat_member.status, change.new_chat_member.status)
    if change.chat.id != MAIN_CHAT_ID:
        return
    old, new = change.old_chat_member.status, change.new_chat_member.status
    user = change.new_chat_member.user
    if new == "restricted" and old != "restricted" and not getattr(user, "is_bot", False):
        await mafia_handle_chat_mute(context, user.id)
    if getattr(user, "is_bot", False) or has_access(user.id):
        return
    key = str(user.id)
    if new in ("left", "kicked"):
        if data.get("unverified", {}).pop(key, None) is not None:
            save_data()
        return
    # Участник с мутом остается статусом "restricted", вход виден по флагу is_member
    was_out = old in ("left", "kicked") or (
        old == "restricted" and not getattr(change.old_chat_member, "is_member", True))
    now_in = new == "member" or (new == "restricted" and getattr(change.new_chat_member, "is_member", True))
    if not (was_out and now_in):
        return
    if user_has_app_with_status(user.id, "accepted"):
        logger.info("Вход пользователя %s: есть одобренная заявка, срок не ставится", user.id)
        return

    known, tag = await read_member_tag(context, user.id, change.new_chat_member)
    if not known:
        logger.warning("Библиотека не поддерживает теги участников: вход %s не проверен", user.id)
        return
    if tag:
        logger.info("Вход пользователя %s с тегом «%s»: срок не ставится", user.id, tag)
        return

    now = now_utc()
    deadline = now + UNVERIFIED_TTL
    data.setdefault("unverified", {})[key] = {
        "name": user_name(user), "username": user.username,
        "joined_at": now.isoformat(), "deadline": deadline.isoformat(),
        "reminded": False,
    }
    save_data()
    logger.info("Вход пользователя %s без заявки: срок до %s, отправляю предупреждение", user.id, deadline.isoformat())
    link = build_profile_link(user.id, user_name(user), user.username)
    dl = fmt_dt(deadline)
    await join_batch_add(context, link, dl)
    try:
        await context.bot.send_message(
            chat_id=user.id,
            text=(
                "👋 <b>Привет!</b>\n\n"
                "Вход в чат по ссылке без заявки.\n"
                "Чтобы остаться, подай заявку здесь.\n\n"
                "Напиши /start, и я покажу, что делать дальше.\n\n"
                f"⏳ <b>Срок:</b> до {dl}"
            ),
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass  # человек не нажимал /start, личка недоступна
    try:
        await context.bot.send_message(
            ADMIN_CHAT_ID,
            f"🔔 Вход в чат без заявки: <b>{link}</b>\n<i>Предупреждение отправлено, срок до {dl}</i>",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass


async def deliver_already_member(context, app):
    try:
        await context.bot.send_message(
            chat_id=app["user_id"],
            text="✅ <b>Заявка одобрена!</b>\n\nТы уже в чате, ничего делать не нужно.",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        return False
    return True


async def kick_unverified_member(context, user_id, reason, public=False):
    """Исключает участника без заявки и сразу снимает блокировку, чтобы он мог подать заявку позже."""
    uid = int(user_id)
    item = data.get("unverified", {}).get(str(uid)) or {}
    link = build_profile_link(uid, item.get("name"), item.get("username"))
    try:
        await context.bot.ban_chat_member(chat_id=MAIN_CHAT_ID, user_id=uid)
        await context.bot.unban_chat_member(chat_id=MAIN_CHAT_ID, user_id=uid, only_if_banned=True)
    except TelegramError:
        logger.exception("Не удалось исключить участника без заявки")
        return False
    data.get("unverified", {}).pop(str(uid), None)
    log_action(None, "unverified_kicked", uid, details=reason)
    if public:
        await announce(
            context,
            f"🚪 <b>{link}</b> пока не в чате: {reason}.\n\n"
            f"Вернуться можно в любой момент, подав заявку: <b>{bot_link(context.bot)}</b>",
        )
    return True


async def unverified_tick(context):
    """Напоминания, предупреждение и исключение тех, кто вошел без заявки."""
    now = now_utc()
    for key, item in list(data.get("unverified", {}).items()):
        uid = int(key)
        if user_has_app_with_status(uid, "accepted"):
            data["unverified"].pop(key, None)
            save_data()
            continue
        if user_has_app_with_status(uid, "pending"):
            continue  # заявка на рассмотрении: решение за админами
        deadline = parse_dt(item.get("deadline"))
        if not deadline:
            continue
        link = build_profile_link(uid, item.get("name"), item.get("username"))
        dl = fmt_dt(deadline)


        if now >= deadline:
            try:
                await context.bot.ban_chat_member(chat_id=MAIN_CHAT_ID, user_id=uid)
                await context.bot.unban_chat_member(chat_id=MAIN_CHAT_ID, user_id=uid, only_if_banned=True)
            except TelegramError:
                logger.exception("Не удалось исключить участника без заявки")
                continue  # повторим в следующий раз
            data["unverified"].pop(key, None)
            log_action(None, "unverified_kicked", uid, details="заявка не подана в срок")



async def background_loop(bot):
    """Фоновый цикл вместо JobQueue: раз в минуту чистит наказания и шлет уведомления,
    раз в час проверяет заявки. Ошибка внутри не останавливает цикл."""
    context = SimpleNamespace(bot=bot)
    ticks = 0
    while True:
        try:
            cleanup_expired()
            await send_expiry_notices(context)
            await unverified_tick(context)
            await quiz_tick(context)
            await chest_tick(context)
            await dice_week_tick(context)
            await econ_week_tick(context)
            await leaf_tick(context)
            if _MSG_DIRTY["v"]:  # счетчик сообщений сохраняем раз в минуту
                _MSG_DIRTY["v"] = False
                save_data()
            if ticks % 60 == 0:
                await stale_applications_job(context)
        except asyncio.CancelledError:
            raise
        except Exception:
            logger.exception("Ошибка в фоновом цикле")
        ticks += 1
        await asyncio.sleep(BACKGROUND_TICK_SECONDS)


SHOP_SEED_TITLES = [
    ("🪙 Осенний странник", 150, "Титул для тех, кто приходит в чат каждую осень"),
    ("✅ Золотой лист", 300, "Редкий титул: золотой, как листва в октябре"),
    ("🏁 Тыквенный король", 500, "Титул для самых смелых охотников за тыквами"),
    ("☁️ Дождевой охотник", 250, "Титул для тех, кто не боится осенних дождей"),
    ("🦉 Ночная сова", 200, "Титул для тех, кто играет допоздна"),
    ("🐿 Запасливая белка", 180, "Титул для тех, кто копит коины на зиму"),
    ("🦊 Лисица-охотница", 220, "Титул для хитрых и быстрых игроков"),
    ("❌ Лесной грибник", 160, "Титул для тех, кто собирает все, что можно"),
    ("🌬 Ветер перемен", 280, "Титул для тех, кто меняет ход игры"),
    ("🧙 Осенний маг", 450, "Титул для самых опытных игроков чата"),
    ("🪄 Заклинатель листьев", 350, "Титул для тех, кто ловит листопад первым"),
    ("🕰 Хранитель вечера", 260, "Титул для тех, кто задерживается в чате"),
    ("⚡ Хлебороб", 190, "Титул для тех, кто собирает урожай"),
    ("🎩 Джентльмен осени", 320, "Титул для стильных участников чата"),
    ("👑 Король каштанов", 400, "Редкий титул для лучших игроков сезона"),
    ("🔮 Провидец", 380, "Титул для тех, кто угадывает все ответы"),
    ("🎯 Меткий стрелок", 240, "Титул для тех, кто попадает в цель"),
    ("🛡 Страж очага", 300, "Титул для тех, кто оберегает чат"),
    ("⚡ Молния осени", 270, "Титул для самых быстрых участников"),
    ("🌙 Лунный путник", 210, "Титул для тех, кто гуляет по ночам"),
]
SHOP_SEED_ITEMS = [
    ("🛍 Шарф дружбы", 100, "Теплый шарф, чтобы не мерзнуть в осенний вечер"),
    ("⏳ Чай с медом", 50, "Горячий чай, пока за окном дождь"),
    ("🍎 Яблочный пирог", 80, "Ароматный пирог с корицей"),
    ("🕯 Свеча уюта", 120, "Свеча, которая делает вечер теплее"),
    ("⛔ Мешок каштанов", 60, "Свежие каштаны прямо из парка"),
    ("🏁 Тыква-фонарь", 150, "Светильник, который сияет в темноте"),
    ("🍯 Банка меда", 90, "Настоящий осенний мед с ароматом луга"),
    ("🛡 Вязаные варежки", 110, "Варежки, которые согреют в любой мороз"),
    ("🍇 Корзина винограда", 75, "Сладкий виноград на осенний вечер"),
    ("🥧 Тыквенный пирог", 95, "Пирог с пряностями и корицей"),
    ("🧺 Корзина грибов", 130, "Свежие грибы из осеннего леса"),
    ("📖 Книга у камина", 140, "Уютная книга для долгих вечеров"),
    ("🪵 Охапка дров", 85, "Дрова, чтобы разжечь камин"),
    ("🍷 Бокал глинтвейна", 105, "Горячий глинтвейн с пряностями"),
    ("☕ Кофе с корицей", 65, "Ароматный кофе, чтобы бодрить вечером"),
    ("🧦 Теплые носки", 70, "Носки, которые спасут от холодных ног"),
    ("🪁 Воздушный змей", 115, "Змей для ветреного осеннего дня"),
    ("🌻 Букет подсолнухов", 125, "Яркий букет, чтобы осень казалась теплее"),
    ("🎁 Коробка сюрпризов", 200, "Что внутри, узнаете после покупки"),
    ("🪅 Гирлянда из листьев", 160, "Декор, который украсит ваш профиль"),
]


SHOP_SEED_EXTRA = [
    ("title", "🌌 Тот, кто видит звезды", 330, "Титул для тех, кто ночью смотрит в небо и ждет падающую звезду"),
    ("title", "🐺 Вожак стаи", 410, "Титул для тех, кто ведет за собой весь чат"),
    ("title", "🦅 Хозяин высот", 360, "Титул для тех, кто всегда на первом месте в топе"),
    ("title", "🧭 Вечный путешественник", 230, "Титул для тех, кто исследует каждый угол бота"),
    ("title", "🏹 Лучник листопада", 290, "Титул для тех, кто бьет без промаха в кубике"),
    ("title", "🕸 Паук-счетовод", 310, "Титул для тех, кто считает каждый коин"),
    ("title", "🪶 Перо жар-птицы", 470, "Редкий титул, который переливается в профиле"),
    ("title", "🔥 Костровой", 240, "Титул для тех, кто греет чат своими сообщениями"),
    ("title", "🧊 Ледяной расчет", 340, "Титул для тех, кто играет хладнокровно"),
    ("title", "🎭 Мастер интриги", 420, "Титул для тех, кто выигрывает в мафии хитростью"),
    ("title", "🕵 Тень в тумане", 330, "Титул для тех, кто появляется незаметно"),
    ("title", "🛶 Капитан тихой заводи", 250, "Титул для тех, кто знает все тихие места чата"),
    ("title", "🧶 Мастер узоров", 200, "Титул для тех, кто создает красоту в каждом уголке"),
    ("title", "🌠 Ловец метеоритов", 480, "Редкий титул для самых удачливых игроков"),
    ("title", "🦔 Колючий характер", 170, "Титул для тех, кто не любит лишних слов"),
    ("item", "🍪 Печенье с предсказанием", 55, "Внутри записка с предсказанием на вечер"),
    ("item", "🪄 Волшебная палочка сезона", 260, "Палочка с листом клена, которая будет напоминать о победе"),
    ("item", "🧸 Плюшевый лис", 135, "Мягкий лис, который ждет вас в профиле"),
    ("item", "🚂 Билет на осенний поезд", 145, "Билет в путешествие по красивым лесам"),
    ("item", "🦋 Коллекция бабочек", 175, "Бабочки, которые собраны в одну яркую коллекцию"),
    ("item", "🌿 Травяной сбор", 70, "Сбор трав для бодрости и хорошего настроения"),
    ("item", "🥐 Круассан с шоколадом", 45, "Свежий круассан, пока он еще теплый"),
    ("item", "🎻 Скрипка в дождь", 300, "Инструмент, который играет осенние мелодии"),
    ("item", "🗺 Карта потерянного леса", 190, "Карта, которая ведет к скрытым тайникам"),
    ("item", "🔭 Телескоп звездочета", 330, "Телескоп для ночных наблюдений за звездами"),
    ("item", "🧪 Зелье бодрости", 85, "Бодрящее зелье, которое пахнет лесом"),
    ("item", "🪔 Фонарь путника", 115, "Фонарь, который освещает дорогу в темноте"),
    ("item", "🐞 Божья коровка на удачу", 55, "Маленький талисман удачи для вашего профиля"),
    ("item", "🎲 Счастливая кость", 240, "Кубик, который любит смелых игроков"),
    ("item", "🦉 Совиный ключ", 210, "Ключ, который открывает потаенные двери чата"),
    ("item", "🪙 Охапка осенних листьев", 40, "Яркий букет, который шуршит под ногами"),
    ("item", "🌙 Лунный камень", 280, "Камень, который светится в лунную ночь"),
]


def seed_shop_extra():
    """Один раз добавляет дополнительные товары, если таких названий еще нет в магазине."""
    if data.get("shop_seed_extra"):
        return
    existing = {i["name"] for i in shop_state()["items"]}
    for kind, name, price, desc in SHOP_SEED_EXTRA:
        if name not in existing:
            shop_add_item(name, price, desc, kind="title" if kind == "title" else "item")
    data["shop_seed_extra"] = True
    save_data()


def seed_shop_once():
    """Один раз при первом запуске добавляет в магазин стартовый набор товаров и титулов."""
    if data.get("shop_seeded"):
        return
    if shop_state()["items"]:
        data["shop_seeded"] = True
        save_data()
        return
    for name, price, desc in SHOP_SEED_TITLES:
        shop_add_item(name, price, desc, kind="title")
    for name, price, desc in SHOP_SEED_ITEMS:
        shop_add_item(name, price, desc)
    data["shop_seeded"] = True
    save_data()


PUBLIC_COMMANDS = [
    ("mystat", "Свой профиль: статус, титул, покупки"),
    ("stat", "Профиль участника: ответом или @ником"),
    ("balance", "Свой баланс DS коинов"),
    ("rich", "Топ богачей по DS коинам"),
    ("shop", "Магазин товаров и титулов"),
    ("dice", "Кубик со ставками: 6 дает x4, 5 дает x1"),
    ("diceweek", "Топ по кубику за неделю"),
    ("duel", "Дуэль на кубиках: /duel @ник ставка"),
    ("give", "Передать коины: /give @ник сумма"),
    ("lottery", "Лотерея: твои билеты и шанс"),
    ("bank", "Банк недели и банк лотереи"),
    ("mafia", "Начать игру в мафию"),
    ("mafiatop", "Топ побед в мафии"),
    ("guide", "Гайд: что умеет бот"),
    ("likegive", "Ответом на сообщение: выдать от 5 до 10 лайков (раз в сутки)"),
    ("toplikes", "Топ профилей по лайкам"),
    ("help", "То же, что /guide"),
]


BOT_DESCRIPTION = (
    "🤖 Бот чата DestroyCraft\n\n"
    "⚡️ Сервер: tg.ds-craft.net\n"
    "🎮 Сайт: ds-craft.ru\n\n"
    "🎯 Что умеет бот:\n"
    "▫️ заявки в чат и модерация\n"
    "▫️ DS коины: кубик, дуэль, лотерея, мафия, викторина\n"
    "▫️ магазин товаров и титулов\n"
    "▫️ листопад, банк недели и топ игроков\n\n"
    "📝 Чтобы подать заявку, напиши /start\n"
    "📩 Вопросы по боту: @escpls\n"
)
BOT_SHORT_DESCRIPTION = (
    "🤖 Уникальный бот для чата DestroyCraft\n\n"
    "⚡️ IP: tg.ds-craft.net\n"
    "🎮 Сайт: ds-craft.ru\n\n"
    "📝 По вопросам: @escpls"
)
# Запасной вариант, если Telegram считает длину в UTF-16 и не принимает полный текст
BOT_SHORT_DESCRIPTION_COMPACT = BOT_SHORT_DESCRIPTION.replace("\n\n📝", "\n📝")
# Запасной вариант, если Telegram считает длину в UTF-16 и не принимает полный текст
BOT_SHORT_DESCRIPTION_COMPACT = BOT_SHORT_DESCRIPTION.replace("\n\n📝", "\n📝")


async def set_bot_descriptions(bot):
    """Описание бота в профиле и короткое описание в поиске."""
    try:
        await bot.set_my_description(BOT_DESCRIPTION)
    except TelegramError:
        logger.exception("Не удалось обновить описание бота")
    try:
        await bot.set_my_short_description(BOT_SHORT_DESCRIPTION)
    except TelegramError:
        try:
            await bot.set_my_short_description(BOT_SHORT_DESCRIPTION_COMPACT)
        except TelegramError:
            logger.exception("Не удалось обновить короткое описание бота")


async def set_public_commands(bot):
    """Публичное меню команд в Telegram: видно в чате, при нажатии на «/»."""
    try:
        commands = [BotCommand(name, description) for name, description in PUBLIC_COMMANDS]
        # В группах меню команд нужно, в личке с ботом — нет
        await bot.set_my_commands(commands, scope=BotCommandScopeAllGroupChats())
        await bot.set_my_commands([], scope=BotCommandScopeAllPrivateChats())
    except TelegramError:
        logger.exception("Не удалось обновить меню команд")


async def _on_startup(application):
    global _background_task
    seed_shop_once()
    seed_shop_extra()
    asyncio.create_task(set_public_commands(application.bot))
    asyncio.create_task(notify_interrupted_mafia(application.bot))
    asyncio.create_task(set_bot_descriptions(application.bot))
    _background_task = asyncio.create_task(background_loop(application.bot))


async def _on_shutdown(application):
    if _background_task is not None:
        _background_task.cancel()


async def warnings_command(update, context):
    if not await require_staff(update, context):
        return
    cleanup_expired()
    lines = []
    for uid, count in data["warnings"].items():
        if int(count) <= 0:
            continue
        expires = parse_dt(data["warning_expires"].get(uid))
        tail = f", истекают {fmt_dt(expires)}" if expires else ""
        lines.append(f"🦊 {saved_user_link_with_id(uid)} — {int(count)}/3{tail}")
    if not lines:
        await update.effective_message.reply_text("ℹ️ Активных предупреждений нет.")
        return
    await update.effective_message.reply_text(
        "🔔️ <b>Предупреждения участников:</b>\n\n" + "\n".join(lines), parse_mode=ParseMode.HTML, **NO_PREVIEW
    )


async def remove_warnings_command(update, context):
    if not await require_staff(update, context):
        return
    message = update.effective_message
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Используй <code>/сп</code> ответом на сообщение пользователя "
                                   "(или карточку жалобы), либо <code>/сп @username</code>.")
        return
    data["warnings"][str(target_id)] = 0
    data["warning_expires"].pop(str(target_id), None)
    log_action(actor_id(update), "warnings_cleared", target_id)
    await message.reply_text(
        f"✅ <b>{saved_user_link(target_id)}</b> — предупреждения сняты",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def block_reports_command(update, context):
    if not await require_staff(update, context):
        return
    message = update.effective_message
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Используй <code>/зж</code> ответом на сообщение пользователя "
                                   "либо <code>/зж @username</code>.")
        return
    if target_id == context.bot.id:
        await message.reply_text("❗️ Нельзя установить запрет для бота.")
        return
    link = saved_user_link(target_id)
    if str(target_id) in {str(x) for x in data["blocked_reports"]}:
        await message.reply_text(
            f"ℹ️ <b>{link}</b> — запрет на жалобы уже стоит",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
        return
    data["blocked_reports"].append(target_id)
    log_action(actor_id(update), "reports_blocked", target_id)
    await message.reply_text(
        f"🚫 <b>{link}</b> — запрет на жалобы\n<i>Срок: бессрочно</i>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def unblock_reports_command(update, context):
    if not await require_staff(update, context):
        return
    message = update.effective_message
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Используй <code>/рж</code> ответом на сообщение или <code>/рж @username</code>.")
        return
    link = saved_user_link(target_id)
    if str(target_id) not in {str(x) for x in data["blocked_reports"]}:
        await message.reply_text(
            f"ℹ️ <b>{link}</b> — запрета на жалобы не было",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
        return
    data["blocked_reports"] = [x for x in data["blocked_reports"] if str(x) != str(target_id)]
    log_action(actor_id(update), "reports_unblocked", target_id)
    await message.reply_text(
        f"✅ <b>{link}</b> — запрет на жалобы снят",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def blocked_reports_list_command(update, context):
    if not await require_staff(update, context):
        return
    blocked = data.get("blocked_reports", [])
    if not blocked:
        await update.effective_message.reply_text("ℹ️ Пользователей с запретом на жалобы нет.")
        return
    await update.effective_message.reply_text(
        "ℹ️ <b>Участники, которым запрещено подавать жалобы:</b>\n\n"
        + "\n".join(f"🦊 {saved_user_link_with_id(uid)}" for uid in blocked),
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def punishments_command(update, context):
    if not await require_staff(update, context):
        return
    cleanup_expired()
    lines = []
    for uid, punishment in data["punishments"].items():
        if punishment.get("type") == "mute":
            until = parse_dt(punishment.get("until"))
            tail = f", до {fmt_dt(until)}" if until else ""
            lines.append(f"🔕 {saved_user_link_with_id(uid)} — мут ({esc(punishment.get('duration', 'неизвестно'))}{esc(tail)})")
        elif punishment.get("type") == "ban":
            lines.append(f"🔨 {saved_user_link_with_id(uid)} — блокировка")
    if not lines:
        await update.effective_message.reply_text("ℹ️ Активных наказаний нет.")
        return
    await update.effective_message.reply_text(
        "⛔️ <b>Активные наказания участников:</b>\n\n" + "\n".join(lines), parse_mode=ParseMode.HTML, **NO_PREVIEW
    )


async def remove_punishment_command(update, context):
    if not await require_staff(update, context):
        return
    message = update.effective_message
    args = command_args(message)
    force = any(a.lower() == "принудительно" for a in args)
    args = [a for a in args if a.lower() != "принудительно"]
    target_id, _ = resolve_target(message, args)
    if target_id is None:
        await reply_usage(message, "Используй <code>/сн</code> ответом на сообщение или карточку жалобы, "
                                   "либо <code>/сн @username</code>.")
        return
    punishment = data["punishments"].get(str(target_id))
    if not punishment:
        await message.reply_text(
            f"ℹ️ <b>{saved_user_link(target_id)}</b> — активных наказаний нет",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
        return
    kind = punishment.get("type")
    success = (await remove_mute(target_id, context)) if kind == "mute" else (
        await remove_ban(target_id, context) if kind == "ban" else False
    )
    if not success and force:
        data["punishments"].pop(str(target_id), None)
        success = True
    if not success:
        await message.reply_text(
            "❌ Не удалось снять наказание. Если участника уже нет в чате, "
            "удали запись командой <code>/сн принудительно</code>.",
            parse_mode=ParseMode.HTML,
        )
        return
    log_action(actor_id(update), "punishment_removed", target_id, details=kind)
    await message.reply_text("✅ Наказание снято.")


async def remember_message_users(update, context):
    message, chat = update.effective_message, update.effective_chat
    if not message or not chat or chat.id not in (MAIN_CHAT_ID, ADMIN_CHAT_ID):
        return
    users = [message.from_user] if message.from_user else []
    if message.reply_to_message and message.reply_to_message.from_user:
        users.append(message.reply_to_message.from_user)
    changed = False
    for user in users:
        info = {"id": user.id, "name": user_name(user), "username": user.username}
        if data["users"].get(str(user.id)) != info:
            data["users"][str(user.id)] = info
            changed = True
    if changed:
        save_data()


# =====================================================================
# ПРАВА АДМИНИСТРАТОРОВ, СПРАВКА
# =====================================================================
async def unified_admin_access(update, context, action):
    message, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not message or not chat or chat.id not in (MAIN_CHAT_ID, ADMIN_CHAT_ID):
        return
    if not user or not is_owner(user.id):
        if chat.id == ADMIN_CHAT_ID:
            await message.reply_text("❌ Доступ запрещен!")
        return

    if action == "list":
        ids = sorted(admin_ids())
        if not ids:
            await message.reply_text("ℹ️ Назначенных администраторов нет.")
            return
        lines = []
        for admin_id in ids:
            chat_info = data.get("admin_chats", {}).get(str(admin_id))
            if chat_info:
                title = chat_info.get("title") or f"Чат {admin_id}"
                chat_username = chat_info.get("username")
                # Старые записи data.json могли не содержать username — попробуем получить его заново.
                if not chat_username:
                    try:
                        live_chat = await context.bot.get_chat(int(admin_id))
                        chat_username = getattr(live_chat, "username", None)
                        if chat_username:
                            chat_info["username"] = chat_username
                            chat_info["title"] = live_chat.title or title
                            save_data()
                    except TelegramError:
                        logger.warning("Не удалось получить ссылку для чата администратора %s", admin_id)
                if chat_username:
                    lines.append(
                        f'⛔️ <a href="https://t.me/{esc(str(chat_username).lstrip("@"))}">{esc(title)}</a>'
                    )
                else:
                    lines.append(f"⛔️ {esc(title)} (<code>{admin_id}</code>)")
            else:
                lines.append(f"⛔️ {saved_user_link_with_id(admin_id)}")
        await message.reply_text("👮 <b>Список администраторов:</b>\n\n" + "\n".join(lines),
                                 parse_mode=ParseMode.HTML, **NO_PREVIEW)
        return

    replied = message.reply_to_message
    if not replied:
        command = "/выдатьадмина" if action == "grant" else "/снятьадмина"
        await message.reply_text(f"📍 Используй {command} ответом на сообщение пользователя, чат или карточку заявки.")
        return

    target_chat = replied.sender_chat
    target_user = None if target_chat else replied.from_user
    target_id = target_chat.id if target_chat else (target_user.id if target_user else None)
    if not target_chat:  # ответ на карточку/диалог заявки -> права получает сам пользователь
        _, app = find_application(replied.message_id)
        if not app:
            _, app = find_contact_app(replied.message_id)
        if app:
            target_id, target_user = int(app["user_id"]), None
    if target_id is None:
        await message.reply_text("❌ Не удалось определить пользователя или чат.")
        return
    target_id = int(target_id)
    if target_user and target_user.is_bot:
        await message.reply_text("❌ Нельзя выдать права боту.")
        return
    if target_id == OWNER_ID:
        await message.reply_text("ℹ️ Владелец уже имеет полный доступ." if action == "grant"
                                 else "❌ Нельзя снять права у владельца бота.")
        return

    current = admin_ids()
    if target_chat:
        label = esc(target_chat.title or f"Чат {target_id}")
    else:
        label = mention_user(target_user) if target_user else saved_user_link(target_id)

    if action == "grant":
        if target_id in current:
            await message.reply_text("ℹ️ У этого пользователя или чата уже есть права администратора.")
            return
        current.add(target_id)
        data["admins"] = sorted(current)
        if target_chat:
            data.setdefault("admin_chats", {})[str(target_id)] = {
                "id": target_id,
                "title": target_chat.title or f"Чат {target_id}",
                "type": target_chat.type,
                "username": getattr(target_chat, "username", None),
            }
        log_action(user.id, "admin_access_granted", target_id)
        await message.reply_text(f"⛔️ Права администратора выданы: {label}.", parse_mode=ParseMode.HTML, **NO_PREVIEW)
    else:
        if target_id not in current:
            await message.reply_text("ℹ️ У этого пользователя или чата нет прав администратора.")
            return
        current.discard(target_id)
        data["admins"] = sorted(current)
        data.setdefault("admin_chats", {}).pop(str(target_id), None)
        log_action(user.id, "admin_access_revoked", target_id)
        await message.reply_text(f"⛔️ Права администратора сняты: {label}.", parse_mode=ParseMode.HTML, **NO_PREVIEW)


async def grant_admin_command(update, context):
    await unified_admin_access(update, context, "grant")


async def remove_admin_command(update, context):
    await unified_admin_access(update, context, "revoke")


async def admin_list_command(update, context):
    await unified_admin_access(update, context, "list")


async def unified_help(update, context):
    if not await require_staff(update, context):
        return
    line = "━━━━━━━━━━━━━━━━━━"
    text = (
        "🛠 <b>ПАМЯТКА ПО КОМАНДАМ</b>\n"
        f"{line}\n"
        "⚡ <i>Участник — ответ на сообщение участника, карточку или @username</i>\n\n"

        "⛔ <b>МОДЕРАЦИЯ</b>\n\n"
        "🔔️ <b>/преды</b> — предупреждения и срок их сгорания\n"
        "🧹 <b>/сп</b> — снять все предупреждения\n"
        "🔕 <b>/зж</b> · <b>/рж</b> — запретить или разрешить жалобы\n"
        "📋 <b>/запреты</b> — кому запрещены жалобы\n"
        "⛔ <b>/наказания</b> — активные наказания\n"
        "🔓 <b>/сн</b> — снять наказание\n"
        "   ↳ <i>⚡ /сн принудительно — если участника уже нет в чате</i>\n"
        "📢 <b>#жалоба</b> причина — ответом на сообщение\n"
        "\n"
        f"{line}\n\n"

        "📨 <b>ЗАЯВКИ</b>\n\n"
        "📋 <b>/заявки</b> — на рассмотрении\n"
        "📝 <b>/шаблон</b> — меню шаблона приветствия <i>(владелец, в личке)</i>\n"
        "🚷 <b>/банзаявки</b> [часы] — запрет подачи, по умолчанию 24 ч\n"
        "♾ <b>/банзаявки навсегда</b> — бессрочный запрет\n"
        "✅ <b>/разбанзаявки</b> — снять запрет подачи\n"
        "📃 <b>/списокбанов</b> — кому запрещена подача\n"
        "💬 <b>/конец</b> — завершить диалог с пользователем\n"
        "📜 <b>/журнал</b> — история действий\n\n"
        f"{line}\n\n"

        "🪙 <b>DS КОИНЫ</b>\n\n"
        "🪙 <b>/баланс</b> — свой баланс (в админ-чате: баланс участника, ответом или @username)\n"
        "🏆 <b>/богачи</b> — топ-10 по DS коинам\n"
        "🛍 <b>/шоп</b> — магазин: покупка за DS коины\n"
        "🦊 <b>/мустат</b> — свой профиль: статус, картинка, коины, покупки\n"
        "🔎 <b>/стат</b> — профиль участника с лайком: ответом, @username или ID\n"
        "🎁 <b>/выдатькоины</b> ID количество — выдать или списать коины <i>(в админ-чате)</i>\n"
        "   ↳ <i>или ответом на сообщение: /выдатькоины количество</i>\n\n"
        f"{line}\n\n"

        "⭐ <b>ДОСТУП</b> <i>(только владелец)</i>\n\n"
        "➕ <b>/выдатьадмина</b> · ➖ <b>/снятьадмина</b> — ответом на сообщение\n"
        "👮 <b>/списокадминов</b> — список администраторов\n\n"
        f"{line}\n"
        "ℹ️ <b>/помощь</b> — эта памятка"
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, **NO_PREVIEW)


# =====================================================================
# РЕГИСТРАЦИЯ
# =====================================================================
ROUTES = {
    "/помощь": unified_help,
    "/преды": warnings_command,
    "/сп": remove_warnings_command,
    "/зж": block_reports_command,
    "/рж": unblock_reports_command,
    "/запреты": blocked_reports_list_command,
    "/наказания": punishments_command,
    "/сн": remove_punishment_command,
    "/выдатьадмина": grant_admin_command,
    "/снятьадмина": remove_admin_command,
    "/списокадминов": admin_list_command,
    "/журнал": show_admin_log,
    "/шаблон": template_command,
    "/нажатия": start_log_command,
    "/сбросзаявку": reset_application_command,
    "/конец": end_contact,
    "/банзаявки": block_applications_command,
    "/разбанзаявки": unblock_applications_command,
    "/списокбанов": list_application_bans,
    "/заявки": list_pending_applications,
}


async def command_router(update, context):
    message = update.effective_message
    if not message or not message.text:
        return
    name, _, bot_part = message.text.split(maxsplit=1)[0].partition("@")
    if bot_part and bot_part.lower() != (context.bot.username or "").lower():
        return  # команда адресована другому боту
    handler = ROUTES.get(name.lower())
    if handler:
        await handler(update, context)


async def error_handler(update, context):
    logger.error("Ошибка при обработке обновления", exc_info=context.error)
    if isinstance(context.error, (NetworkError, TimedOut)) or not OWNER_ID:
        return
    last = context.application.bot_data.get("last_error_notice", 0)
    if time.time() - last < 60:
        return
    context.application.bot_data["last_error_notice"] = time.time()
    try:
        await context.bot.send_message(
            OWNER_ID, f"🔔️ Ошибка в боте: {type(context.error).__name__}: {context.error}"[:500]
        )
    except TelegramError:
        pass


# =====================================================================
# ВИКТОРИНА И DS КОИНЫ
# Владелец включает викторину командой /викторина. Вопросы выходят сами каждые N часов.
# На ответ 5 минут, попытка одна. Первый правильный ответ получает 1 DS коин.
# =====================================================================
# Банк вопросов зашит в код: отдельный файл не нужен и не потеряется при сборке.
QUIZ_BANK = [{'q': 'Сколько булыжников нужно для 7 печей? (на 1 печь — 8 булыжников)',
  'correct': '56',
  'wrong': ['64', '48', '54']},
 {'q': 'На сервере 49 игроков, из них 15 в шахте. Сколько игроков на поверхности?',
  'correct': '34',
  'wrong': ['50', '44', '24']},
 {'q': 'В 5 стаках по 64 блока — сколько блоков всего?', 'correct': '320', 'wrong': ['324', '317', '323']},
 {'q': 'Сколько железных слитков нужно для 2 ведер? (на ведро — 3 слитка)',
  'correct': '6',
  'wrong': ['14', '22', '16']},
 {'q': 'Из чего делают кровать?',
  'correct': '3 шерсти и 3 доски',
  'wrong': ['4 шерсти и 2 доски', '5 досок', '6 шерсти']},
 {'q': 'Сколько железных слитков нужно для 9 ведер? (на ведро — 3 слитка)',
  'correct': '27',
  'wrong': ['22', '43', '31']},
 {'q': 'Сколько булыжников нужно для 6 печей? (на 1 печь — 8 булыжников)',
  'correct': '48',
  'wrong': ['64', '56', '44']},
 {'q': 'Сколько предметов влезет в 2 сундука, если в каждом 27 ячеек по 64 предмета?',
  'correct': '3456',
  'wrong': ['3459', '3460', '3454']},
 {'q': 'Из чего делают торт?',
  'correct': 'Молоко, сахар, яйцо и пшеница',
  'wrong': ['Тыква и вода', 'Картофель и соль', 'Морковь и мед']},
 {'q': 'На сервере 89 игроков, из них 13 в шахте. Сколько игроков на поверхности?',
  'correct': '76',
  'wrong': ['44', '78', '140']},
 {'q': 'У игрока 16 единиц здоровья. Сколько сердец? (1 сердце = 2 единицы)',
  'correct': '8',
  'wrong': ['24', '4', '3']},
 {'q': 'Сколько железных слитков нужно для 6 ведер? (на ведро — 3 слитка)',
  'correct': '18',
  'wrong': ['19', '13', '21']},
 {'q': 'Ферма дает 27 пшеницы в час. Сколько пшеницы будет за 5 часов?',
  'correct': '135',
  'wrong': ['131', '143', '134']},
 {'q': 'На сервере 57 игроков, из них 30 в шахте. Сколько игроков на поверхности?',
  'correct': '27',
  'wrong': ['31', '24', '17']},
 {'q': 'У игрока 20 единиц здоровья. Сколько сердец? (1 сердце = 2 единицы)',
  'correct': '10',
  'wrong': ['2', '74', '5']},
 {'q': 'На сервере 79 игроков, из них 27 в шахте. Сколько игроков на поверхности?',
  'correct': '52',
  'wrong': ['57', '49', '50']},
 {'q': 'В инвентаре 30 ячеек заняты, а 11 свободны. Сколько всего ячеек в инвентаре?',
  'correct': '41',
  'wrong': ['38', '36', '40']},
 {'q': 'В инвентаре 14 ячеек заняты, а 8 свободны. Сколько всего ячеек в инвентаре?',
  'correct': '22',
  'wrong': ['24', '6', '21']},
 {'q': 'Сколько пшеницы нужно для 7 хлебов? (на хлеб — 3 пшеницы)',
  'correct': '21',
  'wrong': ['24', '31', '13']},
 {'q': 'В 2 стаках по 64 блока — сколько блоков всего?', 'correct': '128', 'wrong': ['129', '123', '136']},
 {'q': 'У игрока 18 единиц здоровья. Сколько сердец? (1 сердце = 2 единицы)',
  'correct': '9',
  'wrong': ['10', '7', '19']},
 {'q': 'Какой моб убегает от кошек?', 'correct': 'Крипер', 'wrong': ['Зомби', 'Паук', 'Скелет']},
 {'q': 'Сколько булыжников нужно для 9 печей? (на 1 печь — 8 булыжников)',
  'correct': '72',
  'wrong': ['64', '104', '40']},
 {'q': 'На сервере 66 игроков, из них 22 в шахте. Сколько игроков на поверхности?',
  'correct': '44',
  'wrong': ['40', '39', '108']},
 {'q': 'Какой блок светится в темноте?',
  'correct': 'Светокамень',
  'wrong': ['Песчаник', 'Камень', 'Обсидиан']},
 {'q': 'Какой предмет иногда выпадает из листвы?',
  'correct': 'Саженец',
  'wrong': ['Алмаз', 'Золотой слиток', 'Обсидиан']},
 {'q': 'Что быстрее всего восстанавливает голод?', 'correct': 'Стейк', 'wrong': ['Семена', 'Палка', 'Песок']},
 {'q': 'В 3 стаках по 64 блока — сколько блоков всего?', 'correct': '192', 'wrong': ['196', '188', '184']},
 {'q': 'Сколько предметов влезет в 5 сундука, если в каждом 27 ячеек по 64 предмета?',
  'correct': '8640',
  'wrong': ['8637', '8624', '8642']},
 {'q': 'Сколько досок нужно, чтобы сделать 7 сундуков? (на 1 сундук — 8 досок)',
  'correct': '56',
  'wrong': ['58', '72', '55']},
 {'q': 'Почему бедрок нельзя сломать в обычном режиме?',
  'correct': 'Он неразрушимый',
  'wrong': ['Он слишком тяжелый', 'Он сделан из стекла', 'Его охраняет эндермен']},
 {'q': 'На сервере 70 игроков, из них 28 в шахте. Сколько игроков на поверхности?',
  'correct': '42',
  'wrong': ['58', '40', '52']},
 {'q': 'Сколько досок нужно, чтобы сделать 9 сундуков? (на 1 сундук — 8 досок)',
  'correct': '72',
  'wrong': ['104', '80', '74']},
 {'q': 'В инвентаре 10 ячеек заняты, а 20 свободны. Сколько всего ячеек в инвентаре?',
  'correct': '30',
  'wrong': ['28', '31', '26']},
 {'q': 'В инвентаре 16 ячеек заняты, а 10 свободны. Сколько всего ячеек в инвентаре?',
  'correct': '26',
  'wrong': ['34', '18', '42']},
 {'q': 'Ферма дает 11 пшеницы в час. Сколько пшеницы будет за 5 часов?',
  'correct': '55',
  'wrong': ['57', '87', '51']},
 {'q': 'Сколько предметов влезет в 4 сундука, если в каждом 27 ячеек по 64 предмета?',
  'correct': '6912',
  'wrong': ['6920', '6922', '6976']},
 {'q': 'Сколько досок нужно, чтобы сделать 6 сундуков? (на 1 сундук — 8 досок)',
  'correct': '48',
  'wrong': ['80', '16', '64']},
 {'q': 'Сколько булыжников нужно для 2 печей? (на 1 печь — 8 булыжников)',
  'correct': '16',
  'wrong': ['20', '32', '12']},
 {'q': 'Ферма дает 18 пшеницы в час. Сколько пшеницы будет за 5 часов?',
  'correct': '90',
  'wrong': ['26', '154', '98']},
 {'q': 'У игрока 14 единиц здоровья. Сколько сердец? (1 сердце = 2 единицы)',
  'correct': '7',
  'wrong': ['39', '2', '4']},
 {'q': 'Ферма дает 23 пшеницы в час. Сколько пшеницы будет за 5 часов?',
  'correct': '115',
  'wrong': ['112', '114', '105']},
 {'q': 'Что делает ночное зрение?',
  'correct': 'Помогает видеть в темноте',
  'wrong': ['Ускоряет бег', 'Лечит', 'Делает невидимым']},
 {'q': 'У тебя 8 алмазов. Сколько алмазных мечей можно сделать? (на меч — 2 алмаза)',
  'correct': '4',
  'wrong': ['3', '12', '5']},
 {'q': 'На сервере 71 игроков, из них 21 в шахте. Сколько игроков на поверхности?',
  'correct': '50',
  'wrong': ['45', '82', '49']},
 {'q': 'Ферма дает 30 пшеницы в час. Сколько пшеницы будет за 5 часов?',
  'correct': '150',
  'wrong': ['118', '152', '158']},
 {'q': 'У тебя 6 алмазов. Сколько алмазных мечей можно сделать? (на меч — 2 алмаза)',
  'correct': '3',
  'wrong': ['1', '7', '67']},
 {'q': 'В 8 стаках по 64 блока — сколько блоков всего?', 'correct': '512', 'wrong': ['508', '509', '511']}]

QUIZ_INTERVAL = timedelta(minutes=_env_int("QUIZ_INTERVAL_MINUTES", 60))
QUIZ_ANSWER_TTL = timedelta(minutes=5)
QUIZ_WINNERS = 3  # сколько первых верных ответов получают награду
QUIZ_LETTERS = "АБВГ"


def quiz_bank():
    return QUIZ_BANK


def quiz_state():
    return data.setdefault("quiz", {"enabled": False, "next_at": None, "used": [], "current": None, "round": 0})


def ds_balance(user_id):
    return int(data.get("ds_coins", {}).get(str(user_id), 0))


def quiz_keyboard(rid, count):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(QUIZ_LETTERS[i], callback_data=f"qz:{rid}:{i}") for i in range(count)
    ]])


async def quiz_refresh(context, cur, closed=False):
    """Обновляет сообщение с вопросом: призовые места по номерам и сколько мест осталось."""
    winners = cur.get("winners", [])
    lines = [cur["text"], "", "🏆 <b>Призовые места:</b>"]
    for i in range(1, QUIZ_WINNERS + 1):
        name = winners[i - 1]["label"] if i <= len(winners) else "—"
        lines.append(f"{i}. {name}")
    lines.append("")
    lines.append("🏁 Викторина завершена" if closed else f"📝 Осталось мест: {QUIZ_WINNERS - len(winners)}")
    markup = None if closed else quiz_keyboard(cur["round"], cur["count"])
    try:
        await context.bot.edit_message_text(
            text="\n".join(lines), chat_id=MAIN_CHAT_ID, message_id=cur["message_id"],
            parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW,
        )
    except TelegramError:
        pass


async def quiz_finish(context, cur):
    """Раунд с призерами закрыт: последний вид сообщения остается минуту, потом удаляется."""
    st = quiz_state()
    st["current"] = None
    save_data()
    await quiz_refresh(context, cur, closed=True)
    asyncio.create_task(delete_later(context.bot, [(MAIN_CHAT_ID, cur["message_id"])], 60))


async def quiz_end(context, cur):
    """Конец раунда по времени или по выключению викторины."""
    if cur.get("winners"):
        await quiz_finish(context, cur)
    else:
        await quiz_close_round(context, delete=True)


async def quiz_start_round(context):
    bank = quiz_bank()
    st = quiz_state()
    if not bank:
        return False
    used = set(st.get("used", []))
    available = [i for i in range(len(bank)) if i not in used]
    if not available:  # все вопросы уже были: начинаем круг заново
        st["used"] = []
        available = list(range(len(bank)))
    qid = random.choice(available)
    item = bank[qid]
    options = [item["correct"]] + list(item["wrong"])
    random.shuffle(options)
    st["round"] = int(st.get("round", 0)) + 1
    rid = st["round"]
    text = (
        "🧠 <b>ВИКТОРИНА</b>\n\n"
        f"<b>{esc(item['q'])}</b>\n\n"
        + "\n".join(f"{QUIZ_LETTERS[i]}) {esc(o)}" for i, o in enumerate(options))
        + f"\n\n🏆 Первые {QUIZ_WINNERS} верных ответа получают по 20 DS коинов\n⏳ На ответ дается 5 минут. Попытка лишь одна"
    )
    message = await context.bot.send_message(
        MAIN_CHAT_ID, text, parse_mode=ParseMode.HTML, reply_markup=quiz_keyboard(rid, len(options)),
        **NO_PREVIEW,
    )
    st["used"] = list(used | {qid})
    st["current"] = {
        "round": rid, "message_id": message.message_id, "text": text, "count": len(options),
        "correct": options.index(item["correct"]),
        "deadline": (now_utc() + QUIZ_ANSWER_TTL).isoformat(),
        "attempted": [], "winners": [],
    }
    save_data()
    return True


async def delete_later(bot, targets, delay=60):
    """Удаляет сообщения через delay секунд, чтобы не засорять чат."""
    await asyncio.sleep(delay)
    for chat_id, message_id in targets:
        try:
            await bot.delete_message(chat_id, message_id)
        except TelegramError:
            pass


async def quiz_close_round(context, delete=False):
    """Закрывает текущий раунд: убирает кнопки, ответ в чат не выводит."""
    st = quiz_state()
    cur = st.get("current")
    if not cur:
        return
    st["current"] = None
    save_data()
    try:
        if delete:
            await context.bot.delete_message(MAIN_CHAT_ID, cur["message_id"])
        else:
            await context.bot.edit_message_reply_markup(
                chat_id=MAIN_CHAT_ID, message_id=cur["message_id"], reply_markup=None,
            )
    except TelegramError:
        pass


async def quiz_tick(context):
    st = quiz_state()
    if not st.get("enabled"):
        return
    now = now_utc()
    cur = st.get("current")
    if cur:
        if now >= parse_dt(cur["deadline"]):
            await quiz_end(context, cur)
        return
    next_at = parse_dt(st.get("next_at"))
    if next_at is None or now >= next_at:
        st["next_at"] = (now + QUIZ_INTERVAL).isoformat()
        save_data()
        await quiz_start_round(context)


async def quiz_command(update, context):
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id):
        return  # запускать викторину может только владелец
    st = quiz_state()
    if st.get("enabled"):
        st["enabled"] = False
        save_data()
        if st.get("current"):
            await quiz_end(context, st["current"])
        await message.reply_text("⏹ Викторина выключена.")
        return
    if not quiz_bank():
        await message.reply_text("❌ Банк вопросов пуст или не читается.")
        return
    st["enabled"] = True
    st["next_at"] = (now_utc() + QUIZ_INTERVAL).isoformat()
    save_data()
    if not st.get("current"):
        await quiz_start_round(context)
    await message.reply_text(
        f"▶️ Викторина включена. Новый вопрос каждые {int(QUIZ_INTERVAL.total_seconds() // 60)} мин."
    )


async def quiz_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    if is_hidden(user.id) or earn_blocked(user.id):
        await query.answer("Недоступно", show_alert=True)
        return
    st = quiz_state()
    cur = st.get("current")
    try:
        _, rid, idx = query.data.split(":")
        rid, idx = int(rid), int(idx)
    except ValueError:
        await query.answer()
        return
    if not cur or cur["round"] != rid:
        await query.answer("Вопрос уже закрыт", show_alert=True)
        return
    if now_utc() >= parse_dt(cur["deadline"]):
        await query.answer("Время на ответ вышло", show_alert=True)
        await quiz_end(context, cur)
        return
    if str(user.id) in cur["attempted"]:
        await query.answer("Попытка использована на этот вопрос", show_alert=True)
        return
    cur["attempted"].append(str(user.id))
    if idx != cur["correct"]:
        save_data()
        await query.answer("❌ Неверно. Попытка использована.", show_alert=True)
        try:  # владелец видит неверные нажатия в личке, в чат ничего не пишем
            await context.bot.send_message(
                OWNER_ID,
                f"🔘 {mention_user(user)}: вариант {QUIZ_LETTERS[idx]} — неверно "
                f"(правильный {QUIZ_LETTERS[cur['correct']]})",
                parse_mode=ParseMode.HTML, **NO_PREVIEW,
            )
        except TelegramError:
            pass
        return
    winners = cur.setdefault("winners", [])
    if len(winners) >= QUIZ_WINNERS:
        await query.answer("Призовые места уже заняты", show_alert=True)
        return
    winners.append({"uid": user.id, "label": mention_user(user)})
    coins = data.setdefault("ds_coins", {})
    coins[str(user.id)] = ds_balance(user.id) + 20
    log_action(user.id, "quiz_win", user.id, details=f"викторина, раунд {rid}, место {len(winners)}")
    await query.answer(f"✅ Верно! Место: {len(winners)}, +20 DS коинов.", show_alert=True)
    if len(winners) >= QUIZ_WINNERS:
        await quiz_finish(context, cur)
    else:
        save_data()
        await quiz_refresh(context, cur)


GUIDE_PAGES = [
    [
        ("🦊 ПРОФИЛЬ", [
            "▫️ /мустат — свой профиль",
            "▫️ /стат — профиль участника",
        ]),
        ("🪙 КОИНЫ", [
            "▫️ /баланс — свой баланс",
            "▫️ /богачи — топ по балансу",
            "▫️ /шоп — магазин товаров и титулов",
        ]),
    ],
    [
        ("✅ ИГРЫ", [
            "▫️ /кубик — кубик со ставками: 6 дает ×4, 5 дает ×1",
            "▫️ /дуэль @ник 10 — дуэль на кубиках",
            "▫️ /топкубик — топ по кубику за неделю",
            "▫️ /лотерея — твои билеты и шанс",
            "▫️ /лотерея 1 — купить билет, 10 DS коинов",
            "▫️ /мафия — игра в мафию: роли, ночь и голосование",
        ]),
        ("💸 ПЕРЕВОД И БАНК", [
            "▫️ /передать @ник 50 — перевод, комиссия 10% в банк недели",
            "▫️ /банк — банк недели и банк лотереи",
        ]),
    ],
    [
        ("💬 КАК ЗАРАБОТАТЬ", [
            "▫️ Викторина — первый верный ответ дает 20 DS коинов, раз в час",
            "▫️ Листопад — кто первым поймает упавший лист, получает 50 DS коинов",
            "▫️ Мафия — победители получают 50 DS коинов",
            "▫️ Кубик и дуэль — выигрыш забирается из ставки",
            "▫️ Сообщения — каждые 100 дают +100 DS коинов",
        ]),
    ],
]


def guide_text(page):
    lines = ["❓ <b>ЧТО УМЕЕТ БОТ?</b>", "━━━━━━━━━━━━━━━━━━", ""]
    for title, items in GUIDE_PAGES[page]:
        lines.append(f"<b>{title}</b>")
        lines.append("")
        lines.extend(items)
        lines.append("")
    if page == len(GUIDE_PAGES) - 1:
        lines.append("━━━━━━━━━━━━━━━━━━")

    return "\n".join(lines).rstrip()


def guide_markup(page):
    last = len(GUIDE_PAGES) - 1
    row = []
    if page > 0:
        row.append(InlineKeyboardButton("◀️", callback_data=f"gd:{page - 1}"))
    if page < last:
        row.append(InlineKeyboardButton("▶️", callback_data=f"gd:{page + 1}"))
    return InlineKeyboardMarkup([row])


async def public_help_command(update, context):
    """Гайд участника: листается кнопками, страницы меняются в одном сообщении."""
    message = update.effective_message
    if not message:
        return
    try:
        await message.reply_text(guide_text(0), parse_mode=ParseMode.HTML, reply_markup=guide_markup(0),
                                 **NO_PREVIEW)
    except Exception:
        logger.exception("Ошибка в команде /гайд")
        user = update.effective_user
        if user:
            try:
                await context.bot.send_message(user.id, "⚠️ Не удалось показать гайд. Ошибка записана в лог.")
            except TelegramError:
                pass


async def guide_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    try:
        page = int(query.data.split(":")[1])
    except (IndexError, ValueError):
        await query.answer()
        return
    page = min(max(page, 0), len(GUIDE_PAGES) - 1)
    await query.answer()
    try:
        await query.message.edit_text(guide_text(page), parse_mode=ParseMode.HTML,
                                      reply_markup=guide_markup(page), **NO_PREVIEW)
    except TelegramError:
        pass


async def balance_command(update, context):
    """Участник видит свой баланс. Админ в админ-чате может посмотреть баланс другого (ответом или @ником/ID)."""
    message, user = update.effective_message, update.effective_user
    if not message or not user:
        return
    target_id = user.id
    if has_access(user.id) and message.chat.id == ADMIN_CHAT_ID:
        resolved, _ = resolve_target(message, command_args(message))
        if resolved is not None:
            target_id = resolved
    if target_id == user.id:
        text = f"🪙 Баланс: {balance_text(user.id, True)}"
    else:
        text = f"🪙 Баланс {saved_user_link(target_id)}: {balance_text(target_id, False)}"
    await message.reply_text(text, parse_mode=ParseMode.HTML, **NO_PREVIEW)


async def grant_coins_command(update, context):
    """Владелец и админы в админ-чате: /выдатькоины [ник или ID] количество (или ответом на сообщение)."""
    if not await require_staff(update, context, admin_chat_only=True):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not has_access(user.id):
        return
    target_id, rest = resolve_target(message, command_args(message))
    if target_id is None or not rest or not rest[0].lstrip("-").isdigit():
        await reply_usage(message, "Используй <code>/выдатькоины ID количество</code> "
                                   "или ответом на сообщение: <code>/выдатькоины количество</code>.")
        return
    amount = int(rest[0])
    if amount == 0 or abs(amount) > 1000000:
        await message.reply_text("❌ Количество должно быть от -1000000 до 1000000, кроме нуля.")
        return
    coins = data.setdefault("ds_coins", {})
    new_balance = max(0, ds_balance(target_id) + amount)
    coins[str(target_id)] = new_balance
    log_action(user.id, "coins_granted", target_id, details=f"{amount:+d} DS коинов")
    await message.reply_text(
        f"✅ <b>{saved_user_link(target_id)}</b>: {amount:+d} DS коинов\n"
        f"🪙 Баланс: <b>{new_balance}</b>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


def is_hidden(user_id):
    """Скрытые владельцем участники не видны в топе, профилях и подсчетах."""
    return str(user_id) in [str(x) for x in data.get("hidden_users", [])]


async def hide_command(update, context):
    """Владелец: /скрыть и /открыть — ответом, @username или ID."""
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id):
        return
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Используй <code>/скрыть</code> или <code>/открыть</code> "
                                   "ответом на сообщение участника, с @username или с ID.")
        return
    hidden = data.setdefault("hidden_users", [])
    command = (message.text or "").split()[0].lower()
    if command.startswith("/скрыть"):
        if str(target_id) not in [str(x) for x in hidden]:
            hidden.append(target_id)
        log_action(user.id, "user_hidden", target_id)
        await message.reply_text("🙈 Участник скрыт: нет в топе, профиле и подсчетах.")
    else:
        hidden[:] = [x for x in hidden if str(x) != str(target_id)]
        log_action(user.id, "user_shown", target_id)
        await message.reply_text("👁 Участник снова виден.")
    save_data()


def ds_place(user_id):
    """Место участника в топе по балансу (None, если баланс 0 или участник скрыт)."""
    if is_hidden(user_id) or ds_balance(user_id) <= 0:
        return None
    ranking = sorted(((int(u), int(v)) for u, v in data.get("ds_coins", {}).items()
                      if int(v) > 0 and not is_hidden(u)), key=lambda item: (-item[1], item[0]))
    for place, (u, _) in enumerate(ranking, 1):
        if u == int(user_id):
            return place
    return None


def balance_text(user_id, self_view):
    """Баланс с местом в топе: «вы на N месте» для себя, «на N месте» для других."""
    coins = ds_balance(user_id)
    text = f"<b>{coins} {coins_word(coins)}</b>"
    place = ds_place(user_id)
    if place:
        text += f" (вы на {place} месте)" if self_view else f" (на {place} месте)"
    return text


async def coins_top_command(update, context):
    message = update.effective_message
    if not message:
        return
    try:
        top = sorted(((int(uid), int(v)) for uid, v in data.get("ds_coins", {}).items()
                      if int(v) > 0 and not is_hidden(uid)),
                     key=lambda item: (-item[1], item[0]))[:10]
        if not top:
            await message.reply_text("🏆 Пока никто не заработал DS коины.")
            return
        medals = ["🥇", "🥈", "🥉"]
        lines = []
        for i, (uid, coins) in enumerate(top):
            place = medals[i] if i < len(medals) else f"{i + 1}."
            lines.append(f"{place} {saved_user_link(uid)} — <b>{coins}</b>")
        await message.reply_text(
            "🏆 <b>Топ по балансу DS коинов</b>\n\n" + "\n".join(lines),
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except Exception:
        logger.exception("Ошибка в команде /богачи")
        user = update.effective_user
        if user:
            try:
                await context.bot.send_message(user.id, "⚠️ Не удалось показать топ богачей. Ошибка записана в лог.")
            except TelegramError:
                pass


# =====================================================================
# МАГАЗИН
# Участники покупают за DS коины (/шоп). Владелец управляет товарами (/шопс).
# Картинку товара владелец прикрепляет к сообщению: фото с подписью /шопс добавить ...
# =====================================================================
def shop_state():
    return data.setdefault("shop", {"next_id": 1, "items": []})


def shop_find(item_id):
    return next((i for i in shop_state()["items"] if i["id"] == item_id), None)


def shop_active_items():
    return [i for i in shop_state()["items"] if i.get("active", True)]


def parse_shop_add(text):
    """'Название | цена | описание' -> (название, цена, описание) или None."""
    parts = [p.strip() for p in (text or "").split("|")]
    if len(parts) < 2 or not parts[0] or not parts[1].isdigit():
        return None
    price = int(parts[1])
    if not 1 <= price <= 1000000 or len(parts[0]) > 60:
        return None
    return parts[0], price, (parts[2] if len(parts) > 2 else "")


SHOP_USAGE = (
    "Используй:\n"
    "<code>/шопс добавить Название | цена | описание</code>\n"
    "<code>/шопс цена ID новая_цена</code>\n"
    "<code>/шопс удалить ID</code>\n"
    "<code>/шопс обновить</code> — окончательно убрать товары с пометкой «убран»\n"
    "<code>/шопс список</code>\n\n"
    "Картинка: отправь фото с подписью <code>/шопс добавить Название | цена | описание</code>"
)


def shop_add_item(name, price, desc, photo=None, kind="item"):
    state = shop_state()
    item = {"id": state["next_id"], "name": name, "price": price, "desc": desc,
            "photo": photo, "active": True, "kind": kind}
    state["next_id"] += 1
    state["items"].append(item)
    save_data()
    return item


async def shop_admin_command(update, context):
    """Владелец: /шопс добавить | цена | удалить | список."""
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id):
        return
    if message.chat.type != ChatType.PRIVATE:
        await message.reply_text("🔒 Магазин управляется в личке с ботом.")
        return
    parts = (message.text or "").split(maxsplit=2)
    sub = parts[1].lower() if len(parts) > 1 else ""
    if not sub:
        await shop_send_menu(context, message.chat.id)
        return
    tail = parts[2] if len(parts) > 2 else ""

    if sub == "добавить":
        parsed = parse_shop_add(tail)
        if not parsed:
            await reply_usage(message, SHOP_USAGE)
            return
        item = shop_add_item(*parsed)
        await message.reply_text(f"✅ Товар #{item['id']} добавлен: {esc(item['name'])} — {item['price']} DS коинов")
    elif sub == "цена":
        args = tail.split()
        if len(args) != 2 or not args[0].isdigit() or not args[1].isdigit() or not shop_find(int(args[0])):
            await reply_usage(message, SHOP_USAGE)
            return
        item = shop_find(int(args[0]))
        item["price"] = max(1, min(1000000, int(args[1])))
        save_data()
        await message.reply_text(f"✅ Цена «{esc(item['name'])}»: {item['price']} DS коинов")
    elif sub == "удалить":
        item = shop_find(int(tail)) if tail.strip().isdigit() else None
        if not item:
            await reply_usage(message, SHOP_USAGE)
            return
        item["active"] = False
        save_data()
        await message.reply_text(f"🗑 Товар #{item['id']} «{esc(item['name'])}» убран из магазина")
    elif sub == "обновить":
        state = shop_state()
        before = len(state["items"])
        state["items"] = [i for i in state["items"] if i.get("active", True)]
        removed = before - len(state["items"])
        save_data()
        await message.reply_text(
            f"🔄 Магазин обновлен: удалено товаров и титулов с пометкой «убран»: {removed}. "
            f"Осталось: {len(state['items'])}."
        )
    elif sub == "список":
        items = shop_state()["items"]
        if not items:
            await message.reply_text("🛍 Товаров пока нет.")
            return
        lines = []
        for i in items:
            status = "" if i.get("active", True) else " (убран)"
            photo = " 🖼" if i.get("photo") else ""
            kind = "💬" if i.get("kind") == "title" else "🛍"
            lines.append(f"{kind} #{i['id']} {esc(i['name'])} — {i['price']} DS коинов{photo}{status}")
        # Telegram не принимает сообщения длиннее 4096 символов: делим список на части
        chunks, current = [], "🛍 <b>Товары и титулы</b>\n\n"
        for line in lines:
            if len(current) + len(line) + 1 > 3500:
                chunks.append(current)
                current = ""
            current += line + "\n"
        chunks.append(current)
        for chunk in chunks:
            await message.reply_text(chunk, parse_mode=ParseMode.HTML)
    else:
        await reply_usage(message, SHOP_USAGE)


async def shop_photo_add(message, caption):
    """Фото с подписью «/шопс добавить ...» — товар с картинкой."""
    text = re.sub(r"(?i)^/шопс\s+добавить\s*", "", caption, count=1)
    parsed = parse_shop_add(text)
    if not parsed:
        await reply_usage(message, SHOP_USAGE)
        return
    item = shop_add_item(*parsed, photo=message.photo[-1].file_id)
    await message.reply_text(f"✅ Товар #{item['id']} с картинкой добавлен: {esc(item['name'])} — {item['price']} DS коинов")


def coins_word(n):
    n = abs(int(n))
    if 11 <= n % 100 <= 14:
        return "DS коинов"
    return {1: "DS коин", 2: "DS коина", 3: "DS коина", 4: "DS коина"}.get(n % 10, "DS коинов")


SHOP_CATS = {"i": "🛍 Товары", "t": "💬 Титулы"}


def shop_cat_items(cat):
    want = "title" if cat == "t" else "item"
    return [i for i in shop_active_items() if i.get("kind", "item") == want]


def shop_switch_row(cat):
    return [InlineKeyboardButton(("✓ " if key == cat else "") + name, callback_data=f"sp:{key}:0")
            for key, name in SHOP_CATS.items()]


SHOP_PAGE_SIZE = 8


def shop_list_card(page, items, cat):
    """Магазин списком: до SHOP_PAGE_SIZE товаров на странице, покупка по номеру."""
    pages = max(1, (len(items) + SHOP_PAGE_SIZE - 1) // SHOP_PAGE_SIZE)
    page = min(max(page, 0), pages - 1)
    start = page * SHOP_PAGE_SIZE
    chunk = items[start:start + SHOP_PAGE_SIZE]
    kind = "💬 Титулы" if cat == "t" else "🛍 Товары"
    lines = [f"<b>{kind}</b> · стр. {page + 1}/{pages}", ""]
    buy_buttons = []
    for n, item in enumerate(chunk, start + 1):
        lines.append(f"<b>{n}.</b> {esc(item['name'])} — <b>{item['price']} {coins_word(item['price'])}</b>")
        if item.get("desc"):
            lines.append(f"<i>{esc(item['desc'])}</i>")
        lines.append("")
        buy_buttons.append(InlineKeyboardButton(str(n), callback_data=f"shop:buy:{item['id']}"))
    rows = [buy_buttons[i:i + 4] for i in range(0, len(buy_buttons), 4)]
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️", callback_data=f"sp:{cat}:{page - 1}"))
    nav.append(InlineKeyboardButton(f"{page + 1}/{pages}", callback_data=f"sp:{cat}:{page}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("▶️", callback_data=f"sp:{cat}:{page + 1}"))
    rows.append(nav)
    rows.append(shop_switch_row(cat))
    return "\n".join(lines).rstrip(), InlineKeyboardMarkup(rows)


async def shop_show(context, chat_id, page, cat="i"):
    items = shop_cat_items(cat)
    if not items:
        await context.bot.send_message(
            chat_id, "Здесь пока пусто.",
            reply_markup=InlineKeyboardMarkup([shop_switch_row(cat)]),
        )
        return None
    text, markup = shop_list_card(page, items, cat)
    return await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                          reply_markup=markup, **NO_PREVIEW)


async def shop_public_command(update, context):
    message = update.effective_message
    await shop_show(context, message.chat.id, 0, "i")


async def shop_page_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    parts = query.data.split(":")
    try:
        cat = parts[1] if parts[1] in SHOP_CATS else "i"
        page = int(parts[2])
    except (IndexError, ValueError):
        await query.answer()
        return
    await query.answer()
    chat_id = query.message.chat.id
    items = shop_cat_items(cat)
    if not items:
        try:
            await query.message.delete()
        except TelegramError:
            pass
        await shop_show(context, chat_id, 0, cat)
        return
    text, markup = shop_list_card(page, items, cat)
    msg = query.message
    try:
        await context.bot.edit_message_text(
            text=text, chat_id=chat_id, message_id=msg.message_id,
            parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW,
        )
        return
    except TelegramError:
        pass
    try:
        await msg.delete()
    except TelegramError:
        pass
    await shop_show(context, chat_id, page, cat)


async def shop_buy_callback(update, context):
    query = update.callback_query
    if not query:
        return
    user = query.from_user
    try:
        item_id = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        await query.answer()
        return
    item = shop_find(item_id)
    if not item or not item.get("active", True):
        await query.answer("Товар больше не продается", show_alert=True)
        return
    balance = ds_balance(user.id)
    if balance < item["price"]:
        await query.answer(
            f"Недостаточно DS коинов: нужно {item['price']}, у тебя {balance}", show_alert=True,
        )
        return
    if item.get("kind") == "title":
        owned = data.setdefault("titles_owned", {}).setdefault(str(user.id), [])
        if item["id"] in owned:
            await query.answer("Этот титул у тебя уже есть", show_alert=True)
            return
        owned.append(item["id"])
    data.setdefault("ds_coins", {})[str(user.id)] = balance - item["price"]
    add_to_bank(user.id, item["price"] * TRANSFER_FEE_PERCENT // 100)
    purchases = data.setdefault("purchases", [])
    purchases.append({"pid": purchase_next_pid(), "at": now_utc().isoformat(), "user_id": user.id,
                      "item_id": item["id"], "item_name": item["name"], "price": item["price"],
                      "photo": item.get("photo")})
    del purchases[:-500]
    log_action(user.id, "shop_purchase", user.id, details=f"{item['name']} за {item['price']}")
    save_data()
    await query.answer(f"✅ Куплено: {item['name']}. Баланс: {balance - item['price']}", show_alert=True)
    try:  # владелец узнает о покупке и выдает товар вручную
        await context.bot.send_message(
            OWNER_ID,
            f"🛍 Покупка: {mention_user(user)} · «{esc(item['name'])}» за {item['price']} DS коинов",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass


# =====================================================================
# ПРОФИЛЬ УЧАСТНИКА
# /мустат — свой профиль с кнопками (статус, картинка). /стат — профиль любого участника.
# Профиль открытый: монеты, покупки, викторина, статус и картинка.
# =====================================================================
PROFILE_STATUS_MAX = 60
PF_PROMPT_TEXT = {
    "status": "✏️ <b>Пришли статус одним сообщением</b>\n\nДо 60 символов. Отмена — кнопка ниже.",
    "photo": "🖼 <b>Пришли картинку одним сообщением</b>\n\nОтправь фото. Отмена — кнопка ниже.",
}


def get_profile(user_id):
    return data.setdefault("profiles", {}).setdefault(str(user_id), {"status": None, "photo": None})


LIKEGIVE_MIN = 5
LIKEGIVE_MAX = 10
LIKEGIVE_COOLDOWN = timedelta(hours=24)


def like_count(user_id):
    real = len(data.get("likes", {}).get(str(user_id), []))
    return real + int(data.get("bonus_likes", {}).get(str(user_id), 0))


async def likegive_command(update, context):
    """/likegive ответом на сообщение: выдает получателю от 5 до 10 лайков. Выдавать можно раз в сутки."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    replied = message.reply_to_message
    target = replied.from_user if replied else None
    if not target or target.is_bot:
        await message.reply_text("Ответь командой /likegive на сообщение того, кому выдать лайки.")
        return
    last = data.setdefault("likegive_last", {}).get(str(user.id))
    if last and now_utc() - parse_dt(last) < LIKEGIVE_COOLDOWN:
        left = LIKEGIVE_COOLDOWN - (now_utc() - parse_dt(last))
        hours, rest = divmod(int(left.total_seconds()), 3600)
        minutes = rest // 60
        await message.reply_text(f"⏳ Лайки выдаются раз в сутки. Следующие через {hours} ч {minutes} мин.")
        return
    amount = random.randint(LIKEGIVE_MIN, LIKEGIVE_MAX)
    bonus = data.setdefault("bonus_likes", {})
    bonus[str(target.id)] = int(bonus.get(str(target.id), 0)) + amount
    data["likegive_last"][str(user.id)] = now_utc().isoformat()
    save_data()
    if target.id == user.id:
        text = f"❤️ Тебе начислено {amount} {likes_word(amount)} в профиль."
    else:
        text = f"❤️ {mention_user(target)} получает {amount} {likes_word(amount)} от {mention_user(user)}!"
    await message.reply_text(text, parse_mode=ParseMode.HTML, **NO_PREVIEW)


async def toplikes_command(update, context):
    """/toplikes: топ-10 профилей по количеству лайков."""
    message = update.effective_message
    if not message:
        return
    uids = set(data.get("profiles", {}).keys()) | set(data.get("likes", {}).keys()) | set(data.get("bonus_likes", {}).keys())
    ranking = sorted(((int(u), like_count(u)) for u in uids if like_count(u) > 0 and not is_hidden(u)),
                     key=lambda item: (-item[1], item[0]))[:10]
    if not ranking:
        await message.reply_text("❤️ Лайков пока нет.")
        return
    medals = ["🥇", "🥈", "🥉"]
    lines = [f"{medals[i] if i < 3 else f'{i + 1}.'} {saved_user_link(u)} — <b>{n} {likes_word(n)}</b>"
             for i, (u, n) in enumerate(ranking)]
    await message.reply_text("❤️ <b>Топ лайков</b>\n\n" + "\n".join(lines),
                             parse_mode=ParseMode.HTML, **NO_PREVIEW)


def catch_count(user_id, kind):
    """Сколько раз игрок поймал событие: kind = 'leaf' (листопад), позже 'snow' (снегопад)."""
    return int(data.get("catches", {}).get(str(user_id), {}).get(kind, 0))


def add_catch(user_id, kind):
    stats = data.setdefault("catches", {}).setdefault(str(user_id), {})
    stats[kind] = int(stats.get(kind, 0)) + 1


def dislike_count(user_id):
    return len(data.get("dislikes", {}).get(str(user_id), []))


def like_markup(target_id, viewer_id):
    """Два варианта оценки: лайк и дизлайк. Отмеченный — тот, что уже поставлен."""
    me = str(viewer_id)
    liked = me in data.get("likes", {}).get(str(target_id), [])
    like_label = f"{'✓ ' if liked else ''}❤️ {like_count(target_id)}"
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(like_label, callback_data=f"lk:{target_id}"),
    ]])


PROFILE_LINE = "━━━━━━━━━━━━━━━━━━"
MSG_RANKS = [(0, "🌱", "Новичок"), (100, "🗣", "Свой"), (500, "🥉", "Активный"),
             (1500, "🥈", "Душа чата"), (4000, "⭐", "Легенда чата")]
MSG_REWARD_EVERY = 100   # каждые 100 сообщений
MSG_REWARD_COINS = 100   # награда в DS коинах
BUY_RANKS = [(0, "⚪", "Без покупок"), (1, "🛍", "Первый шаг"), (3, "🥉", "Покупатель"),
             (10, "🥈", "Меценат"), (25, "⭐", "Магнат")]
_MSG_DIRTY = {"v": False}


def rank_progress(value, table):
    """Текущий ранг и полоска прогресса до следующего."""
    idx = 0
    for i, (threshold, _, _) in enumerate(table):
        if value >= threshold:
            idx = i
    cur = table[idx]
    if idx + 1 >= len(table):
        return cur, "▰" * 10 + "  максимум"
    nxt = table[idx + 1]
    span = nxt[0] - cur[0]
    filled = min(10, int(10 * (value - cur[0]) / span)) if span else 10
    return cur, "▰" * filled + "▱" * (10 - filled) + f"  {value} / {nxt[0]} до «{nxt[2]}»"


def message_count(user_id):
    return int(data.get("msg_counts", {}).get(str(user_id), 0))


async def count_message(update, context):
    """Считаем сообщения участников в основном чате (команды и сообщения ботов не считаем)."""
    user, message = update.effective_user, update.effective_message
    if not user or user.is_bot or not message or is_hidden(user.id):
        return
    text = message.text or message.caption or ""
    if text.startswith("/"):
        return
    counts = data.setdefault("msg_counts", {})
    counts[str(user.id)] = counts.get(str(user.id), 0) + 1
    _MSG_DIRTY["v"] = True
    total = counts[str(user.id)]
    if total % MSG_REWARD_EVERY == 0:
        coins = data.setdefault("ds_coins", {})
        coins[str(user.id)] = ds_balance(user.id) + MSG_REWARD_COINS
        log_action(user.id, "message_reward", user.id, details=f"{total} сообщений, +{MSG_REWARD_COINS} DS коина")
        try:
            await context.bot.send_message(
                MAIN_CHAT_ID,
                f"🎉 {mention_user(user)}: <b>{total}</b> сообщений, награда "
                f"<b>+{MSG_REWARD_COINS} {coins_word(MSG_REWARD_COINS)}</b>",
                parse_mode=ParseMode.HTML, **NO_PREVIEW,
            )
        except TelegramError:
            pass


def likes_word(n):
    n = abs(int(n))
    if 11 <= n % 100 <= 14:
        return "лайков"
    if n % 10 == 1:
        return "лайк"
    if 2 <= n % 10 <= 4:
        return "лайка"
    return "лайков"


def messages_word(n):
    n = abs(int(n))
    if 11 <= n % 100 <= 14:
        return "сообщений"
    if n % 10 == 1:
        return "сообщение"
    if 2 <= n % 10 <= 4:
        return "сообщения"
    return "сообщений"


CUSTOM_EMOJI_PNG = {
    "fox": "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",
    "pencil": "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",
    "name_tag": "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",
    "sprout": "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",
    "gift": "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",
    "coins": "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",
    "masks": "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",
    "autumn_leaves": "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",
    "heart": "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",
    "crown": "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",
}
CUSTOM_EMOJI_ORDER = list(CUSTOM_EMOJI_PNG.keys())


def custom_emoji_html(key, fallback):
    """Кастомный эмодзи из набора бота, если он создан; иначе обычный значок."""
    emoji_id = data.get("custom_emoji", {}).get(key)
    if not emoji_id:
        return fallback
    return f'<tg-emoji emoji-id="{emoji_id}">{fallback}</tg-emoji>'


async def emoji_set_create(update, context):
    """Владелец: /эмодзисоздать — создает набор кастомных эмодзи из картинок бота."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or not is_owner(user.id):
        return
    import base64
    try:
        bot = context.bot
        stickers = []
        for key in CUSTOM_EMOJI_ORDER:
            png_bytes = base64.b64decode(CUSTOM_EMOJI_PNG[key])
            uploaded = await bot.upload_sticker_file(
                user_id=OWNER_ID,
                sticker=InputFile(io.BytesIO(png_bytes), filename=f"{key}.png"),
                sticker_format="static")
            stickers.append(InputSticker(sticker=uploaded.file_id, emoji_list=["✨"], format="static"))
        old_name = data.get("custom_emoji_set")
        if old_name:
            try:
                await bot.delete_sticker_set(old_name)
            except TelegramError:
                logger.exception("Не удалось удалить старый набор эмодзи")
        name = f"destroycraft_ui2_by_{(bot.username or 'bot').lower()}"
        await bot.create_new_sticker_set(
            user_id=OWNER_ID, name=name, title="DestroyCraft", stickers=stickers,
            sticker_type="custom_emoji")
        created = await bot.get_sticker_set(name)
        ids = [s.custom_emoji_id for s in created.stickers]
        data["custom_emoji"] = dict(zip(CUSTOM_EMOJI_ORDER, ids))
        data["custom_emoji_set"] = name
        save_data()
        await message.reply_text(f"✅ Набор эмодзи создан: {name}")
    except TelegramError as exc:
        logger.exception("Не удалось создать набор эмодзи")
        await message.reply_text(f"❌ Не удалось создать набор: {exc}")


def build_profile(user_id, self_view=False):
    uid = int(user_id)
    prof = get_profile(uid)
    title = shop_find(prof["title"]) if prof.get("title") else None
    msgs = message_count(uid)
    buys = len([p for p in data.get("purchases", []) if int(p.get("user_id", 0)) == uid and not p.get("hidden")])
    coins = ds_balance(uid)
    status = esc(prof["status"]) if prof.get("status") else "Расскажи о себе"
    title_text = esc(title["name"]) if title else "не выбран"
    msg_rank = rank_progress(msgs, MSG_RANKS)[0]
    idx = MSG_RANKS.index(msg_rank)
    if idx + 1 < len(MSG_RANKS):
        nxt = MSG_RANKS[idx + 1]
        next_line = f"   до «<b>{nxt[2]}</b>»: {nxt[0] - msgs}"
    else:
        next_line = "   максимальный ранг"
    lines = [f"{custom_emoji_html('fox', '🦊')} <b>{saved_user_link(uid)}</b>"]
    if prof.get("tags"):
        lines.append(esc(prof["tags"]))
    lines += [
        PROFILE_LINE,
        f"{custom_emoji_html('pencil', '✏️')} {status}",
        f"{custom_emoji_html('name_tag', '🏷')} <b>Титул:</b> {title_text}",
        "",
        f"{msg_rank[1]} <b>{msg_rank[2]}</b> — {msgs} {messages_word(msgs)}",
        next_line,
        "",
        f"{custom_emoji_html('gift', '🛍')} <b>Покупок:</b> {buys}",
        f"{custom_emoji_html('coins', '🪙')} <b>Баланс:</b> {coins} {coins_word(coins)}",
        f"{custom_emoji_html('masks', '🎭')} <b>Мафия:</b> {int(data.get('mafia_games', {}).get(str(uid), 0))} игр · {int(data.get('mafia_wins', {}).get(str(uid), 0))} побед",
        "",
        f"{custom_emoji_html('autumn_leaves', '🍂')} <b>Поймано листьев:</b> {catch_count(uid, 'leaf')}",
        f"{'─' * 4} {custom_emoji_html('heart', '❤️')} <b>{like_count(uid)} {likes_word(like_count(uid))}</b> {'─' * 4}",
    ]
    return "\n".join(lines)


def profile_markup(uid):
    prof = get_profile(uid)
    rows = [[
        InlineKeyboardButton("✏️ Статус", callback_data=f"pf:status:{uid}"),
        InlineKeyboardButton("🖼 Картинка", callback_data=f"pf:photo:{uid}"),
    ]]
    rows.append([InlineKeyboardButton("💬 Титул", callback_data=f"tt:open:{uid}"),
                 InlineKeyboardButton("🛍 Мои покупки", callback_data=f"pu:open:{uid}")])
    extra = []
    if prof.get("status"):
        extra.append(InlineKeyboardButton("🗑 Убрать статус", callback_data=f"pf:clearstatus:{uid}"))
    if prof.get("photo"):
        extra.append(InlineKeyboardButton("🗑 Убрать картинку", callback_data=f"pf:clearphoto:{uid}"))
    if extra:
        rows.append(extra)
    return InlineKeyboardMarkup(rows)


async def render_panel(context, chat_id, uid, text, markup, photo=None, force_new=False):
    """Единое сообщение пользователя: меняем его на месте, новое отправляем только если нельзя
    или если force_new (тогда старое сообщение удаляется, а новое появляется внизу чата)."""
    stored = data.setdefault("profile_msgs", {}).get(str(uid))
    if stored and stored.get("chat") == chat_id and not force_new:
        try:
            if photo and stored.get("photo"):
                await context.bot.edit_message_media(
                    chat_id=chat_id, message_id=stored["msg"],
                    media=InputMediaPhoto(media=photo, caption=text, parse_mode=ParseMode.HTML),
                    reply_markup=markup,
                )
            elif not photo and not stored.get("photo"):
                await context.bot.edit_message_text(
                    text=text, chat_id=chat_id, message_id=stored["msg"],
                    parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW,
                )
            else:
                raise TelegramError("picture added or removed")
            return None
        except TelegramError as exc:
            if "not modified" in str(exc).lower():
                return None
    sent = None
    if photo:
        try:
            sent = await context.bot.send_photo(chat_id, photo, caption=text, parse_mode=ParseMode.HTML,
                                                reply_markup=markup)
        except TelegramError:
            logger.exception("Не удалось отправить картинку профиля пользователя %s", uid)
            photo = None
            text += "\n\n<i>Картинка недоступна, добавь ее заново</i>"
    if sent is None:
        sent = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                              reply_markup=markup, **NO_PREVIEW)
    if stored and stored.get("chat") == chat_id:
        try:
            await context.bot.delete_message(chat_id, stored["msg"])
        except TelegramError:
            pass
    data["profile_msgs"][str(uid)] = {"chat": chat_id, "msg": sent.message_id, "photo": bool(photo)}
    save_data()
    return sent


async def show_profile(context, chat_id, uid, force_new=False):
    return await render_panel(context, chat_id, uid, build_profile(uid, True), profile_markup(uid),
                              get_profile(uid).get("photo"), force_new=force_new)


async def send_profile(context, chat_id, uid, with_buttons, viewer_id=None):
    """Свой профиль — в одном сообщении. Чужой (/стат) — отдельным сообщением с кнопкой лайка."""
    if with_buttons:
        return await show_profile(context, chat_id, uid)
    prof = get_profile(uid)
    text = build_profile(uid)
    markup = None
    if viewer_id is not None and int(viewer_id) != int(uid):
        markup = like_markup(uid, viewer_id)
    if prof.get("photo"):
        try:
            return await context.bot.send_photo(chat_id, prof["photo"], caption=text,
                                                parse_mode=ParseMode.HTML, reply_markup=markup)
        except TelegramError:
            logger.exception("Не удалось отправить картинку профиля пользователя %s", uid)
            text += "\n\n<i>Картинка недоступна, добавь ее заново</i>"
    return await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                          reply_markup=markup, **NO_PREVIEW)


async def my_profile_command(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not user:
        return
    await show_profile(context, message.chat.id, user.id, force_new=True)
    try:  # команду убираем, профиль уже внизу чата
        await message.delete()
    except TelegramError:
        pass


async def profile_command(update, context):
    """/стат: ответом на сообщение, @username или ID. Без аргументов — свой профиль."""
    message = update.effective_message
    if not message:
        return
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        if command_args(message) or message.reply_to_message:
            await reply_usage(message, "Используй <code>/стат</code> ответом на сообщение участника, "
                                       "или <code>/стат @username</code>, или <code>/стат ID</code>.")
            return
        target_id = update.effective_user.id
    if is_hidden(target_id):
        await message.reply_text("🙈 Профиль скрыт.")
        return
    await send_profile(context, message.chat.id, target_id, with_buttons=False, viewer_id=update.effective_user.id)


async def show_prompt(context, chat_id, uid, step, error=None):
    """Подсказка для статуса или картинки — в том же сообщении профиля."""
    text = PF_PROMPT_TEXT[step] + (f"\n\n{error}" if error else "")
    markup = InlineKeyboardMarkup([[InlineKeyboardButton("❌ Отмена", callback_data=f"pf:cancel:{uid}")]])
    photo = get_profile(uid).get("photo") if step == "status" else None
    await render_panel(context, chat_id, uid, text, markup, photo)


async def profile_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    try:
        _, action, uid = query.data.split(":")
        uid = int(uid)
    except ValueError:
        await query.answer()
        return
    if uid != user.id:
        await query.answer("Это не твой профиль", show_alert=True)
        return
    chat_id = query.message.chat.id
    await query.answer()
    prof = get_profile(uid)
    if action in ("status", "photo"):
        context.user_data["pf_step"] = action
        context.user_data["pf_chat"] = chat_id
        context.user_data["pf_uid"] = uid
        await show_prompt(context, chat_id, uid, action)
        return
    if action == "cancel":
        await _pf_close(context, chat_id, uid)
        return
    if action == "clearstatus":
        prof["status"] = None
    elif action == "clearphoto":
        prof["photo"] = None
    else:
        return
    save_data()
    await show_profile(context, chat_id, uid)


async def like_callback(update, context):
    """Лайк или дизлайк профиля. Повторное нажатие снимает оценку. Свой профиль оценивать нельзя."""
    query = update.callback_query
    if not query or not query.data:
        return
    try:
        kind, target = query.data.split(":")[0], int(query.data.split(":")[1])
    except (IndexError, ValueError):
        await query.answer()
        return
    liker = query.from_user.id
    if liker == target:
        await query.answer("Свой профиль оценивать нельзя", show_alert=True)
        return
    me = str(liker)
    likes = data.setdefault("likes", {}).setdefault(str(target), [])
    dislikes = data.setdefault("dislikes", {}).setdefault(str(target), [])
    if kind == "lk":
        if me in likes:
            likes.remove(me)
            popup = "Лайк убран"
        else:
            likes.append(me)
            if me in dislikes:
                dislikes.remove(me)
            popup = "❤️ Лайк поставлен"
    else:
        if me in dislikes:
            dislikes.remove(me)
            popup = "Дизлайк убран"
        else:
            dislikes.append(me)
            if me in likes:
                likes.remove(me)
            popup = "🪙 Дизлайк поставлен"
    save_data()
    await query.answer(popup)
    text = build_profile(target)
    markup = like_markup(target, liker)
    try:
        if query.message.photo:
            await query.message.edit_caption(caption=text, parse_mode=ParseMode.HTML, reply_markup=markup)
        else:
            await query.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW)
    except TelegramError:
        pass


def owned_titles(uid):
    owned = set(data.get("titles_owned", {}).get(str(uid), []))
    return [i for i in shop_state()["items"] if i.get("kind") == "title" and i["id"] in owned]


async def title_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    parts = query.data.split(":")
    try:
        action, uid = parts[1], int(parts[2])
    except (IndexError, ValueError):
        await query.answer()
        return
    if uid != user.id:
        await query.answer("Это не твой профиль", show_alert=True)
        return
    chat_id = query.message.chat.id
    prof = get_profile(uid)
    if action == "open":
        owned = owned_titles(uid)
        if not owned:
            await query.answer("Титулов пока нет. Их можно купить в /шоп", show_alert=True)
            return
        await query.answer()
        rows = [[InlineKeyboardButton(("✅ " if prof.get("title") == i["id"] else "") + i["name"],
                                      callback_data=f"tt:set:{uid}:{i['id']}")] for i in owned]
        rows.append([InlineKeyboardButton("❌ Без титула", callback_data=f"tt:clear:{uid}")])
        rows.append([InlineKeyboardButton("⬅️ В профиль", callback_data=f"tt:back:{uid}")])
        await render_panel(context, chat_id, uid, "💬 <b>Выбери титул</b>", InlineKeyboardMarkup(rows), None)
        return
    if action == "back":
        await query.answer()
        await show_profile(context, chat_id, uid)
        return
    if action == "set" and len(parts) > 3 and parts[3].isdigit():
        item_id = int(parts[3])
        if item_id not in [i["id"] for i in owned_titles(uid)]:
            await query.answer("Этого титула у тебя нет", show_alert=True)
            return
        prof["title"] = item_id
    elif action == "clear":
        prof["title"] = None
    else:
        await query.answer()
        return
    save_data()
    await query.answer()
    await show_profile(context, chat_id, uid)


async def _pf_close(context, chat_id, uid):
    context.user_data.pop("pf_step", None)
    context.user_data.pop("pf_chat", None)
    context.user_data.pop("pf_uid", None)
    await show_profile(context, chat_id, uid)


async def profile_input(update, context):
    """Ждем статус или картинку от участника, который нажал кнопку в профиле."""
    step = context.user_data.get("pf_step")
    message, user = update.effective_message, update.effective_user
    if not step or not message or not user:
        return
    chat_id = message.chat.id
    if chat_id != context.user_data.get("pf_chat") or user.id != context.user_data.get("pf_uid"):
        return
    uid = user.id
    prof = get_profile(uid)
    if step == "status":
        if not message.text or message.text.startswith("/"):
            return
        status = message.text.strip()
        if not status or len(status) > PROFILE_STATUS_MAX:
            try:
                await message.delete()
            except TelegramError:
                pass
            await show_prompt(context, chat_id, uid, "status",
                              error=f"❌ Статус: не больше {PROFILE_STATUS_MAX} символов.")
            return
        prof["status"] = status
    else:
        if not message.photo:
            return
        prof["photo"] = message.photo[-1].file_id
    save_data()
    try:
        await message.delete()
    except TelegramError:
        pass
    await _pf_close(context, chat_id, uid)


# =====================================================================
# ПОКУПКИ: просмотр, скрытие и удаление (кнопки в /мустат)
# =====================================================================


def purchase_next_pid():
    data["purchase_seq"] = int(data.get("purchase_seq", 0)) + 1
    return data["purchase_seq"]


def ensure_purchase_pids():
    for p in data.get("purchases", []):
        if "pid" not in p:
            p["pid"] = purchase_next_pid()
    save_data()


def purchases_view(uid, page):
    """Одна покупка на экране: картинка, цена, дата и кнопки."""
    items = [p for p in reversed(data.get("purchases", [])) if int(p.get("user_id", 0)) == int(uid)]
    back = [InlineKeyboardButton("⬅️ В профиль", callback_data=f"pu:profile:{uid}")]
    if not items:
        return "🛍 <b>Мои покупки</b>\n\nПокупок пока нет.", InlineKeyboardMarkup([back]), None
    pages = len(items)
    page = min(max(page, 0), pages - 1)
    p = items[page]
    photo = p.get("photo") or (shop_find(p.get("item_id")) or {}).get("photo")
    dt = parse_dt(p.get("at"))
    when = fmt_dt(dt) if dt else ""
    hidden = "\n👁 <i>скрыто из профиля</i>" if p.get("hidden") else ""
    text = (
        f"🛍 <b>{esc(p.get('item_name', '?'))}</b>\n\n"
        f"🎁 Цена: <b>{p.get('price', 0)} {coins_word(p.get('price', 0))}</b>\n"
        f"🗓 {esc(when)}{hidden}\n\n"
        f"<i>{page + 1} из {pages}</i>"
    )
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️", callback_data=f"pu:page:{uid}:{page - 1}"))
    nav.append(InlineKeyboardButton(f"{page + 1}/{pages}", callback_data=f"pu:page:{uid}:{page}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("▶️", callback_data=f"pu:page:{uid}:{page + 1}"))
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("👁 Показать" if p.get("hidden") else "🙈 Скрыть",
                              callback_data=f"pu:hide:{uid}:{p['pid']}:{page}"),
         InlineKeyboardButton("🗑 Удалить", callback_data=f"pu:del:{uid}:{p['pid']}:{page}")],
        nav,
        back,
    ])
    return text, markup, photo


async def purchases_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    parts = query.data.split(":")
    try:
        action, uid = parts[1], int(parts[2])
    except (IndexError, ValueError):
        await query.answer()
        return
    if uid != user.id:
        await query.answer("Это не твои покупки", show_alert=True)
        return
    chat_id = query.message.chat.id
    ensure_purchase_pids()
    if action == "profile":
        await query.answer()
        await show_profile(context, chat_id, uid)
        return
    page = 0
    if action == "page":
        page = int(parts[3])
        await query.answer()
    elif action in ("hide", "del"):
        pid, page = int(parts[3]), int(parts[4])
        target = next((p for p in data.get("purchases", [])
                       if p.get("pid") == pid and int(p.get("user_id", 0)) == uid), None)
        if target is None:
            await query.answer("Покупка уже удалена")
        elif action == "hide":
            target["hidden"] = not target.get("hidden", False)
            save_data()
            await query.answer("Готово")
        else:
            data["purchases"].remove(target)
            save_data()
            await query.answer("Удалено")
    elif action == "open":
        await query.answer()
    else:
        await query.answer()
        return
    text, markup, photo = purchases_view(uid, page)
    await render_panel(context, chat_id, uid, text, markup, photo)


# =====================================================================
# МАГАЗИН: меню владельца с кнопками (в личке)
# =====================================================================
async def shop_send_menu(context, chat_id):
    count = len(shop_state()["items"])
    await context.bot.send_message(
        chat_id,
        f"🛍 <b>Управление магазином</b>\n\nТоваров: <b>{count}</b>",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("➕ Добавить товар", callback_data="sh:add"),
             InlineKeyboardButton("💬 Добавить титул", callback_data="sh:addtitle")],
            [InlineKeyboardButton("📋 Товары", callback_data="sh:list")],
        ]),
    )


async def shop_send_list(context, chat_id):
    items = shop_state()["items"]
    if not items:
        await context.bot.send_message(
            chat_id, "📋 Товаров пока нет.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("➕ Добавить товар", callback_data="sh:add")],
                                               [InlineKeyboardButton("🏠 Меню", callback_data="sh:menu")]]),
        )
        return
    rows = []
    for i in items[:30]:
        mark = "" if i.get("active", True) else " (убран)"
        rows.append([InlineKeyboardButton(f"#{i['id']} {i['name']} — {i['price']}{mark}"[:64],
                                          callback_data=f"sh:item:{i['id']}")])
    rows.append([InlineKeyboardButton("🏠 Меню", callback_data="sh:menu")])
    await context.bot.send_message(chat_id, "📋 <b>Товары</b>\n\nВыбери товар для управления:",
                                   parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(rows))


async def shop_send_item(context, chat_id, item):
    active = item.get("active", True)
    kind = "💬 Титул" if item.get("kind") == "title" else "🛍 Товар"
    text = (
        f"{kind} <b>#{item['id']} {esc(item['name'])}</b>\n"
        f"🎁 Цена: <b>{item['price']} DS коинов</b>\n"
        + (f"📝 {esc(item['desc'])}\n" if item.get("desc") else "")
        + f"💬 Статус: {'в продаже' if active else 'убран из магазина'}\n"
        f"🖼 Картинка: {'есть' if item.get('photo') else 'нет'}"
    )
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Цена", callback_data=f"sh:price:{item['id']}"),
         InlineKeyboardButton("🖼 Картинка", callback_data=f"sh:photo:{item['id']}")],
        [InlineKeyboardButton("🗑 Убрать" if active else "♻️ Вернуть", callback_data=f"sh:toggle:{item['id']}")],
        [InlineKeyboardButton("⬅️ К списку", callback_data="sh:list"),
         InlineKeyboardButton("🏠 Меню", callback_data="sh:menu")],
    ])
    if item.get("photo"):
        await context.bot.send_photo(chat_id, item["photo"], caption=text, parse_mode=ParseMode.HTML,
                                     reply_markup=markup)
    else:
        await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=markup,
                                       **NO_PREVIEW)


async def shop_admin_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    if not is_owner(user.id) or query.message.chat.type != ChatType.PRIVATE:
        await query.answer("Нет доступа", show_alert=True)
        return
    chat_id = query.message.chat.id
    parts = query.data.split(":")
    action = parts[1]
    arg = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else None
    await query.answer()

    if action in ("price", "photo", "add", "addtitle"):
        pass  # шаг ввода ниже задается явно
    else:
        context.user_data.pop("shop_step", None)

    if action == "menu":
        await shop_send_menu(context, chat_id)
    elif action == "list":
        await shop_send_list(context, chat_id)
    elif action in ("add", "addtitle"):
        context.user_data["shop_step"] = {"action": action}
        await context.bot.send_message(
            chat_id,
            "➕ <b>Новый товар</b>\n\nПришли одним сообщением:\n<code>Название | цена | описание</code>\n\n"
            "Описание можно не писать. Картинку добавим отдельно кнопкой.",
            parse_mode=ParseMode.HTML,
        )
    elif action in ("price", "photo") and arg is not None:
        item = shop_find(arg)
        if not item:
            await context.bot.send_message(chat_id, "❌ Товар не найден.")
            return
        context.user_data["shop_step"] = {"action": action, "item": arg}
        prompt = (f"✏️ Пришли новую цену для <b>{esc(item['name'])}</b> (число)."
                  if action == "price" else
                  f"🖼 Пришли картинку для <b>{esc(item['name'])}</b> (фото).")
        await context.bot.send_message(chat_id, prompt, parse_mode=ParseMode.HTML)
    elif action == "toggle" and arg is not None:
        item = shop_find(arg)
        if item:
            item["active"] = not item.get("active", True)
            save_data()
            await shop_send_item(context, chat_id, item)
    elif action == "item" and arg is not None:
        item = shop_find(arg)
        if item:
            await shop_send_item(context, chat_id, item)
        else:
            await context.bot.send_message(chat_id, "❌ Товар не найден.")


async def shop_text_input(update, context):
    """Владелец пишет текст в шаге магазина: новый товар или новая цена."""
    step = context.user_data.get("shop_step") or {}
    message = update.effective_message
    text = (message.text or "").strip()
    chat_id = message.chat.id
    if step.get("action") in ("add", "addtitle"):
        parsed = parse_shop_add(text)
        if not parsed:
            await message.reply_text("❌ Формат: <code>Название | цена | описание</code>", parse_mode=ParseMode.HTML)
            return
        item = shop_add_item(*parsed, kind="title" if step["action"] == "addtitle" else "item")
        context.user_data.pop("shop_step", None)
        await message.reply_text(f"✅ Товар #{item['id']} добавлен")
        await shop_send_item(context, chat_id, item)
    elif step.get("action") == "price":
        item = shop_find(step.get("item"))
        if not item or not text.isdigit() or not 1 <= int(text) <= 1000000:
            await message.reply_text("❌ Пришли цену числом от 1 до 1000000.")
            return
        item["price"] = int(text)
        save_data()
        context.user_data.pop("shop_step", None)
        await message.reply_text(f"✅ Новая цена: {item['price']} DS коинов")
        await shop_send_item(context, chat_id, item)


async def shop_photo_input(update, context):
    """Владелец присылает картинку в шаге магазина."""
    step = context.user_data.get("shop_step") or {}
    message = update.effective_message
    if step.get("action") != "photo":
        return
    item = shop_find(step.get("item"))
    if not item:
        context.user_data.pop("shop_step", None)
        return
    item["photo"] = message.photo[-1].file_id
    save_data()
    context.user_data.pop("shop_step", None)
    await message.reply_text("✅ Картинка добавлена")
    await shop_send_item(context, message.chat.id, item)


# =====================================================================
# СУНДУЧКИ: 3 сундучка, за один из них +5 DS коинов. Запускает владелец командой /сундучки.
# Попадание — всплывающее окно. Мест 5. После каждого попадания выигрышный сундучок меняется.
# =====================================================================
CHEST_COUNT = 3
CHEST_PLACES = 5
CHEST_REWARD = 5
CHEST_PRIZES = 2  # сколько из трех сундуков выигрышные: шанс 2 из 3


def chest_state():
    return data.setdefault("chests", {"current": None, "round": 0})


def chest_text(cur, closed=False):
    winners = cur["winners"]
    left = CHEST_PLACES - len(winners)
    lines = [
        "🎁 <b>ИГРА — СУНДУЧКИ</b>",
        "",
        "Выбери один из трех сундучков",
        f"Попадание — <b>+{CHEST_REWARD} DS коинов</b>",
        "",
        f"🏆 До первых {CHEST_PLACES}-ти победителей",
        "",
        "🏆 <b>Призовые места:</b>",
    ]
    for i in range(1, CHEST_PLACES + 1):
        name = winners[i - 1]["label"] if i <= len(winners) else "—"
        lines.append(f"{i}. {name}")
    lines.append("")
    lines.append("🏁 Игра завершена" if closed else f"📝 Осталось мест: <b>{left}</b>")
    return "\n".join(lines)


def chest_keyboard(rid):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(f"🎁 {i + 1}", callback_data=f"ch:{rid}:{i}") for i in range(CHEST_COUNT)
    ]])


async def chest_refresh(context, cur, closed=False):
    markup = None if closed else chest_keyboard(cur["round"])
    text = chest_text(cur, closed)
    try:
        if cur.get("photo"):
            await context.bot.edit_message_caption(
                caption=text, chat_id=MAIN_CHAT_ID, message_id=cur["message_id"],
                parse_mode=ParseMode.HTML, reply_markup=markup,
            )
        else:
            await context.bot.edit_message_text(
                text=text, chat_id=MAIN_CHAT_ID, message_id=cur["message_id"],
                parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW,
            )
    except TelegramError:
        pass


async def chest_end(context, cur):
    """Конец игры: с призерами сообщение живет минуту, без призеров удаляется сразу."""
    st = chest_state()
    st["current"] = None
    save_data()
    if cur["winners"]:
        await chest_refresh(context, cur, closed=True)
        asyncio.create_task(delete_later(context.bot, [(MAIN_CHAT_ID, cur["message_id"])], 60))
    else:
        try:
            await context.bot.delete_message(MAIN_CHAT_ID, cur["message_id"])
        except TelegramError:
            pass


async def chest_command(update, context):
    """Владелец: /сундучки — запуск, /сундучки стоп — остановить."""
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id):
        return
    st = chest_state()
    cur = st.get("current")
    if (message.text or "").lower().endswith("стоп"):
        if cur:
            await chest_end(context, cur)
            await message.reply_text("⏹ Игра остановлена.")
        else:
            await message.reply_text("Игры сейчас нет.")
        return
    if cur:
        await message.reply_text("Игра уже идет.")
        return
    st["round"] = int(st.get("round", 0)) + 1
    rid = st["round"]
    start_text = chest_text({"winners": [], "round": rid})
    photo = data.get("chest_photo")
    if photo:
        sent = await context.bot.send_photo(
            MAIN_CHAT_ID, photo, caption=start_text, parse_mode=ParseMode.HTML,
            reply_markup=chest_keyboard(rid),
        )
    else:
        sent = await context.bot.send_message(
            MAIN_CHAT_ID, start_text, parse_mode=ParseMode.HTML,
            reply_markup=chest_keyboard(rid), **NO_PREVIEW,
        )
    st["current"] = {
        "round": rid, "message_id": sent.message_id, "winners": [], "attempted": [], "photo": bool(photo),
        "picks": [], "prizes": random.sample(range(CHEST_COUNT), CHEST_PRIZES),
    }
    save_data()


async def chest_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    try:
        _, rid, idx = query.data.split(":")
        rid, idx = int(rid), int(idx)
    except ValueError:
        await query.answer()
        return
    st = chest_state()
    cur = st.get("current")
    if not cur or cur["round"] != rid:
        await query.answer("Игра уже закрыта", show_alert=True)
        return
    if is_hidden(user.id) or earn_blocked(user.id):
        await query.answer("Недоступно", show_alert=True)
        return
    if str(user.id) in cur["attempted"]:
        await query.answer("Попытка уже использована", show_alert=True)
        return
    cur["attempted"].append(str(user.id))
    hit = idx in cur["prizes"]
    cur["picks"].append({"label": mention_user(user), "idx": idx, "hit": hit})
    try:  # владелец видит каждый выбор в личке, в чат это не выводится
        await context.bot.send_message(
            OWNER_ID,
            f"🎁 {mention_user(user)}: сундук {idx + 1} — {'попадание' if hit else 'мимо'}",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass
    if not hit:
        save_data()
        await query.answer("❌ Мимо", show_alert=True)
        return
    cur["winners"].append({"uid": user.id, "label": mention_user(user)})
    coins = data.setdefault("ds_coins", {})
    coins[str(user.id)] = ds_balance(user.id) + CHEST_REWARD
    log_action(user.id, "chest_win", user.id, details=f"сундучки, раунд {rid}, место {len(cur['winners'])}")
    await query.answer(f"🎉 Попадание! +{CHEST_REWARD} DS коинов", show_alert=True)
    # выигрышная пара сундуков меняется, чтобы ответ нельзя было передать в чат
    old = set(cur["prizes"])
    pairs = [list(p) for p in itertools.combinations(range(CHEST_COUNT), CHEST_PRIZES)]
    cur["prizes"] = random.choice([p for p in pairs if set(p) != old])
    if len(cur["winners"]) >= CHEST_PLACES:
        await chest_end(context, cur)
    else:
        save_data()
        await chest_refresh(context, cur)


async def chest_tick(context):
    """Таймера у игры сундуков нет: она идет, пока не займут все места или ее не остановят."""
    return


# =====================================================================
# НАБОР АНИМИРОВАННЫХ ЭМОДЗИ (полоска прогресса). Создает владелец командой /эмодзинабор.
# Файлы эмодзи вшиты в код, чтобы не зависеть от папки на сервере.
# =====================================================================
EMOJI_PURPLE_TGS = base64.b64decode("H4sICF/Q3moC/3B1cnBsZS50Z3MA7Zpfc6MgEMC/C8/WkeWPmE9x7x0fbJteM/k7anPtZPLdbwEBbdKau5crN0ynKgjrwi+7rLgnciQLIvIy5yQjzy1ZsCIjqwNZ4Gl/sMVfZCEoZORlOO+22Ofw2h42S+z09PRkWjddt+w7srivM7Jp3petvj7526sdnmlG+ney4IOMh6bTErrW3FljhxPZ60NjuqyxuijOGWkndbrmMKm5LzL8q7G++aS+m9aj2Gz4r8+6297c6l6aw9KqrdUkP1viNNUX+FAc/ePqzZwftqbPCw7rudl0SxzimxnHdocdsP2qD5K6FzJMQeEG6rU5kUey6NtXLQF7aKXr7NsfkfI+Km2PWltWyhyxCzziHV7QXCksVjmnugzmrsSiLnGZlzSjSuRQ6bKEXGZQDH1LyEWVAStyCqas+4KT/KFk2yr9OC+JOUn2OQz0yWvBOLYJOjKhRWDZjoANkimblKhWJrRVY0FSD2P0FBykV4HpCQj6sbHy04Jt6AethbgZsQ/w06XGczlo5mfa6m05GAu0PoWcs8FgnjdoMI8frFlPIsqheFAyo9qwP3EXdJCIYrzIXlvzpeO47jY+dxr1VYd0TY9ufdGsay6qjJ6o27k+1xeut+tN0fgaPZCJN4WpN+36dqXdVxQONSi7syP+K7c6knen/rmL/tolOhd0h75BWyxW33FRuEsmCmsRpuDc1J8YB0ezKAQeJPyHtpFdQV5Gg9x4ZYtWefqg5Ag5hYR8HrmMBTnjyiMHTx8AAnLgKiGfRy5iQQ6Ke87C06dCBeRU8YR8HjmPBjn4BZxWnn7FR8ShSMTnibNYiCNJT5yF6G0UvIkUu90AHGIBXvnFWzryLNh3WsFvYE3jWcH9Aj5cVGHxLlOAPs+6iAQ1c7YsHWkqQ2jut6cS6y9Yx2LWenIGxuCwA4R3byhSiDZPO5YFm0oXh9PKcYcqxGcg0yvYPO1Y4nHwSzYIx52JEJ8xSBHaPO1Y3rfBB+OMOu6chhCNVSlGm6cdy4Ya86/aTDnuXIUojac37Rtox7Jjzv1WGueOu+AhShNpI+0G2rF8EuN+r1xQx13SEKWJtFF+A+1YvnkL/zFMlI67LEOUJtOXsBtoV5HQlv5rt2SOe8lGG2npU/ctuyuxbKVJn89SFg68KkKYVqZklltwx7KbVnK3Xpf+g4iSIU5TPMVpn+CeaErt0/GWTZXz2XWG0Ym82YxHLL5rJf2kTOtNup2RwQYhktscvW8x/u1xyGvcNt26+9HuD8u2Xw0pgavd0f+wt/unJbZv9AT1KT06pUen9OhxevQ1M3y7bnKPmxW625lU4vr8G7F4u2f6MQAA")  # фиолетовое заполненное место
EMOJI_LIME_TGS = base64.b64decode("H4sICF/Q3moC/2xpbWUudGdzAO2azXKbMBCA30VnhUG/CD9F7xkOxHZqxr8D1HXG43fvSiAJYqdKe2nU0WQCrJCWlT7vahG6ojNaIJEVGUcYvbZowXKMmhNawOl4GsSfaCEIxWgzng97aLNr9mtoslqtTN2669Z9hxbPFUa7+m3d6uuru90c4Eww6t/Qgo8aXupOa+hac2cLDa7oqA+1abKF4jy/YdTOynTJaVbynGP4q6C8/qC8m5eDWjz+Vzfd7GhudZv6tB7M1mai7y2yluoLeCj0fdlczPllb9psoFuv9a5bQxcvph/7AzSA+k3vNXUbNA5BbjvqrLmiJVr07Q+tAVpooyv85Y9A+RiVtWdtLStkBtgFHOEOz0mmFIhlxomWqbkrQdQSl1lBMFEio6WWJc0kpvnYtqCZKDFleUaokXVbajW/k4a6Sj/OaWJW0/AcRvXJWcE41PE2MqFVgDz0gI2aCZtJRBvj66qpIqm7MXkKdNKZwPQAePvY1Pi5MFR0ndZK7IgMD3DDpaZjOVrmRnqwe+BgPNB42Qnd8OgwrztwmOU7b84UzrNSH4jERPv1B9GCjApBi9PYa2e+jxuPo8bHMaN6GI8e2dFt76p19V2RsRNsu1W36i7udr0RTajRHZkFUzoPpl3fNjp6RRFPvbGHocd/FVUn+p7UP4/Qv4+INgI9QWjQDgvFT1zk9pKJfHAII9go9Se+IfHgH9rN/jvXwA+IF9EQNzF5IKscfKrkhDihiXiQuIyFOOPKEacOPqXUE6dcJeJB4iIW4lRxh1k4+EQoT5wonogHifNoiFM3eZPSwS/5BDjNE/AgcBYLcADpgDOfuE3yNpHStjBvGgvv0k3c0oJn3rvT7B1GTeKZvd3kPV6UfuIuUmoeRJ1HQppZT5YWNJE+KXerUgn1x6hjcWo9OCNiaqlT6t+5aZ6ysyDsWCZrIm0GTkqLnZY+NaMyvXsFYceSiVM3XVNhsTPhUzNGU3IWhB3LezZ1aTgjFjsnPjtjZUrPgrBjWUZj7hWbKYudK5+g8fSGHYYdyyo5dwtonFvsgvsETaTlszDsWD6Ccbc+LojFLolP0ERaHA/DjuUbt3Cfv0RhscvCJ2gyffsKwy4jgS3d123JLPaCTZbP0qftTyyqxLKAJt3ulSK33FXuM7QibV35BO1Y1tAKbufqwn0DUdKnaIqnFO0x7ZmlZHg63Bq2xbmddAbRFV3MuAgQ37SRblDm5WZrndHBRiWSD/vxvkT/9+dxD+O+7rbdt/Z4Wrd9M27/aw5n97veH1drqF/rAerTTui0EzrthJ7uhH7khpfHLrfcNRBtA9uGq9svjM7wm+MxAAA=")      # желто-зеленое заполненное место
EMOJI_EMPTY_TGS = base64.b64decode("H4sICF/Q3moC/2VtcHR5LnRncwDVVNtugzAM/Rc/R1Eu3MqvTDywlg7U0iLCulaIf5+dQIDSvm+qmnAc++TYkd3DDVIIecwDYHBsIdWCQdVAitu1cfAH0lAqBuW4X2qMKeqme2DM4XCwzrkxRWcg/cgYnPNH0dJ374+rC+6SAcakwROFae3RCSN6uNKS25gTmoUYGLQrG1maleVDMPxlaM/f2M3ajrRs/GcDhV3tkSnzpnC6SSd8tTBJpQ+8FLPfV3e7f9Y2psS8jvnZFJjj3eZRXzAA/atuZjIljDUQU6JeTQ97SLv2mxgwgkRn7M+v+MzXf6X2Rmp1HHF89hBXPAmE5EmCcMcDSVjZ0wghoSDisWQyCbnaEY4Uj5gSY2yseLhjSgsulcUUqybmJ+R8E7rOM+mJyd2jFW1ehQ7QZ9aoQ6JA7DLQI7PUKyRJzOybLIkiSmNxCybpJWgqwKxPL8WvgXP0SRPJVBF3gS9XsqzlqMxX2ul272A70HZZAwMbG+Z4xobZP3Uz15JNi2aSGvvNuJAjI9J4yo66eTs4Xo+N90MjezmQXukwp42byTcmqxO1DdmQbUav6Sy0swYdfgHWT7sgrwUAAA==")    # пустое место
EMOJI_SET_KEYS = {"💜": "purple", "💚": "lime", "⬜": "empty"}


async def read_emoji_ids(context, set_name):
    sset = await context.bot.get_sticker_set(set_name)
    ids = {}
    for sticker in sset.stickers:
        key = EMOJI_SET_KEYS.get(sticker.emoji)
        if key and sticker.custom_emoji_id:
            ids[key] = sticker.custom_emoji_id
    return ids


async def emoji_set_command(update, context):
    """Владелец в личке: создает набор эмодзи и запоминает их ID."""
    if not await require_staff(update, context):
        return
    message, user = update.effective_message, update.effective_user
    if not user or not is_owner(user.id) or message.chat.type != ChatType.PRIVATE:
        return
    st = data.setdefault("emoji", {})
    bot_name = (context.bot.username or "").lower()
    if not bot_name:
        await message.reply_text("❌ Не удалось узнать имя бота. Попробуйте позже.")
        return
    if all(st.get("ids", {}).get(k) for k in ("purple", "lime", "empty")):
        await message.reply_text(f"✅ Набор уже создан: {st.get('set')}")
        return
    # если набор с таким именем уже есть (например, после неудачной попытки) — берем ID из него
    n = 1
    while True:
        # имя набора должно заканчиваться на _by_<имя бота>, номер ставим перед этим окончанием
        set_name = f"destroy_bar_by_{bot_name}" if n == 1 else f"destroy_bar{n}_by_{bot_name}"
        try:
            existing = await read_emoji_ids(context, set_name)
        except TelegramError:
            break  # набора с таким именем нет
        if all(existing.get(k) for k in ("purple", "lime", "empty")):
            st.update({"set": set_name, "ids": existing})
            save_data()
            await message.reply_text(
                f"✅ Набор уже был создан: {set_name}\n"
                f"💜 ID: <code>{existing['purple']}</code>\n"
                f"💚 ID: <code>{existing['lime']}</code>\n"
                f"⬜ ID: <code>{existing['empty']}</code>",
                parse_mode=ParseMode.HTML,
            )
            return
        n += 1
    try:
        # сначала загружаем файлы, потом создаем набор из полученных file_id
        files = {}
        for key, blob in (("purple", EMOJI_PURPLE_TGS), ("lime", EMOJI_LIME_TGS), ("empty", EMOJI_EMPTY_TGS)):
            files[key] = await context.bot.upload_sticker_file(
                user_id=OWNER_ID, sticker=InputFile(io.BytesIO(blob), filename=f"{key}.tgs"),
                sticker_format="animated",
            )
        await context.bot.create_new_sticker_set(
            user_id=OWNER_ID,
            name=set_name,
            title="Полоска прогресса",
            stickers=[
                InputSticker(sticker=files["purple"].file_id, emoji_list=["💜"], format="animated"),
                InputSticker(sticker=files["lime"].file_id, emoji_list=["💚"], format="animated"),
                InputSticker(sticker=files["empty"].file_id, emoji_list=["⬜"], format="animated"),
            ],
            sticker_type="custom_emoji",
        )
    except TelegramError as exc:
        await message.reply_text(f"❌ Не удалось создать набор: {exc}")
        return
    ids = await read_emoji_ids(context, set_name)
    st.update({"set": set_name, "ids": ids})
    save_data()
    await message.reply_text(
        f"✅ Набор создан: {set_name}\n"
        f"💜 ID: <code>{ids.get('purple', '—')}</code>\n"
        f"💚 ID: <code>{ids.get('lime', '—')}</code>\n"
        f"⬜ ID: <code>{ids.get('empty', '—')}</code>",
        parse_mode=ParseMode.HTML,
    )


# =====================================================================
# КУБИК: панель /кубик со ставками и кнопкой «Бросить». Бросок делает бот через ✅.
# Выигрыш = ставка × множитель: 6 — ×4, 5 — ×1, остальное — ничего.
# =====================================================================
DICE_STAKE = 1
DICE_BETS = [1, 5, 10, 25, 50]
DICE_MULT = {6: 4, 5: 1}
DICE_COOLDOWN = timedelta(seconds=30)
DICE_MSG_TTL = 300  # все сообщения игры удаляются через 5 минут
DICE_STREAK_NEED = 3   # сколько выигрышей подряд нужно для бонуса
DICE_STREAK_BONUS = 2  # бонус за следующий выигрыш
DICE_WEEK_PRIZE = 20   # приз первому по кубику за неделю


def dice_bet(user_id):
    return int(data.get("dice_bet", {}).get(str(user_id), DICE_STAKE))


def dice_panel_text(user_id):
    stake = dice_bet(user_id)
    return (
        "✅ <b>Кубик</b>\n\n"
        f"Ставка: <b>{stake} {coins_word(stake)}</b>\n"
        f"6 дает <b>+{(DICE_MULT[6] - 1) * stake}</b>, 5 возвращает ставку, остальное теряет ставку\n"
        f"🪙 Баланс: {balance_text(user_id, True)}\n\n"
        "Выбери ставку и нажми «Бросить»."
    )


def dice_panel_markup(user_id):
    stake = dice_bet(user_id)
    bets = [InlineKeyboardButton(f"{b}{' ✓' if b == stake else ''}", callback_data=f"dc:{user_id}:bet:{b}")
            for b in DICE_BETS]
    return InlineKeyboardMarkup([bets, [InlineKeyboardButton("✅ Бросить", callback_data=f"dc:{user_id}:roll")]])


def dice_check(user, stake):
    """Возвращает текст ошибки или None, если бросок можно сделать."""
    last = parse_dt(data.setdefault("dice_last", {}).get(str(user.id)))
    if last and now_utc() - last < DICE_COOLDOWN:
        left = int((DICE_COOLDOWN - (now_utc() - last)).total_seconds()) + 1
        return f"⏳ Подожди {left} сек. перед следующим броском."
    if earn_blocked(user.id):
        return "⛔ Заработок для тебя отключен."
    balance = ds_balance(user.id)
    if balance < stake:
        return f"❌ Недостаточно DS коинов: нужно {stake}, у тебя {balance}."
    return None


def dice_week_key():
    today = now_utc().date()
    return (today - timedelta(days=today.weekday())).isoformat()


def dice_settle(user, stake, value):
    """Списывает ставку, начисляет выигрыш, ведет серию, статистику и недельный топ."""
    uid = str(user.id)
    streak_map = data.setdefault("dice_streak", {})
    streak = int(streak_map.get(uid, 0))
    win = stake * DICE_MULT.get(value, 0)
    base = win - stake  # выигрыш или проигрыш без бонуса
    bonus = DICE_STREAK_BONUS if base > 0 and streak >= DICE_STREAK_NEED else 0
    change = base + bonus
    new_balance = ds_balance(user.id) + change
    data.setdefault("ds_coins", {})[uid] = new_balance
    data.setdefault("dice_last", {})[uid] = now_utc().isoformat()
    streak = streak + 1 if base > 0 else 0
    streak_map[uid] = streak
    stats = data.setdefault("dice_stats", {}).setdefault(uid, {"rolls": 0, "wins": 0, "best": 0})
    stats["rolls"] += 1
    if base > 0:
        stats["wins"] += 1
    stats["best"] = max(stats["best"], streak)
    week = data.setdefault("dice_week", {"key": dice_week_key(), "profit": {}})
    if week["key"] != dice_week_key():
        data["dice_week_prev"] = week
        week = {"key": dice_week_key(), "profit": {}}
        data["dice_week"] = week
    if change > 0:
        week["profit"][uid] = week["profit"].get(uid, 0) + change
    log_action(user.id, "dice_roll", user.id, details=f"ставка {stake}, выпало {value}, изменение {change:+d}")
    save_data()
    if change > 0:
        result = f"выигрыш <b>+{change} {coins_word(change)}</b>"
    elif change == 0:
        result = "ставка возвращена"
    else:
        result = f"проигрыш <b>{change} {coins_word(-change)}</b>"
    if bonus:
        result += f" ⏳ бонус серии <b>+{bonus}</b>"
    if base > 0 and streak >= 2:
        result += f" · серия {streak}"
    return (f"✅ {mention_user(user)} — выпало <b>{value}</b>, ставка {stake}: {result}\n"
            f"🪙 Баланс: {balance_text(user.id, False)}")


async def dice_week_tick(context):
    """В начале новой недели награждает первого по кубику за прошлую неделю."""
    prev = data.get("dice_week_prev")
    if not prev or prev.get("awarded"):
        return
    prev["awarded"] = True
    save_data()
    profit = prev.get("profit", {})
    if not profit:
        return
    winner, amount = sorted(profit.items(), key=lambda item: (-item[1], item[0]))[0]
    coins = data.setdefault("ds_coins", {})
    coins[winner] = ds_balance(int(winner)) + DICE_WEEK_PRIZE
    save_data()
    try:
        await context.bot.send_message(
            MAIN_CHAT_ID,
            f"🏆 Лучший игрок в кубик за прошлую неделю: <a href=\"tg://user?id={winner}\">игрок</a> "
            f"(выигрыш {amount} DS коинов) и получает <b>+{DICE_WEEK_PRIZE} DS коинов</b>",
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass


async def dice_top_command(update, context):
    """/топкубик: топ по выигрышу в кубик за текущую неделю."""
    message = update.effective_message
    week = data.get("dice_week", {"profit": {}})
    ranking = sorted(((int(u), int(v)) for u, v in week.get("profit", {}).items() if int(v) > 0
                      and not is_hidden(u)), key=lambda item: (-item[1], item[0]))[:10]
    if not ranking:
        await message.reply_text("✅ На этой неделе в кубик еще никто не выигрывал.")
        return
    medals = ["🥇", "🥈", "🥉"]
    lines = [f"{medals[i] if i < 3 else f'{i + 1}.'} {saved_user_link(u)} — <b>+{v}</b>"
             for i, (u, v) in enumerate(ranking)]
    await message.reply_text(
        "✅ <b>Топ кубика за неделю</b>\n\n" + "\n".join(lines),
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


def schedule_delete(bot, chat_id, message_id, delay):
    asyncio.create_task(delete_later(bot, [(chat_id, message_id)], delay))


async def dice_handler(update, context):
    """Игрок сам отправил ✅ в чат — бросок засчитывается по ставке из панели."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or not message.dice or message.dice.emoji != "🎲":
        return
    if is_hidden(user.id):
        return
    schedule_delete(context.bot, MAIN_CHAT_ID, message.message_id, DICE_MSG_TTL)
    stake = dice_bet(user.id)
    error = dice_check(user, stake)
    if error:
        sent = await message.reply_text(error)
        schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)
        return
    text = dice_settle(user, stake, message.dice.value)
    sent = await message.reply_text(text, parse_mode=ParseMode.HTML, **NO_PREVIEW)
    schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)


async def dice_command(update, context):
    """/кубик: панель со ставками только для этого игрока."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or is_hidden(user.id):
        return
    # /кубик можно вызвать не чаще, чем раз в DICE_COOLDOWN, как и бросок
    last = parse_dt(data.setdefault("dice_panel_last", {}).get(str(user.id)))
    if last and now_utc() - last < DICE_COOLDOWN:
        left = int((DICE_COOLDOWN - (now_utc() - last)).total_seconds()) + 1
        sent = await message.reply_text(f"⏳ Подожди {left} сек. перед следующим вызовом /кубик.")
        schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)
        schedule_delete(context.bot, MAIN_CHAT_ID, message.message_id, DICE_MSG_TTL)
        return
    data["dice_panel_last"][str(user.id)] = now_utc().isoformat()
    save_data()
    schedule_delete(context.bot, MAIN_CHAT_ID, message.message_id, DICE_MSG_TTL)
    sent = await context.bot.send_message(
        MAIN_CHAT_ID, dice_panel_text(user.id), parse_mode=ParseMode.HTML,
        reply_markup=dice_panel_markup(user.id), **NO_PREVIEW,
    )
    schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)


async def dice_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    parts = query.data.split(":")
    try:
        uid, action = int(parts[1]), parts[2]
    except (IndexError, ValueError):
        await query.answer()
        return
    if uid != user.id:
        await query.answer("Это не твоя панель", show_alert=True)
        return
    chat_id = query.message.chat.id
    if action == "bet":
        bet = int(parts[3])
        if bet not in DICE_BETS:
            await query.answer()
            return
        data.setdefault("dice_bet", {})[str(user.id)] = bet
        save_data()
        await query.answer(f"Ставка: {bet}")
        try:
            await query.message.edit_text(dice_panel_text(user.id), parse_mode=ParseMode.HTML,
                                          reply_markup=dice_panel_markup(user.id), **NO_PREVIEW)
        except TelegramError:
            pass
        return
    if action == "roll":
        stake = dice_bet(user.id)
        error = dice_check(user, stake)
        if error:
            await query.answer(error, show_alert=True)
            return
        await query.answer()
        rolled = await context.bot.send_dice(chat_id, emoji="🎲")
        schedule_delete(context.bot, chat_id, rolled.message_id, DICE_MSG_TTL)
        text = dice_settle(user, stake, rolled.dice.value)
        sent = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, **NO_PREVIEW)
        schedule_delete(context.bot, chat_id, sent.message_id, DICE_MSG_TTL)
        return
    await query.answer()


# =====================================================================
# МЕНЮ В ЛИЧКЕ (/меню, /menu): магазин и богачи.
# =====================================================================
PROMO_MAX_USES = 2              # активаций на один промокод
PROMO_TTL = timedelta(hours=24)  # срок действия промокода
















async def owner_note(context, text):
    """Уведомление владельцу в личку. Действия самого владельца не присылаем."""
    if not OWNER_ID:
        return
    try:
        await context.bot.send_message(OWNER_ID, text, parse_mode=ParseMode.HTML, **NO_PREVIEW)
    except TelegramError:
        pass






def promo_markup(context):
    """Кнопка под промокодом: открывает чат с ботом, куда вводится код."""
    username = getattr(context.bot, "username", None)
    if not username:
        return None
    return InlineKeyboardMarkup([[InlineKeyboardButton("🎟 Ввести код", url=f"https://t.me/{username}?start=promo")]])


def promo_text(code, promo):
    left = promo.get("max", PROMO_MAX_USES) - len(promo["used"])
    what = f"{promo['amount']} DS коинов"
    if parse_dt(promo["expires"]) < now_utc():
        status = "⛔ Срок действия истек."
    elif left <= 0:
        status = "⛔ Активации закончились."
    else:
        status = f"Осталось активаций: {left} из {promo.get('max', PROMO_MAX_USES)}"
    return (f"🎁 <b>Промокод: <code>{code}</code></b>\n"
            f"Награда: {what}\n"
            f"Введите код в личке с ботом\n\n"
            f"{status}")


async def promo_refresh(context, code, promo):
    if not promo.get("msg"):
        return
    try:
        if promo.get("photo"):
            await context.bot.edit_message_caption(
                caption=promo_text(code, promo), chat_id=MAIN_CHAT_ID, message_id=promo["msg"],
                parse_mode=ParseMode.HTML, reply_markup=promo_markup(context),
            )
        else:
            await context.bot.edit_message_text(
                text=promo_text(code, promo), chat_id=MAIN_CHAT_ID, message_id=promo["msg"],
                parse_mode=ParseMode.HTML, reply_markup=promo_markup(context), **NO_PREVIEW,
            )
    except TelegramError:
        pass


_MEMBER_CACHE = {}


async def is_main_member(context, user_id):
    """Состоит ли участник в основном чате (результат кешируется на 5 минут)."""
    if is_owner(user_id):
        return True
    cached = _MEMBER_CACHE.get(str(user_id))
    if cached and now_utc() - cached[1] < timedelta(minutes=5):
        return cached[0]
    try:
        member = await context.bot.get_chat_member(MAIN_CHAT_ID, user_id)
        ok = member.status in ("member", "administrator", "creator") or (
            member.status == "restricted" and getattr(member, "is_member", False))
    except TelegramError:
        ok = False
    _MEMBER_CACHE[str(user_id)] = (ok, now_utc())
    return ok


def earn_blocked(user_id):
    return str(user_id) in [str(x) for x in data.get("earn_blocked", [])]




async def users_count_command(update, context):
    """Владелец: сколько участников в базе."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or not is_owner(user.id):
        return
    everyone = set(str(x) for x in data.get("dm_users", []))
    everyone |= set(data.get("ds_coins", {}).keys())
    everyone |= set(data.get("profiles", {}).keys())
    everyone |= set(data.get("menus", {}).keys())
    await message.reply_text(
        f"👥 В базе участников: <b>{len(everyone)}</b>\n"
        f"💬 Писали боту в личку: <b>{len(data.get('dm_users', []))}</b>",
        parse_mode=ParseMode.HTML,
    )


async def broadcast_command(update, context):
    """Владелец: /рассылка текст — всем, кто писал боту в личку."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or not is_owner(user.id):
        return
    text = (message.text or "").split(maxsplit=1)
    if len(text) < 2:
        await reply_usage(message, "Используй <code>/рассылка текст сообщения</code>.")
        return
    recipients = list(dict.fromkeys(int(x) for x in data.get("dm_users", [])))
    sent = failed = 0
    for uid in recipients:
        if uid == OWNER_ID:
            continue
        try:
            await context.bot.send_message(uid, text[1], parse_mode=ParseMode.HTML, **NO_PREVIEW)
            sent += 1
        except TelegramError:
            failed += 1
        await asyncio.sleep(0.05)
    await message.reply_text(f"✅ Рассылка: отправлено {sent}, не доставлено {failed}.")


async def earn_block_command(update, context):
    """Владелец: /блокзаработка ID — отключить заработок, повторно — включить."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or not is_owner(user.id):
        return
    target_id, _ = resolve_target(message, command_args(message))
    if target_id is None:
        await reply_usage(message, "Используй <code>/блокзаработка</code> ответом на сообщение "
                                   "или с ID участника.")
        return
    blocked = data.setdefault("earn_blocked", [])
    if str(target_id) in [str(x) for x in blocked]:
        blocked[:] = [x for x in blocked if str(x) != str(target_id)]
        await message.reply_text("✅ Заработок снова доступен.")
    else:
        blocked.append(target_id)
        await message.reply_text("⛔ Заработок для участника отключен: кубик, дуэль, лотерея, викторина, сундуки, мафия.")
    save_data()








async def menu_render(context, chat_id, user_id, notice=None, photo=None, override=None, force_new=False,
                      keyboard=None, inline_markup=None):
    """Меню больше не выводится в сообщении (кнопки внизу). Здесь — только новые сообщения:
    уведомления. Старое сообщение удаляется."""
    if override:
        text, markup = override
        captcha = data.setdefault("captcha_msg", {})
        old = captcha.get(str(user_id))
        sent = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                              reply_markup=markup, **NO_PREVIEW)
        if old:
            try:
                await context.bot.delete_message(chat_id, old)
            except TelegramError:
                pass
        captcha[str(user_id)] = sent.message_id
        save_data()
        return
    if notice:
        await context.bot.send_message(chat_id, notice, parse_mode=ParseMode.HTML,
                                       reply_markup=inline_markup or keyboard, **NO_PREVIEW)


















async def start_promo_command(update, context):
    """Переход по кнопке «Ввести код»: просим отправить код сообщением."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    if not await is_main_member(context, user.id):
        await message.reply_text("🔒 Чтобы пользоваться ботом, сначала вступи в основной чат.")
        raise ApplicationHandlerStop
    context.user_data.pop("menu_step", None)
    await message.reply_text("🎟 Отправь промокод сообщением сюда.")
    raise ApplicationHandlerStop




async def menu_text_first(update, context):
    """Текст в личке: промокод принимаем сразу, если он есть."""
    message = update.effective_message
    text = (message.text or "").strip().upper() if message else ""
    if context.user_data.get("menu_step") != "promo" and text not in data.get("promos", {}):
        return
    await menu_text_input(update, context)
    raise ApplicationHandlerStop


async def menu_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    chat_id = query.message.chat.id
    action = query.data.split(":")[1]
    if not await is_main_member(context, user.id):
        await query.answer("Сначала вступи в основной чат", show_alert=True)
        return
    if action == "shop":
        await query.answer()
        await shop_show(context, chat_id, 0, "i")
        return
    if action == "top":
        await query.answer()
        ranking = sorted(((int(u), int(v)) for u, v in data.get("ds_coins", {}).items()
                          if int(v) > 0 and not is_hidden(u)), key=lambda item: (-item[1], item[0]))[:10]
        if not ranking:
            await context.bot.send_message(chat_id, "🏆 Пока никто не накопил коины.")
            return
        medals = ["🥇", "🥈", "🥉"]
        lines = [f"{medals[i] if i < 3 else f'{i + 1}.'} {saved_user_link(u)} — <b>{v}</b>"
                 for i, (u, v) in enumerate(ranking)]
        await context.bot.send_message(chat_id, "🏆 <b>Богачи</b>\n\n" + "\n".join(lines),
                                       parse_mode=ParseMode.HTML, **NO_PREVIEW)
        return
    if action == "chat":
        await query.answer("Открой основной чат в списке своих чатов в Telegram", show_alert=True)
        return
    await query.answer()


async def menu_text_input(update, context):
    """Ввод промокода в личке: код принимается сразу."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or message.chat.type != ChatType.PRIVATE:
        return
    if not await is_main_member(context, user.id):
        await message.reply_text("🔒 Чтобы пользоваться ботом, сначала вступи в основной чат.")
        return
    context.user_data.pop("menu_step", None)
    code = (message.text or "").strip().upper()
    try:
        await message.delete()
    except TelegramError:
        pass
    promo = data.get("promos", {}).get(code)
    if not promo:
        notice = "❌ Такого промокода нет."
    elif parse_dt(promo["expires"]) < now_utc():
        notice = "❌ Срок действия промокода истек."
    elif len(promo["used"]) >= promo.get("max", PROMO_MAX_USES):
        notice = "❌ Промокод уже закончился."
    elif str(user.id) in promo["used"]:
        notice = "❌ Этот промокод уже использован."
    else:
        data.setdefault("ds_coins", {})[str(user.id)] = ds_balance(user.id) + promo["amount"]
        promo["used"].append(str(user.id))
        notice = f"🎉 Промокод применен: +{promo['amount']} DS коинов."
    save_data()
    if promo:
        await promo_refresh(context, code, promo)
    await menu_render(context, message.chat.id, user.id, notice=notice)
    if user.id != OWNER_ID:
        await owner_note(context, f"🎟 Промокод <code>{esc(code)}</code> введен: {mention_user(user)}. {esc(notice)}")




async def promo_command(update, context):
    """Владелец: /промо coins количество [активаций]. Бот создает код и публикует его в чате."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or not is_owner(user.id):
        return
    parts = (message.text or message.caption or "").split()
    if len(parts) >= 2 and parts[1].lower() == "фото":
        src = message.photo or (message.reply_to_message.photo if message.reply_to_message else None)
        if not src:
            await message.reply_text("Отправь картинку с подписью /промо фото или ответь командой на фото.")
            return
        data["promo_photo"] = src[-1].file_id
        save_data()
        await message.reply_text("✅ Картинка для промокодов сохранена.")
        return
    if len(parts) < 3 or parts[1].lower() not in ("coins", "монеты") or not parts[2].isdigit():
        await reply_usage(message, "Используй <code>/промо coins 50</code>: сразу столько DS коинов.")
        return
    kind = "coins"
    amount = int(parts[2])
    photo = data.get("promo_photo")  # картинка, сохраненная командой /промо фото
    max_uses = int(parts[3]) if len(parts) > 3 and parts[3].isdigit() else PROMO_MAX_USES
    alphabet = string.ascii_uppercase + string.digits
    code = "".join(random.choice(alphabet) for _ in range(6))
    while code in data.get("promos", {}):
        code = "".join(random.choice(alphabet) for _ in range(6))
    data.setdefault("promos", {})[code] = {
        "type": kind, "amount": amount, "max": max_uses, "photo": photo,
        "expires": (now_utc() + PROMO_TTL).isoformat(), "used": [],
    }
    save_data()
    what = f"{amount} DS коинов"
    if photo:
        sent = await context.bot.send_photo(
            MAIN_CHAT_ID, photo, caption=promo_text(code, data["promos"][code]),
            parse_mode=ParseMode.HTML, reply_markup=promo_markup(context),
        )
    else:
        sent = await context.bot.send_message(
            MAIN_CHAT_ID, promo_text(code, data["promos"][code]),
            parse_mode=ParseMode.HTML, reply_markup=promo_markup(context), **NO_PREVIEW,
        )
    data["promos"][code]["msg"] = sent.message_id
    save_data()
    await message.reply_text(f"✅ Код <code>{code}</code> опубликован в чате.", parse_mode=ParseMode.HTML)


# =====================================================================
# ДУЭЛЬ: /duel @ник ставка (или ответом на сообщение). Соперник принимает кнопкой.
# Оба бросают кубик. Больший бросок забирает банк. Ничья — ставки возвращаются.
# =====================================================================
DUEL_TTL = timedelta(minutes=5)


def duel_text(duel, status=None):
    base = (f"⚔️ {saved_user_link(duel['challenger'])} вызывает {saved_user_link(duel['target'])} "
            f"на дуэль: ставка <b>{duel['bet']} {coins_word(duel['bet'])}</b>")
    return base + (f"\n\n{status}" if status else "")


async def duel_command(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or is_hidden(user.id):
        return
    if not await is_main_member(context, user.id):
        return
    args = command_args(message)
    bet = None
    if args and args[-1].isdigit():
        bet = int(args.pop())
    if bet is None or bet not in DICE_BETS:
        await reply_usage(message, "Используй <code>/duel @ник 10</code> или ответом на сообщение: "
                                   f"<code>/duel 10</code>. Ставка: {', '.join(map(str, DICE_BETS))}.")
        return
    target_id, _ = resolve_target(message, args)
    if target_id is None or int(target_id) == user.id:
        await reply_usage(message, "Укажи соперника: ответом на сообщение или @ником.")
        return
    if is_hidden(target_id):
        return
    if ds_balance(user.id) < bet or ds_balance(target_id) < bet:
        await message.reply_text("❌ У одного из игроков не хватает DS коинов для такой ставки.")
        return
    duels = data.setdefault("duels", {})
    duel_id = str(int(data.get("duel_seq", 0)) + 1)
    data["duel_seq"] = int(duel_id)
    duel = {"id": duel_id, "challenger": user.id, "target": int(target_id), "bet": bet}
    markup = InlineKeyboardMarkup([[
        InlineKeyboardButton("⚔️ Принять", callback_data=f"du:acc:{duel_id}"),
        InlineKeyboardButton("❌ Отмена", callback_data=f"du:cancel:{duel_id}"),
    ]])
    sent = await context.bot.send_message(MAIN_CHAT_ID, duel_text(duel), parse_mode=ParseMode.HTML,
                                          reply_markup=markup, **NO_PREVIEW)
    duel["msg"] = sent.message_id
    duels[duel_id] = duel
    save_data()
    asyncio.create_task(duel_expire(context, duel_id))


def duel_roll_markup(duel_id):
    return InlineKeyboardMarkup([[InlineKeyboardButton("✅ Бросить", callback_data=f"du:roll:{duel_id}")]])


def duel_rolls_status(duel):
    rolls = duel.get("rolls", {})
    lines = []
    for uid in (duel["challenger"], duel["target"]):
        if str(uid) in rolls:
            lines.append(f"✅ {saved_user_link(uid)} — <b>{rolls[str(uid)]}</b>")
        else:
            lines.append(f"✅ {saved_user_link(uid)} — ждем бросок")
    return "\n".join(lines) + "\n\nНажмите «✅ Бросить», чтобы кинуть кубик."


async def duel_expire(context, duel_id):
    """Вызов не принят за DUEL_TTL — дуэль отменяется."""
    await asyncio.sleep(DUEL_TTL.total_seconds())
    duel = data.get("duels", {}).get(duel_id)
    if not duel or duel.get("stage") == "rolling":
        return
    data["duels"].pop(duel_id, None)
    save_data()
    try:
        await context.bot.edit_message_text(
            text=duel_text(duel, "⌛ Дуэль отменена: ответа от соперника не было."),
            chat_id=MAIN_CHAT_ID, message_id=duel["msg"], parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass


async def duel_roll_expire(context, duel_id):
    """Не все бросили за DUEL_TTL — ставки возвращаются обоим."""
    await asyncio.sleep(DUEL_TTL.total_seconds())
    duel = data.get("duels", {}).get(duel_id)
    if not duel or duel.get("stage") != "rolling":
        return
    coins = data.setdefault("ds_coins", {})
    for uid in (duel["challenger"], duel["target"]):
        coins[str(uid)] = ds_balance(uid) + duel["bet"]
    data["duels"].pop(duel_id, None)
    save_data()
    try:
        await context.bot.edit_message_text(
            text=duel_text(duel, "⌛ Не все бросили кубик вовремя: ставки возвращены."),
            chat_id=MAIN_CHAT_ID, message_id=duel["msg"], parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass


async def duel_finish(context, duel_id):
    duel = data.get("duels", {}).get(duel_id)
    if not duel:
        return
    v_ch = duel["rolls"][str(duel["challenger"])]
    v_tg = duel["rolls"][str(duel["target"])]
    bet = duel["bet"]
    pot = bet * 2
    coins = data.setdefault("ds_coins", {})
    scores = (f"✅ {saved_user_link(duel['challenger'])} — <b>{v_ch}</b>\n"
              f"✅ {saved_user_link(duel['target'])} — <b>{v_tg}</b>\n")
    if v_ch == v_tg:
        for uid in (duel["challenger"], duel["target"]):
            coins[str(uid)] = ds_balance(uid) + bet
        status = scores + "Ничья — ставки возвращены."
    else:
        winner = duel["challenger"] if v_ch > v_tg else duel["target"]
        coins[str(winner)] = ds_balance(winner) + pot
        status = scores + f"🏆 Победитель: {saved_user_link(winner)}, забирает <b>{pot} {coins_word(pot)}</b>"
        log_action(winner, "duel_win", winner, details=f"дуэль, банк {pot}")
    data["duels"].pop(duel_id, None)
    save_data()
    try:
        await context.bot.edit_message_text(
            text=duel_text(duel, status), chat_id=MAIN_CHAT_ID, message_id=duel["msg"],
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass


async def duel_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    parts = query.data.split(":")
    if len(parts) < 3:
        await query.answer()
        return
    action, duel_id = parts[1], parts[2]
    duel = data.get("duels", {}).get(duel_id)
    if not duel:
        await query.answer("Дуэль уже закрыта", show_alert=True)
        return
    if action == "cancel":
        if user.id not in (duel["challenger"], duel["target"]):
            await query.answer("Это не твоя дуэль", show_alert=True)
            return
        if duel.get("stage") == "rolling":
            await query.answer("Дуэль уже идет", show_alert=True)
            return
        data["duels"].pop(duel_id, None)
        save_data()
        await query.answer()
        await query.message.edit_text(duel_text(duel, "❌ Дуэль отменена."), parse_mode=ParseMode.HTML,
                                      **NO_PREVIEW)
        return
    if action == "acc":
        if user.id != duel["target"]:
            await query.answer("Принять дуэль может только тот, кого вызвали", show_alert=True)
            return
        if duel.get("stage") == "rolling":
            await query.answer()
            return
        bet = duel["bet"]
        if ds_balance(duel["challenger"]) < bet or ds_balance(duel["target"]) < bet:
            data["duels"].pop(duel_id, None)
            save_data()
            await query.answer()
            await query.message.edit_text(duel_text(duel, "❌ У одного из игроков не хватает коинов."),
                                          parse_mode=ParseMode.HTML, **NO_PREVIEW)
            return
        coins = data.setdefault("ds_coins", {})
        coins[str(duel["challenger"])] = ds_balance(duel["challenger"]) - bet
        coins[str(duel["target"])] = ds_balance(duel["target"]) - bet
        duel["stage"] = "rolling"
        duel["rolls"] = {}
        save_data()
        await query.answer()
        await query.message.edit_text(duel_text(duel, duel_rolls_status(duel)), parse_mode=ParseMode.HTML,
                                      reply_markup=duel_roll_markup(duel_id), **NO_PREVIEW)
        asyncio.create_task(duel_roll_expire(context, duel_id))
        return
    if action == "roll":
        if user.id not in (duel["challenger"], duel["target"]):
            await query.answer("Это не твоя дуэль", show_alert=True)
            return
        if duel.get("stage") != "rolling":
            await query.answer()
            return
        if str(user.id) in duel["rolls"]:
            await query.answer("Кубик уже брошен", show_alert=True)
            return
        await query.answer()
        rolled = await context.bot.send_dice(MAIN_CHAT_ID, emoji="🎲")
        schedule_delete(context.bot, MAIN_CHAT_ID, rolled.message_id, DICE_MSG_TTL)
        duel["rolls"][str(user.id)] = rolled.dice.value
        save_data()
        if len(duel["rolls"]) < 2:
            await query.message.edit_text(duel_text(duel, duel_rolls_status(duel)), parse_mode=ParseMode.HTML,
                                          reply_markup=duel_roll_markup(duel_id), **NO_PREVIEW)
            return
        await duel_finish(context, duel_id)
        return
    await query.answer()


# =====================================================================
# ЭКОНОМИКА: передача коинов (комиссия 10% в банк недели), банк недели, лотерея недели.
# =====================================================================
TRANSFER_FEE_PERCENT = 10
LOTTERY_TICKET = 10
BANK_SHARES = [50, 30, 20]  # доли банка недели трем главным вкладчикам, %


def bank_state():
    bank = data.setdefault("bank", {"key": dice_week_key(), "coins": 0, "contrib": {}})
    if bank.get("key") != dice_week_key():
        bank.update({"key": dice_week_key(), "coins": 0, "contrib": {}})
    return bank


def lottery_state():
    lot = data.setdefault("lottery", {"key": dice_week_key(), "pot": 0, "tickets": {}})
    if lot.get("key") != dice_week_key():
        lot.update({"key": dice_week_key(), "pot": 0, "tickets": {}})
    return lot


def add_to_bank(user_id, amount):
    if amount <= 0:
        return
    bank = bank_state()
    bank["coins"] += amount
    contrib = bank["contrib"]
    contrib[str(user_id)] = contrib.get(str(user_id), 0) + amount
    save_data()


LEAF_REWARD = 50
LEAF_LIFETIME = timedelta(minutes=30)


async def leaf_tick(context):
    """Листопад: примерно раз в 4-8 часов падает лист, его можно поймать первым."""
    now = now_utc()
    leaf = data.get("leaf")
    if leaf and not leaf.get("taken"):
        if now - parse_dt(leaf["posted"]) >= LEAF_LIFETIME:
            data.pop("leaf", None)
            save_data()
            try:
                await context.bot.edit_message_text(
                    text="🍂 Лист улетел, никто не успел его поймать.",
                    chat_id=MAIN_CHAT_ID, message_id=leaf["msg"], parse_mode=ParseMode.HTML, **NO_PREVIEW)
                schedule_delete(context.bot, MAIN_CHAT_ID, leaf["msg"], 600)
            except TelegramError:
                pass
        return
    nxt = data.get("leaf_next")
    if nxt is None:
        data["leaf_next"] = (now + timedelta(minutes=30)).isoformat()
        save_data()
        return
    if now < parse_dt(nxt):
        return
    leaf_id = int(data.get("leaf_seq", 0)) + 1
    data["leaf_seq"] = leaf_id
    try:
        sent = await context.bot.send_message(
            MAIN_CHAT_ID, "🍂 <i>С ветки упал лист... Успей поймать первым!</i>",
            parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ Поймать", callback_data=f"lf:{leaf_id}")]]), **NO_PREVIEW)
    except TelegramError:
        return
    data["leaf"] = {"id": leaf_id, "msg": sent.message_id, "posted": now.isoformat(), "taken": False}
    data["leaf_next"] = (now + timedelta(minutes=30)).isoformat()
    save_data()


async def leaf_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    leaf = data.get("leaf")
    try:
        leaf_id = int(query.data.split(":")[1])
    except (IndexError, ValueError):
        await query.answer()
        return
    if not leaf or leaf.get("id") != leaf_id or leaf.get("taken"):
        await query.answer("Лист уже поймали или он улетел", show_alert=True)
        return
    if not await is_main_member(context, user.id):
        await query.answer("Ловить листья могут только участники чата", show_alert=True)
        return
    leaf["taken"] = True
    data.setdefault("ds_coins", {})[str(user.id)] = ds_balance(user.id) + LEAF_REWARD
    add_catch(user.id, "leaf")
    data.pop("leaf", None)
    save_data()
    await query.answer(f"✅ Лист ваш: +{LEAF_REWARD} DS коинов")
    await query.message.edit_text(
        f"🍂 Лист пойман — {mention_user(user)}: <b>+{LEAF_REWARD} {coins_word(LEAF_REWARD)}</b>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW)
    schedule_delete(context.bot, query.message.chat.id, query.message.message_id, 600)




async def econ_week_tick(context):
    """В начале новой недели: банк делится между главными вкладчиками, лотерея разыгрывается."""
    current = dice_week_key()
    bank = data.get("bank")
    if bank and bank.get("key") != current and bank.get("coins", 0) > 0:
        top = sorted(bank["contrib"].items(), key=lambda item: (-item[1], item[0]))[:3]
        lines = []
        for i, (uid, _) in enumerate(top):
            share = bank["coins"] * BANK_SHARES[i] // 100
            data.setdefault("ds_coins", {})[uid] = ds_balance(int(uid)) + share
            lines.append(f"{i + 1}. {saved_user_link(int(uid))} — <b>+{share} {coins_word(share)}</b>")
        bank.update({"key": current, "coins": 0, "contrib": {}})
        save_data()
        try:
            await context.bot.send_message(
                MAIN_CHAT_ID, "🎁 <b>Банк недели распределен</b>\n\n" + "\n".join(lines),
                parse_mode=ParseMode.HTML, **NO_PREVIEW)
        except TelegramError:
            pass
    lot = data.get("lottery")
    if lot and lot.get("key") != current and lot.get("tickets"):
        pool = [int(uid) for uid, count in lot["tickets"].items() for _ in range(int(count))]
        winner = random.choice(pool)
        prize = lot.get("pot", 0)
        data.setdefault("ds_coins", {})[str(winner)] = ds_balance(winner) + prize
        total = sum(int(c) for c in lot["tickets"].values())
        lot.update({"key": current, "pot": 0, "tickets": {}})
        save_data()
        try:
            await context.bot.send_message(
                MAIN_CHAT_ID,
                f"🎟 <b>Лотерея недели</b>: билетов продано {total}. Победитель "
                f"{saved_user_link(winner)} забирает банк <b>{prize} {coins_word(prize)}</b>",
                parse_mode=ParseMode.HTML, **NO_PREVIEW)
        except TelegramError:
            pass


async def transfer_command(update, context):
    """/передать @ник сумма (или ответом на сообщение): перевод коинов с комиссией 10% в банк недели."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or is_hidden(user.id):
        return
    if not await is_main_member(context, user.id):
        return
    args = command_args(message)
    if not args or not args[-1].isdigit():
        await reply_usage(message, "Используй <code>/передать @ник 50</code> или ответом на сообщение: "
                                   "<code>/передать 50</code>. Комиссия 10% уходит в банк недели.")
        return
    amount = int(args.pop())
    target_id, _ = resolve_target(message, args)
    if target_id is None or int(target_id) == user.id or is_hidden(target_id):
        await reply_usage(message, "Укажи получателя: ответом на сообщение или @ником.")
        return
    if amount < 1:
        return
    if ds_balance(user.id) < amount:
        await message.reply_text(f"❌ Недостаточно {coins_word(ds_balance(user.id))}: у тебя {ds_balance(user.id)}.")
        return
    fee = amount * TRANSFER_FEE_PERCENT // 100
    received = amount - fee
    coins = data.setdefault("ds_coins", {})
    coins[str(user.id)] = ds_balance(user.id) - amount
    coins[str(target_id)] = ds_balance(int(target_id)) + received
    add_to_bank(user.id, fee)
    log_action(user.id, "transfer", int(target_id), details=f"{amount}, комиссия {fee}")
    sent = await message.reply_text(
        f"🎁 {mention_user(user)} → {saved_user_link(int(target_id))}: "
        f"<b>{received} {coins_word(received)}</b> (комиссия в банк недели: {fee})",
        parse_mode=ParseMode.HTML, **NO_PREVIEW)
    schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)


async def lottery_command(update, context):
    """/лотерея N: купить N билетов по 10 DS коинов. Деньги уходят в банк лотереи."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or is_hidden(user.id):
        return
    if not await is_main_member(context, user.id):
        return
    args = command_args(message)
    if not args:
        lot = lottery_state()
        mine = int(lot["tickets"].get(str(user.id), 0))
        total = sum(int(c) for c in lot["tickets"].values())
        chance = mine * 100 / total if total else 0
        sent = await message.reply_text(
            f"🎟 <b>Лотерея недели</b>\n\n"
            f"Твои билеты: <b>{mine}</b>\n"
            f"Всего билетов: {total}\n"
            f"Шанс выиграть: <b>{chance:.1f}%</b>\n"
            f"Банк лотереи: <b>{lot['pot']} DS {coins_word(lot['pot'])}</b>\n\n"
            f"Купить билеты: <code>/лотерея 1</code> (10 DS коинов за билет)",
            parse_mode=ParseMode.HTML, **NO_PREVIEW)
        schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)
        return
    if not args[0].isdigit():
        await reply_usage(message, "Купить билеты: <code>/лотерея 1</code>. Посмотреть свои: <code>/лотерея</code>.")
        return
    count = int(args[0])
    if count < 1 or count > 20:
        await reply_usage(message, "Укажи от 1 до 20 билетов: <code>/лотерея 3</code>.")
        return
    cost = count * LOTTERY_TICKET
    if ds_balance(user.id) < cost:
        await message.reply_text(f"❌ Нужно {cost} {coins_word(cost)} за {count} билетов, "
                                 f"у тебя {ds_balance(user.id)}.")
        return
    lot = lottery_state()
    data.setdefault("ds_coins", {})[str(user.id)] = ds_balance(user.id) - cost
    lot["pot"] += cost
    lot["tickets"][str(user.id)] = int(lot["tickets"].get(str(user.id), 0)) + count
    save_data()
    sent = await message.reply_text(
        f"🎟 Покупка: {mention_user(user)}, билетов: {count}. Всего билетов: {lot['tickets'][str(user.id)]}. "
        f"Банк лотереи: <b>{lot['pot']} {coins_word(lot['pot'])}</b>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW)
    schedule_delete(context.bot, MAIN_CHAT_ID, sent.message_id, DICE_MSG_TTL)


async def bank_command(update, context):
    """/банк: текущий банк недели и банк лотереи."""
    message = update.effective_message
    if not message:
        return
    bank = bank_state()
    lot = lottery_state()
    await message.reply_text(
        f"🎁 Банк недели: <b>{bank['coins']} {coins_word(bank['coins'])}</b>\n"
        f"🎟 Банк лотереи: <b>{lot['pot']} {coins_word(lot['pot'])}</b>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW)


# =====================================================================
# МАФИЯ: набор в основном чате, роли в личке, ночь 60 с, день 2 мин, голосование 1 мин.
# Запускать может любой участник. Вход бесплатный. Победители получают MAFIA_REWARD DS коинов.
# =====================================================================
MAFIA_MIN = 3
MAFIA_MAX = 12
MAFIA_REWARD = 50
MAFIA_NIGHT = timedelta(seconds=60)
MAFIA_DAY = timedelta(seconds=60)
MAFIA_VOTE = timedelta(seconds=60)
MAFIA_LOBBY = timedelta(minutes=3)      # набор открыт 3 минуты
MAFIA_EXTEND = timedelta(minutes=2)     # одно продление набора
MAFIA_MAX_EXTENDS = 3
MAFIA_HANG = timedelta(seconds=45)  # подтверждение казни
MAFIA_NIGHT_PHRASES = [
    "Город засыпает. Где-то скрипит половица...",
    "Ночь опустилась на город. Кто-то уже не спит...",
    "Фонари гаснут. В тишине слышны чужие шаги...",
    "Луна скрылась за тучами. Город затих...",
]
MAFIA_ACTION_LINES = {
    "kill": "🎯 Мафия выбрала жертву...",
    "heal": "💉 Выбор доктора сделан...",
    "check": "🕵️ Проверка комиссара начата...",
    "block": "💃 Путана выбрала цель...",
    "guard": "⛔ Пост телохранителя занят...",
    "mkill": "🔪 Ход маньяка сделан...",
    "shoot": "🔫 Кто-то достает оружие...",
}
MAFIA_ROLES = {
    "mirny": ("🙂 Мирный житель",
              "Днем ищи мафию и голосуй против нее. Твоя сила — в общем голосе."),
    "mafia": ("🎯 Мафия",
              "Ночью вместе с другими мафиози выбираешь жертву. Днем притворяйся мирным."),
    "don": ("🎩 Дон мафии",
            "Ты главный мафиози. Командуешь ночным выбором. Комиссар видит тебя как мирного."),
    "doctor": ("💉 Доктор",
               "Ночью лечишь одного игрока. Можно лечить и себя. Вылеченного не убьют."),
    "commissar": ("🕵️ Комиссар",
                  "Ночью проверяешь одного игрока: мафия он или нет. Дон выглядит мирным."),
    "bodyguard": ("⛔ Телохранитель",
                  "Ночью защищаешь одного игрока, кроме себя. Защищенного не убьют этой ночью."),
    "putana": ("💃 Путана",
               "Ночью блокируешь одного игрока: его ночное действие не сработает."),
    "maniac": ("🔪 Маньяк",
               "Ты сам за себя. Каждую ночь убиваешь одного игрока. Побеждаешь, если останешься один."),
}
MAFIA_SIDE = {"mirny": "town", "doctor": "town", "commissar": "town", "bodyguard": "town",
              "putana": "town", "mafia": "mafia", "don": "mafia", "maniac": "maniac"}
MAFIA_PHOTO_KEYS = {"набор": "lobby", "ночь": "night", "день": "day", "голосование": "vote", "победа": "win", "казнь": "hang"}
MAFIA_GAMES = {}   # chat_id -> игра
MAFIA_BY_ID = {}   # id игры -> игра
MAFIA_SEQ = {"n": 0}
MAFIA_EXPECT_MUTE = set()  # участники, которых ограничивает сама игра (не выбывать из-за этого)


class MafiaGame:
    def __init__(self, chat_id):
        MAFIA_SEQ["n"] += 1
        self.id = MAFIA_SEQ["n"]
        self.chat_id = chat_id
        self.players = {}      # uid -> {"name", "role", "alive"}
        self.phase = "lobby"
        self.day = 1
        self.actions = {"kill": {}, "heal": {}, "check": {}, "block": {}, "guard": {}, "mkill": {}, "shoot": {}}
        self.votes = {}
        self.lobby_msg = None
        self.messages = []     # id сообщений игры в чате, чтобы удалить после конца
        self.muted = set()     # погибшие, которых ограничили в чате
        self.task = None
        self.lobby_deadline = now_utc() + MAFIA_LOBBY
        self.lobby_ext = 0
        self.lobby_photo = False  # набор отправлен картинкой: тогда обновляем подпись
        self.seat = {}         # uid -> номер игрока, фиксируется на всю игру
        self.announced = set() # что уже объявлено в чате этой ночью
        self.last_word = set() # погибшие, которые могут сказать одну последнюю реплику
        self.heal_history = {} # доктор uid -> кого уже лечил
        self.self_healed = set() # доктора, которые уже лечили себя
        self.night_event = None
        self.kill_by = {}
        self.started_at = None
        self.bot_username = None
        self.shots_used = set()  # комиссары, которые уже стреляли
        self.afk = {}  # uid -> сколько действий подряд пропущено
        self.vote_event = None
        self.hang_event = None
        self.vote_msg = None
        self.vote_photo = False
        self.ref_msg = None
        self.ref_photo = False
        self.hang_votes = {}   # голоса ✅ / ⛔️ в казни: uid -> True / False


def mafia_link(uid, name):
    return f'<a href="tg://user?id={uid}">{esc(name)}</a>'


def mafia_roles_for(count):
    mafia = max(1, count // 4)
    roles = ["mafia"] * mafia
    if mafia >= 2:
        roles[0] = "don"
    roles += ["doctor", "commissar"]
    if count >= 6:
        roles.append("bodyguard")
    if count >= 7:
        roles.append("putana")
    if count >= 8:
        roles.append("maniac")
    roles += ["mirny"] * (count - len(roles))
    return roles


def mafia_alive(game):
    return {uid: p for uid, p in game.players.items() if p["alive"]}


def mafia_check_win(game):
    alive = mafia_alive(game)
    if not alive:
        return "nobody"
    sides = [MAFIA_SIDE[p["role"]] for p in alive.values()]
    mafia_count = sides.count("mafia")
    maniac_count = sides.count("maniac")
    town_count = sides.count("town")
    if maniac_count and len(alive) == 1:
        return "maniac"
    if mafia_count == 0 and maniac_count == 0:
        return "town"
    if mafia_count and mafia_count >= town_count + maniac_count and not (
            len(alive) == 2 and mafia_count == 1 and maniac_count == 0):
        return "mafia"
    return None


def mafia_survivors_text(game):
    alive = list(mafia_alive(game).values())
    if not alive:
        return "👥 <b>Живых не осталось</b>"
    counts = {}
    for p in alive:
        counts[p["role"]] = counts.get(p["role"], 0) + 1
    roles = " · ".join(MAFIA_ROLES[role][0] + (f" ×{c}" if c > 1 else "") for role, c in counts.items())
    players = "\n".join(f"{game.seat.get(uid, 0)}. {p.get('link', p['name'])}"
                         for uid, p in sorted(mafia_alive(game).items(), key=lambda kv: game.seat.get(kv[0], 0)))
    return (f"👥 <b>Живые: {len(alive)}</b>\n{players}\n\n"
            f"🎭 <b>Среди них</b>: {roles}")




def mafia_photo(key):
    return data.get("mafia_photos", {}).get(key)


def mafia_lobby_text(game):
    left = max(0, int((game.lobby_deadline - now_utc()).total_seconds() // 60) + 1)
    names = "\n".join(f"▫️ {p.get('link', p['name'])}" for p in game.players.values()) or "▫️ пока никого"
    return ("🎯 Открыт набор в мафию. Жми кнопку «🙋 Играть».\n\n"
            f"👥 Игроков: <b>{len(game.players)}</b> из {MAFIA_MAX} (минимум {MAFIA_MIN})\n\n"
            f"{names}\n\n"
            f"⏳ До старта: около {left} мин.")


def mafia_lobby_markup(game):
    if game.bot_username:
        join_button = InlineKeyboardButton("🙋 Играть",
                                           url=f"https://t.me/{game.bot_username}?start=mafia{game.id}")
    else:
        join_button = InlineKeyboardButton("🙋 Играть", callback_data=f"mf:join:{game.id}")
    return InlineKeyboardMarkup([
        [join_button,
         InlineKeyboardButton("🚪 Выйти", callback_data=f"mf:leave:{game.id}")],
        [InlineKeyboardButton("⏳ Продлить", callback_data=f"mf:extend:{game.id}"),
         InlineKeyboardButton("▶️ Начать", callback_data=f"mf:start:{game.id}")],
    ])


async def mafia_send(context, chat_id, text, markup=None, photo_key=None):
    photo = mafia_photo(photo_key) if photo_key else None
    if photo:
        try:
            sent = await context.bot.send_photo(chat_id, photo, caption=text, parse_mode=ParseMode.HTML,
                                                reply_markup=markup)
            return sent.message_id
        except TelegramError:
            logger.exception("Не удалось отправить картинку фазы %s", photo_key)
    sent = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                          reply_markup=markup, **NO_PREVIEW)
    return sent.message_id


async def mafia_dm(context, uid, text, markup=None):
    try:
        await context.bot.send_message(uid, text, parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW)
    except TelegramError:
        pass


async def mafia_set_mute(context, chat_id, uid, muted):
    """Запрет или снятие записи в чате. Нужны права администратора у бота с правом ограничивать участников."""
    if muted:
        MAFIA_EXPECT_MUTE.add(uid)
        permissions = ChatPermissions(
            can_send_messages=False, can_send_audios=False, can_send_documents=False,
            can_send_photos=False, can_send_videos=False, can_send_video_notes=False,
            can_send_voice_notes=False, can_send_polls=False, can_send_other_messages=False,
            can_add_web_page_previews=False)
    else:
        permissions = ChatPermissions.all_permissions()
    try:
        await context.bot.restrict_chat_member(chat_id, uid, permissions)
    except TelegramError as exc:
        MAFIA_EXPECT_MUTE.discard(uid)
        logger.warning("Не удалось изменить права участника %s в чате %s: %s", uid, chat_id, exc)


async def mafia_command(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    if message.chat.id in MAFIA_GAMES:
        await message.reply_text("🎭 Игра уже идет или набирается.")
        return
    game = MafiaGame(message.chat.id)
    MAFIA_GAMES[message.chat.id] = game
    MAFIA_BY_ID[game.id] = game
    game.bot_username = (context.bot.username or "").lower() or None
    game.lobby_msg = await mafia_send(context, message.chat.id, mafia_lobby_text(game),
                                      mafia_lobby_markup(game), photo_key="lobby")
    game.lobby_photo = bool(mafia_photo("lobby"))
    asyncio.create_task(mafia_lobby_watch(context, game))


async def mafia_edit_lobby(context, game, text=None, parse_mode=None, reply_markup=None, **kwargs):
    """Обновляет сообщение набора: у картинки меняем подпись, у текста — сам текст."""
    if game.lobby_photo:
        await context.bot.edit_message_caption(
            caption=text, chat_id=game.chat_id, message_id=game.lobby_msg,
            parse_mode=parse_mode, reply_markup=reply_markup)
    else:
        await mafia_edit_lobby(context, game, 
            text=text, chat_id=game.chat_id, message_id=game.lobby_msg,
            parse_mode=parse_mode, reply_markup=reply_markup, **kwargs)


async def mafia_refresh_lobby(context, game):
    try:
        await mafia_edit_lobby(context, game, 
            text=mafia_lobby_text(game), chat_id=game.chat_id, message_id=game.lobby_msg,
            parse_mode=ParseMode.HTML, reply_markup=mafia_lobby_markup(game), **NO_PREVIEW)
    except TelegramError:
        pass


async def mafia_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    parts = query.data.split(":")
    try:
        action, gid = parts[1], int(parts[2])
    except (IndexError, ValueError):
        await query.answer()
        return
    game = MAFIA_BY_ID.get(gid)
    if not game:
        await query.answer("Игра уже закончилась", show_alert=True)
        return

    if action == "join":
        if game.phase != "lobby":
            await query.answer("Набор закрыт", show_alert=True)
            return
        if user.id in game.players:
            await query.answer("Ты уже в игре")
            return
        if len(game.players) >= MAFIA_MAX:
            await query.answer("Игроков уже максимум", show_alert=True)
            return
        if not await is_main_member(context, user.id):
            await query.answer("Сначала вступи в основной чат", show_alert=True)
            return
        if str(user.id) not in [str(x) for x in data.get("dm_users", [])]:
            await query.answer("Сначала открой бота в личке и напиши /start", show_alert=True)
            return
        game.players[user.id] = {"name": user.full_name, "link": mafia_link(user.id, user.full_name),
                                 "role": None, "alive": True}
        await query.answer("Ты в игре")
        await mafia_refresh_lobby(context, game)
        return

    if action == "leave":
        if game.phase == "lobby" and user.id in game.players:
            game.players.pop(user.id)
            await query.answer("Выход из набора")
            await mafia_refresh_lobby(context, game)
        else:
            await query.answer()
        return

    if action == "extend":
        if game.phase != "lobby":
            await query.answer("Набор уже закрыт", show_alert=True)
            return
        if game.lobby_ext >= MAFIA_MAX_EXTENDS:
            await query.answer("Набор уже продлен максимум", show_alert=True)
            return
        game.lobby_deadline += MAFIA_EXTEND
        game.lobby_ext += 1
        await query.answer("Набор продлен на 2 минуты")
        await mafia_refresh_lobby(context, game)
        return
    if action == "start":
        if game.phase != "lobby":
            await query.answer()
            return
        if len(game.players) < MAFIA_MIN:
            await query.answer(f"Нужно минимум {MAFIA_MIN} игроков", show_alert=True)
            return
        await query.answer()
        await mafia_begin(context, game)
        return

    if action == "act":
        kind, target = parts[3], int(parts[4])
        player = game.players.get(user.id)
        if game.phase != "night" or not player or not player["alive"]:
            await query.answer("Сейчас нельзя", show_alert=True)
            return
        allowed = {"kill": ("mafia", "don"), "heal": ("doctor",), "check": ("commissar",),
                   "block": ("putana",), "guard": ("bodyguard",), "mkill": ("maniac",),
                   "shoot": ("commissar",)}.get(kind, ())
        if player["role"] not in allowed:
            await query.answer("Это не твоя роль", show_alert=True)
            return
        target_player = game.players.get(target)
        if not target_player or not target_player["alive"]:
            await query.answer("Этот игрок уже не в игре", show_alert=True)
            return
        if target == user.id and kind != "heal":
            await query.answer("Себя выбрать нельзя", show_alert=True)
            return
        if kind == "heal" and target == user.id and user.id in game.self_healed:
            await query.answer("Лечить себя можно только один раз", show_alert=True)
            return
        if kind == "heal" and target != user.id and target in game.heal_history.get(user.id, set()):
            await query.answer("Этого игрока уже лечили", show_alert=True)
            return
        if user.id in game.actions[kind]:
            chosen = game.players[game.actions[kind][user.id]]["name"]
            await query.answer(f"Выбор уже сделан: {chosen}", show_alert=True)
            return
        game.actions[kind][user.id] = target
        key = f"act:{kind}"
        if key not in game.announced:
            game.announced.add(key)
            await mafia_send(context, game.chat_id, f"<i>{MAFIA_ACTION_LINES.get(kind, '')}</i>")
        verbs = {"kill": "выбираешь жертву:", "heal": "лечишь", "check": "проверяешь",
                 "block": "блокируешь", "guard": "защищаешь", "mkill": "убиваешь",
                 "shoot": "стреляешь в"}
        await query.answer(f"Ты {verbs[kind]} {target_player['name']}", show_alert=True)
        if mafia_night_ready(game) and game.night_event:
            game.night_event.set()
        return

    if action == "hang":
        vote = parts[3] == "1"
        player = game.players.get(user.id)
        if game.phase != "hang" or not player or not player["alive"]:
            await query.answer("Сейчас голосовать нельзя", show_alert=True)
            return
        game.hang_votes[user.id] = vote
        await query.answer("Голос принят")
        if game.ref_msg:
            try:
                await context.bot.edit_message_reply_markup(chat_id=game.chat_id, message_id=game.ref_msg,
                                                            reply_markup=mafia_ref_markup(game))
            except TelegramError:
                pass
        if mafia_all_voted(game, game.hang_votes) and game.hang_event:
            game.hang_event.set()
        return

    if action == "mode":
        mode = parts[3]
        player = game.players.get(user.id)
        if game.phase != "night" or not player or not player["alive"] or player["role"] != "commissar":
            await query.answer("Сейчас нельзя", show_alert=True)
            return
        if user.id in game.actions["check"] or user.id in game.actions["shoot"]:
            await query.answer("Действие уже выбрано", show_alert=True)
            return
        await query.answer()
        await mafia_dm(context, user.id,
                       "🔍 Кого проверяешь этой ночью?" if mode == "check" else "🎯 В кого стреляешь этой ночью?",
                       mafia_player_buttons(game, mode, user.id))
        return

    if action == "vote":
        target = int(parts[3])
        player = game.players.get(user.id)
        if game.phase != "vote" or not player or not player["alive"]:
            await query.answer("Сейчас голосовать нельзя", show_alert=True)
            return
        if target != 0 and (target not in game.players or not game.players[target]["alive"]):
            await query.answer("Этот игрок уже не в игре", show_alert=True)
            return
        if target == user.id:
            await query.answer("Себя выбрать нельзя", show_alert=True)
            return
        game.votes[user.id] = target
        await query.answer("Голос принят")
        if game.vote_msg:
            await mafia_edit_msg(context, game, game.vote_msg, mafia_vote_text(game),
                                 mafia_vote_markup(game), game.vote_photo)
        if mafia_all_voted(game, game.votes) and game.vote_event:
            game.vote_event.set()
        return

    await query.answer()


async def mafia_lobby_watch(context, game):
    """Когда время набора вышло: старт при минимуме игроков, иначе набор закрывается."""
    while game.phase == "lobby":
        await asyncio.sleep(10)
        if game.phase != "lobby":
            return
        if now_utc() < game.lobby_deadline:
            continue
        if len(game.players) >= MAFIA_MIN:
            await mafia_begin(context, game)
            return
        game.phase = "closed"
        MAFIA_GAMES.pop(game.chat_id, None)
        MAFIA_BY_ID.pop(game.id, None)
        try:
            await mafia_edit_lobby(context, game, 
                text="\n\n\n"
                     f"❌ Набор закрыт: не набрали минимум {MAFIA_MIN} игроков.",
                chat_id=game.chat_id, message_id=game.lobby_msg, parse_mode=ParseMode.HTML, **NO_PREVIEW)
        except TelegramError:
            pass
        return


async def mafia_begin(context, game):
    if game.phase != "lobby":
        return
    roles = mafia_roles_for(len(game.players))
    random.shuffle(roles)
    for (uid, player), role in zip(game.players.items(), roles):
        player["role"] = role
    game.seat = {uid: i for i, uid in enumerate(game.players, 1)}
    game.phase = "starting"
    game.started_at = now_utc()
    if game.lobby_msg:
        try:
            await mafia_edit_lobby(context, game, 
                text="\n\n\nИгра началась. Роли отправлены в личку с ботом.",
                chat_id=game.chat_id, message_id=game.lobby_msg, parse_mode=ParseMode.HTML, **NO_PREVIEW)
        except TelegramError:
            pass
    for uid, player in game.players.items():
        title, desc = MAFIA_ROLES[player["role"]]
        await mafia_dm(context, uid,
                       f"🎭 <b>Твоя роль: {title}</b>\n\n\n{desc}\n\n"
                       "⏳ Первая ночь скоро. Действия выбирай кнопками в этом чате.")
    data["mafia_active"] = {"chat_id": game.chat_id, "game_id": game.id}
    save_data()
    game.task = asyncio.create_task(mafia_loop(context, game))


def mafia_player_buttons(game, kind, actor):
    rows = []
    for uid, p in mafia_alive(game).items():
        if kind != "heal" and uid == actor:
            continue
        rows.append([InlineKeyboardButton(p["name"], callback_data=f"mf:act:{game.id}:{kind}:{uid}")])
    return InlineKeyboardMarkup(rows) if rows else None


ROLE_KINDS = {"mafia": ("kill",), "don": ("kill",), "doctor": ("heal",),
              "commissar": ("check", "shoot"), "bodyguard": ("guard",),
              "putana": ("block",), "maniac": ("mkill",)}


def mafia_night_ready(game):
    """Все живые с ночным действием уже выбрали цель."""
    for uid, p in mafia_alive(game).items():
        kinds = ROLE_KINDS.get(p["role"])
        if kinds and not any(uid in game.actions[k] for k in kinds):
            return False
    return True


def mafia_all_voted(game, votes):
    return set(mafia_alive(game)) <= set(votes)




async def mafia_mute_alive(context, game, muted):
    for uid in list(mafia_alive(game)):
        await mafia_set_mute(context, game.chat_id, uid, muted)


async def mafia_edit_msg(context, game, msg_id, text, markup, is_photo):
    try:
        if is_photo:
            await context.bot.edit_message_caption(caption=text, chat_id=game.chat_id, message_id=msg_id,
                                                   parse_mode=ParseMode.HTML, reply_markup=markup)
        else:
            await context.bot.edit_message_text(text=text, chat_id=game.chat_id, message_id=msg_id,
                                                parse_mode=ParseMode.HTML, reply_markup=markup, **NO_PREVIEW)
    except TelegramError:
        pass


async def mafia_track_afk(context, game, acted_kinds):
    """Предупреждает, если игрок не сделал ход два раза подряд. Игра при этом не ждет его дольше таймера."""
    for uid, p in mafia_alive(game).items():
        kinds = acted_kinds.get(p["role"])
        if not kinds:
            continue
        if any(uid in game.actions[k] for k in kinds):
            game.afk[uid] = 0
            continue
        game.afk[uid] = game.afk.get(uid, 0) + 1
        if game.afk[uid] == 2:
            try:
                await context.bot.send_message(
                    game.chat_id,
                    f"⏳ {p.get('link', esc(p['name']))} молчит уже второй ход подряд. Игра идет без него.",
                    parse_mode=ParseMode.HTML, **NO_PREVIEW)
            except TelegramError:
                pass


async def mafia_night(context, game):
    game.phase = "night"
    game.actions = {"kill": {}, "heal": {}, "check": {}, "block": {}, "guard": {}, "mkill": {}, "shoot": {}}
    game.announced = set()
    game.last_word = set()
    game.messages.append(await mafia_send(
        context, game.chat_id,
        f"🌙 <b>НОЧЬ {game.day}</b>\n\n\n"
        f"<i>{random.choice(MAFIA_NIGHT_PHRASES)}</i>\n\n"
        "Роли действуют в личке с ботом.\n\n⏳ На выбор 1 минута",
        photo_key="night"))
    await mafia_mute_alive(context, game, True)
    prompts = {
        "mafia": ("🎯 Выбери жертву этой ночью:", "kill"),
        "don": ("🎩 Выбери жертву этой ночью:", "kill"),
        "doctor": ("💉 Кого лечишь этой ночью?", "heal"),
        "bodyguard": ("⛔ Кого защищаешь этой ночью?", "guard"),
        "putana": ("💃 Кого соблазняешь этой ночью?", "block"),
        "maniac": ("🔪 Кого убиваешь этой ночью?", "mkill"),
    }
    for uid, p in mafia_alive(game).items():
        if p["role"] == "commissar":
            markup = InlineKeyboardMarkup([[
                InlineKeyboardButton("🔍 Проверить", callback_data=f"mf:mode:{game.id}:check"),
                InlineKeyboardButton("🎯 Стрелять", callback_data=f"mf:mode:{game.id}:shoot"),
            ]])
            await mafia_dm(context, uid, "🕵️ Что делаешь этой ночью?", markup)
        elif p["role"] in prompts:
            text, kind = prompts[p["role"]]
            await mafia_dm(context, uid, text, mafia_player_buttons(game, kind, uid))
    game.night_event = asyncio.Event()
    if mafia_night_ready(game):
        game.night_event.set()
    try:
        await asyncio.wait_for(game.night_event.wait(), timeout=MAFIA_NIGHT.total_seconds())
    except asyncio.TimeoutError:
        pass


def mafia_pick(votes):
    if not votes:
        return None
    counts = {}
    for t_id in votes:
        counts[t_id] = counts.get(t_id, 0) + 1
    top = max(counts.values())
    return random.choice([t_id for t_id, c in counts.items() if c == top])


def mafia_resolve_night(game):
    """Считает ночные действия. Возвращает (список погибших uid, множество заблокированных)."""
    blocked = set(game.actions["block"].values())
    for doctor, healed in game.actions["heal"].items():
        if doctor in blocked:
            continue
        game.heal_history.setdefault(doctor, set()).add(healed)
        if healed == doctor:
            game.self_healed.add(doctor)

    def pairs(kind):
        return [(actor, t_id) for actor, t_id in game.actions[kind].items()
                if actor not in blocked and game.players[actor]["alive"] and game.players[t_id]["alive"]]

    healed_targets = {t_id for _, t_id in pairs("heal")}
    guard_map = {t_id: actor for actor, t_id in pairs("guard")}
    dead = []
    game.kill_by = {}

    def attack(target, attacker_role):
        if target is None or target in dead or target in healed_targets:
            return
        guard = guard_map.get(target)
        if guard is not None and game.players[guard]["alive"]:
            game.players[guard]["alive"] = False
            dead.append(guard)
            game.kill_by[guard] = attacker_role
            return
        game.players[target]["alive"] = False
        dead.append(target)
        game.kill_by[target] = attacker_role

    for actor, target in pairs("shoot"):
        attack(target, "commissar")
    for kind in ("kill", "mkill"):
        found = pairs(kind)
        target = mafia_pick([t_id for _, t_id in found])
        if target is None:
            continue
        killer = next(actor for actor, t_id in found if t_id == target)
        attack(target, game.players[killer]["role"])
    return dead, blocked


async def mafia_notify_death(context, game, uid):
    game.last_word.add(uid)
    await mafia_dm(context, uid, "💀 <b>Ты погиб.</b>")


async def mafia_day(context, game, dead, final=False):
    game.phase = "day"
    await mafia_mute_alive(context, game, False)
    game.messages.append(await mafia_send(
        context, game.chat_id,
        f"☀️ <b>ДЕНЬ {game.day}</b>\n\n"
        "Солнце всходит, подсушивая на тротуарах пролитую ночью кровь. "
        "Город просыпается и осторожно смотрит друг на друга.",
        photo_key="day"))
    if not dead:
        death_text = "🌤 Этой ночью обошлось без жертв."
    else:
        blocks = []
        for uid in dead:
            p = game.players[uid]
            victim = f"{MAFIA_ROLES[p['role']][0]} {p.get('link', esc(p['name']))}"
            killer = MAFIA_ROLES[game.kill_by.get(uid, "mirny")][0]
            blocks.append(f"Сегодня был жестоко убит {victim}.\nГоворят, за этим стоит {killer}.")
        death_text = "\n\n".join(blocks)
    game.messages.append(await mafia_send(context, game.chat_id, death_text))
    tail = "" if final else "\n\n💬 Обсуждение 1 минута, затем голосование."
    game.messages.append(await mafia_send(context, game.chat_id, mafia_survivors_text(game) + tail))
    for uid in dead:
        await mafia_notify_death(context, game, uid)
        if uid not in game.muted:
            game.muted.add(uid)
            await mafia_set_mute(context, game.chat_id, uid, True)
    if not final:
        await asyncio.sleep(MAFIA_DAY.total_seconds())


def mafia_vote_text(game):
    lines = []
    for uid, p in sorted(mafia_alive(game).items(), key=lambda kv: game.seat.get(kv[0], 0)):
        if uid in game.votes:
            target = game.votes[uid]
            tname = "пропуск" if target == 0 else game.players[target].get("link", game.players[target]["name"])
            lines.append(f"▫️ {p.get('link', p['name'])} → {tname}")
        else:
            lines.append(f"▫️ {p.get('link', p['name'])} — еще думает")
    return ("🗳 <b>ГОЛОСОВАНИЕ</b>\n\n\n"
            "Кого казнить?\n\n" + "\n".join(lines) +
            "\n\n⏳ На выбор 1 минута")


def mafia_vote_markup(game):
    rows = [[InlineKeyboardButton(p["name"], callback_data=f"mf:vote:{game.id}:{uid}")]
            for uid, p in mafia_alive(game).items()]
    rows.append([InlineKeyboardButton("🤷 Пропустить", callback_data=f"mf:vote:{game.id}:0")])
    return InlineKeyboardMarkup(rows)


async def mafia_vote(context, game):
    game.phase = "vote"
    game.votes = {}
    game.vote_event = asyncio.Event()
    msg_id = await mafia_send(context, game.chat_id, mafia_vote_text(game),
                              mafia_vote_markup(game), photo_key="vote")
    game.messages.append(msg_id)
    game.vote_msg = msg_id
    game.vote_photo = bool(mafia_photo("vote"))
    try:
        await asyncio.wait_for(game.vote_event.wait(), timeout=MAFIA_VOTE.total_seconds())
    except asyncio.TimeoutError:
        pass
    counts = {}
    for voter, target in game.votes.items():
        if target and game.players.get(voter, {}).get("alive") and game.players.get(target, {}).get("alive"):
            counts[target] = counts.get(target, 0) + 1
    if not counts:
        text = "Никто не исключен: все пропустили."
    else:
        top = max(counts.values())
        leaders = [t_id for t_id, c in counts.items() if c == top]
        if len(leaders) > 1:
            text = "Никто не исключен: ничья."
        else:
            victim = leaders[0]
            game.messages.append(await mafia_send(
                context, game.chat_id,
                f"🗳 <b>Итог голосования</b>\n\n\n"
                f"Больше всех голосов: <b>{game.players[victim]['name']}</b> ({top})"))
            await mafia_referendum(context, game, victim)
            return
    game.messages.append(await mafia_send(
        context, game.chat_id,
        f"🗳 <b>Итог голосования</b>\n\n\n{text}\n\n{mafia_survivors_text(game)}"))


def mafia_ref_markup(game):
    yes = sum(1 for v in game.hang_votes.values() if v)
    no = sum(1 for v in game.hang_votes.values() if not v)
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(f"✅ {yes}", callback_data=f"mf:hang:{game.id}:1"),
        InlineKeyboardButton(f"⛔️ {no}", callback_data=f"mf:hang:{game.id}:0"),
    ]])


async def mafia_referendum(context, game, victim):
    """Плашка «Вы действительно хотите повесить…» с ✅ и ⛔️."""
    game.phase = "hang"
    game.hang_votes = {}
    name = game.players[victim].get("link", game.players[victim]["name"])
    text = (f"⚖️ <b>КАЗНЬ</b>\n\n\n"
            f"Вы действительно хотите казнить <b>{name}</b>?\n\n"
            "✅ — да, вешаем\n⛔️ — нет, пощадим\n\n⏳ На выбор 45 секунд")
    game.ref_photo = bool(mafia_photo("hang"))
    game.ref_msg = await mafia_send(context, game.chat_id, text, mafia_ref_markup(game), photo_key="hang")
    game.messages.append(game.ref_msg)
    game.hang_event = asyncio.Event()
    try:
        await asyncio.wait_for(game.hang_event.wait(), timeout=MAFIA_HANG.total_seconds())
    except asyncio.TimeoutError:
        pass
    yes = sum(1 for v in game.hang_votes.values() if v)
    no = sum(1 for v in game.hang_votes.values() if not v)
    results = (f"✅ за казнь: <b>{yes}</b>\n\n"
               f"⛔️ против: <b>{no}</b>")
    if yes > no:
        game.players[victim]["alive"] = False
        await mafia_notify_death(context, game, victim)
        if victim not in game.muted:
            game.muted.add(victim)
            await mafia_set_mute(context, game.chat_id, victim, True)
        role_title = MAFIA_ROLES[game.players[victim]["role"]][0]
        verdict = (f"⚖️ <b>Приговор:</b>\n"
                   f"☠️ Казнь исполнена: {name}\n"
                   f"🎭 Роль казненного: {role_title}")
    else:
        verdict = (f"⚖️ <b>Приговор:</b>\n"
                   f"🕊 Помилование: {name} остается в игре.")
    game.phase = "vote"
    if yes > no:
        verdict_line = f"казнили — {name}, {MAFIA_ROLES[game.players[victim]['role']][0]}"
    else:
        verdict_line = f"помиловали — {name}"
    game.messages.append(await mafia_send(
        context, game.chat_id,
        f"🏛 <b>ТРИБУНАЛ DESTROYCRAFT</b>\n\n"
        f"✅ за казнь: <b>{yes}</b>\n"
        f"⛔️ против: <b>{no}</b>\n\n"
        f"⚖️ Приговор: {verdict_line}",
        photo_key="hang"))


async def mafia_finish(context, game, winner):
    titles = {"town": "Мирные", "mafia": "Мафия", "maniac": "Маньяк", "nobody": "никто"}
    winners = [uid for uid, p in game.players.items() if MAFIA_SIDE.get(p["role"]) == winner]
    others = [uid for uid in game.players if uid not in winners]
    coins = data.setdefault("ds_coins", {})
    wins = data.setdefault("mafia_wins", {})
    for uid in winners:
        coins[str(uid)] = ds_balance(uid) + MAFIA_REWARD
        wins[str(uid)] = int(wins.get(str(uid), 0)) + 1
        log_action(uid, "mafia_win", uid, details=f"игра {game.id}, +{MAFIA_REWARD}")
    save_data()

    def line(uid):
        p = game.players[uid]
        return f"▫️ {p.get('link', esc(p['name']))} — {MAFIA_ROLES[p['role']][0]}"

    seconds = int((now_utc() - game.started_at).total_seconds()) if game.started_at else 0
    duration = f"{seconds // 60} мин. {seconds % 60} сек."
    text = (f"🏁 <b>ИГРА ОКОНЧЕНА</b>\n\n\n"
            f"🏆 Победила <b>{titles[winner]}</b>\n\n"
            "🥇 <b>Победители:</b>\n" + ("\n".join(line(uid) for uid in winners) or "▫️ никто") + "\n\n"
            "👥 <b>Остальные участники:</b>\n" + ("\n".join(line(uid) for uid in others) or "▫️ никого") + "\n\n"
            "\n"
            f"⏱ Игра длилась: {duration}\n"
            f"🎁 Награда: <b>+{MAFIA_REWARD} DS {coins_word(MAFIA_REWARD)}</b> каждому победителю")
    game.messages.append(await mafia_send(context, game.chat_id, text, photo_key="win"))
    games = data.setdefault("mafia_games", {})
    for uid in game.players:
        games[str(uid)] = int(games.get(str(uid), 0)) + 1
        verdict = "победа" if uid in winners else "поражение"
        await mafia_dm(context, uid,
                       f"🏁 Игра окончена! Победила {titles[winner]}.\n"
                       f"Твой результат: {verdict}.")
    data.pop("mafia_active", None)
    save_data()
    for uid in list(game.muted):
        await mafia_set_mute(context, game.chat_id, uid, False)
    game.muted.clear()
    MAFIA_GAMES.pop(game.chat_id, None)
    MAFIA_BY_ID.pop(game.id, None)


async def mafia_loop(context, game):
    try:
        while True:
            await mafia_night(context, game)
            await mafia_track_afk(context, game, ROLE_KINDS)
            dead, blocked = mafia_resolve_night(game)
            for actor, target in game.actions["check"].items():
                if actor not in blocked:
                    checked = game.players[target]
                    shown = "mirny" if checked["role"] == "don" else checked["role"]
                    await mafia_dm(context, actor,
                                   f"🕵️ <b>В ходе проверки оказалось:</b> {esc(checked['name'])} является — "
                                   f"{MAFIA_ROLES[shown][0]}")
            winner = mafia_check_win(game)
            await mafia_day(context, game, dead, final=winner is not None)
            if winner is None:
                await mafia_vote(context, game)
                winner = mafia_check_win(game)
            if winner:
                await mafia_finish(context, game, winner)
                return
            game.day += 1
    except asyncio.CancelledError:
        raise
    except Exception:
        logger.exception("Ошибка в игре мафия")
        MAFIA_GAMES.pop(game.chat_id, None)
        MAFIA_BY_ID.pop(game.id, None)
        try:
            await context.bot.send_message(game.chat_id, "🔔️ Игра мафии остановлена из-за ошибки. Владелец уже видит это в логе.")
        except TelegramError:
            pass


async def mafia_relay_dead(update, context):
    """Погибшие пишут в основной чат через бота: сообщение удаляется и отправляется от бота."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    game = MAFIA_GAMES.get(message.chat.id)
    if game and user.id in game.players and game.players[user.id]["alive"] and game.phase == "night":
        try:
            await message.delete()
        except TelegramError:
            pass
        await mafia_set_mute(context, game.chat_id, user.id, True)
        return
    if not game or user.id not in game.players or game.players[user.id]["alive"]:
        return
    text = (message.text or "").strip()
    allowed = user.id in game.last_word and bool(text)
    game.last_word.discard(user.id)
    try:
        await message.delete()
    except TelegramError:
        pass
    if not allowed:
        return
    await context.bot.send_message(
        game.chat_id,
        f"👻 <b>{esc(game.players[user.id]['name'])}</b>: {esc(text)}",
        parse_mode=ParseMode.HTML, **NO_PREVIEW)


async def gender_command(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    markup = InlineKeyboardMarkup([[
        InlineKeyboardButton("👨 Мужской", callback_data="gn:m"),
        InlineKeyboardButton("👩 Женский", callback_data="gn:f"),
    ]])
    await message.reply_text("Выбери пол для игровых сообщений:", reply_markup=markup)


async def gender_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    value = query.data.split(":")[1]
    if value not in ("m", "f"):
        await query.answer()
        return
    data.setdefault("gender", {})[str(query.from_user.id)] = value
    save_data()
    await query.answer("Сохранено")
    try:
        await query.message.edit_text("✅ Пол сохранен.")
    except TelegramError:
        pass


async def mafia_dm_relay(update, context):
    """Погибший пишет в личку боту — бот отправляет сообщение в игровой чат от своего имени."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or message.chat.type != ChatType.PRIVATE:
        return
    text = (message.text or "").strip()
    if not text or text.startswith("/"):
        return
    for game in list(MAFIA_GAMES.values()):
        player = game.players.get(user.id)
        if player and not player["alive"] and user.id in game.last_word:
            game.last_word.discard(user.id)
            await context.bot.send_message(
                game.chat_id,
                f"🔔 Кто-то из жителей слышал крик {player.get('link', esc(player['name']))} "
                f"перед смертью: {esc(text)}",
                parse_mode=ParseMode.HTML, **NO_PREVIEW)
            await mafia_dm(context, user.id, "✅ Сообщение отправлено в чат.")
            raise ApplicationHandlerStop
    return


async def mafia_start_join(update, context):
    """/start mafia<номер>: игрок нажал «Присоединиться» в чате и попал в бота — сразу добавляем в набор."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        raise ApplicationHandlerStop
    gid = int(re.search(r"mafia(\d+)", message.text or "").group(1))
    game = MAFIA_BY_ID.get(gid)
    if not game or game.phase != "lobby":
        await message.reply_text("🎭 Набор уже закрыт.")
        raise ApplicationHandlerStop
    if not await is_main_member(context, user.id):
        await message.reply_text("🔒 Сначала вступи в основной чат.")
        raise ApplicationHandlerStop
    if str(user.id) not in [str(x) for x in data.get("dm_users", [])]:
        data.setdefault("dm_users", []).append(user.id)
        save_data()
    if user.id not in game.players:
        if len(game.players) >= MAFIA_MAX:
            await message.reply_text("🎭 Игроков уже максимум.")
            raise ApplicationHandlerStop
        game.players[user.id] = {"name": user.full_name, "link": mafia_link(user.id, user.full_name),
                                 "role": None, "alive": True}
        await mafia_refresh_lobby(context, game)
    await message.reply_text(f"✅ Ты в наборе мафии. Сейчас игроков: {len(game.players)}, ожидаем старта.")
    raise ApplicationHandlerStop


async def notify_interrupted_mafia(bot):
    """После перезапуска бота: если игра шла, сообщаем, что она прервана без награды."""
    active = data.pop("mafia_active", None)
    if not active:
        return
    save_data()
    try:
        await bot.send_message(active["chat_id"],
                               "⚠️ Игра мафии прервана перезапуском бота. Награда не начисляется.")
    except TelegramError:
        logger.exception("Не удалось сообщить о прерванной игре мафии")


async def mafia_cancel_command(update, context):
    """/отмена: отменяет набор или уже идущую игру. Может участник игры или владелец."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    game = MAFIA_GAMES.get(message.chat.id)
    if not game:
        await message.reply_text("🎭 Сейчас нет игры.")
        return
    if game.phase == "lobby":
        if user.id not in game.players and not is_owner(user.id):
            await message.reply_text("🎭 Отменить набор может участник этой игры.")
            return
    elif not is_owner(user.id):
        await message.reply_text("🎭 Во время игры отменить может только владелец.")
        return
    data.pop("mafia_active", None)
    save_data()
    game.phase = "closed"
    if game.task and not game.task.done():
        game.task.cancel()
    for uid in list(game.players):
        await mafia_set_mute(context, game.chat_id, uid, False)
    game.muted.clear()
    MAFIA_GAMES.pop(game.chat_id, None)
    MAFIA_BY_ID.pop(game.id, None)
    if game.lobby_msg:
        await mafia_edit_lobby(context, game, text="\n\n\n❌ Игра отменена.",
                               parse_mode=ParseMode.HTML, reply_markup=None)
    await message.reply_text("✅ Игра отменена.")


async def mafia_refresh_names(context, game):
    """Обновляет имена и ссылки участников игры из Telegram."""
    for uid, p in game.players.items():
        try:
            member = await context.bot.get_chat_member(game.chat_id, uid)
            p["name"] = member.user.full_name
            p["link"] = mafia_link(uid, member.user.full_name)
        except TelegramError:
            pass
    if game.phase == "lobby":
        await mafia_refresh_lobby(context, game)


async def mafia_update_command(update, context):
    """/обновить: обновляет имена участников текущей игры мафии."""
    message = update.effective_message
    game = MAFIA_GAMES.get(message.chat.id)
    if not game:
        await message.reply_text("🎭 Сейчас нет игры.")
        return
    await mafia_refresh_names(context, game)
    await message.reply_text("✅ Имена участников обновлены.")


async def mafia_handle_chat_mute(context, uid):
    """Ручной мут игрока: бот сам снимает его, игрок остается в игре. Возвращает True, если это игрок игры."""
    if uid in MAFIA_EXPECT_MUTE:
        MAFIA_EXPECT_MUTE.discard(uid)
        return True
    for game in list(MAFIA_GAMES.values()):
        if uid not in game.players:
            continue
        if game.phase == "night" and game.players[uid]["alive"]:
            await mafia_set_mute(context, game.chat_id, uid, True)
        else:
            await mafia_set_mute(context, game.chat_id, uid, False)
        return True
    return False


async def mafia_top_command(update, context):
    """/топмафии: топ по победам в мафии."""
    message = update.effective_message
    if not message:
        return
    ranking = sorted(((int(u), int(v)) for u, v in data.get("mafia_wins", {}).items() if int(v) > 0
                      and not is_hidden(u)), key=lambda item: (-item[1], item[0]))[:10]
    if not ranking:
        await message.reply_text("🎭 Побед в мафии пока нет.")
        return
    medals = ["🥇", "🥈", "🥉"]
    lines = [f"{medals[i] if i < 3 else f'{i + 1}.'} {saved_user_link(u)} — <b>{v}</b>"
             for i, (u, v) in enumerate(ranking)]
    await message.reply_text("🎭 <b>Топ мафии</b>\n\n\n" + "\n".join(lines),
                             parse_mode=ParseMode.HTML, **NO_PREVIEW)


async def drop_old_keyboard(update, context):
    """Если игрок пишет боту в личку, убираем у него старую нижнюю клавиатуру (сообщение сразу удаляется)."""
    user = update.effective_user
    msg = update.effective_message
    if not user or not msg or user.is_bot or msg.chat.type != ChatType.PRIVATE:
        return
    gone = data.setdefault("keyboard_gone", [])
    if user.id in gone:
        return
    try:
        sent = await context.bot.send_message(msg.chat.id, "⌨️", reply_markup=ReplyKeyboardRemove())
        await context.bot.delete_message(msg.chat.id, sent.message_id)
        gone.append(user.id)
        save_data()
    except TelegramError:
        pass


async def log_incoming(update, context):
    """Диагностика: пишет в лог каждое входящее сообщение (чат, пользователь, текст)."""
    msg = update.effective_message
    if msg:
        logger.info("Входящее: chat=%s user=%s text=%r", msg.chat.id,
                    update.effective_user.id if update.effective_user else None, (msg.text or "")[:60])


def register_all_handlers(application):
    only_messages = filters.UpdateType.MESSAGE  # без edited_message: правка не должна запускать команды/жалобы
    staff_chats = filters.Chat(chat_id=[MAIN_CHAT_ID, ADMIN_CHAT_ID])
    admin_chat = filters.Chat(chat_id=ADMIN_CHAT_ID)
    private = filters.ChatType.PRIVATE

    # Жалобы, кнопки, запросы на вступление
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID)
        & (filters.Regex(r"(?i)^#жалоба") | filters.CaptionRegex(r"(?i)^#жалоба")),
        handle_complaint,
    ), group=0)
    application.add_handler(CallbackQueryHandler(
        moderation_callback, pattern=r"^(warn|remove_warning|mute|mutetime|unmute|ban|unban|back):"), group=0)
    application.add_handler(CallbackQueryHandler(application_callback, pattern=r"^app:"), group=0)
    application.add_handler(ChatJoinRequestHandler(join_request_handler, chat_id=MAIN_CHAT_ID), group=0)
    application.add_handler(ChatMemberHandler(on_member_change, ChatMemberHandler.CHAT_MEMBER), group=0)
    application.add_handler(CallbackQueryHandler(chest_callback, pattern=r"^ch:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Dice.DICE, dice_handler), group=3)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(кубик|dice)(?:@\w+)?(?:\s|$)"),
        dice_command), group=0)
    application.add_handler(CallbackQueryHandler(dice_callback, pattern=r"^dc:"), group=0)
    application.add_handler(CallbackQueryHandler(duel_callback, pattern=r"^du:"), group=0)
    application.add_handler(CallbackQueryHandler(guide_callback, pattern=r"^gd:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(likegive|лайки)(?:@\w+)?(?:\s|$)"),
        likegive_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(toplikes|топлайков)(?:@\w+)?(?:\s|$)"),
        toplikes_command), group=0)
    application.add_handler(CallbackQueryHandler(leaf_callback, pattern=r"^lf:"), group=0)
    application.add_handler(CallbackQueryHandler(mafia_callback, pattern=r"^mf:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(мафия|mafia)(?:@\w+)?(?:\s|$)"),
        mafia_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(отмена|mafiacancel)(?:@\w+)?(?:\s|$)"),
        mafia_cancel_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(обновить|update)(?:@\w+)?(?:\s|$)"),
        mafia_update_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(топмафии|mafiatop)(?:@\w+)?(?:\s|$)"),
        mafia_top_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.TEXT & ~filters.COMMAND,
        mafia_relay_dead), group=5)
    application.add_handler(MessageHandler(
        only_messages & private & filters.Regex(r"(?i)^/(пол|gender)(?:@\w+)?(?:\s|$)"), gender_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & private & filters.TEXT & ~filters.COMMAND, mafia_dm_relay), group=-2)
    application.add_handler(MessageHandler(
        only_messages & private & filters.Regex(r"(?i)^/start\s+mafia\d+\b"), mafia_start_join), group=-1)
    application.add_handler(CallbackQueryHandler(gender_callback, pattern=r"^gn:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(передать|give)(?:@\w+)?(?:\s|$)"),
        transfer_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(лотерея|lottery)(?:@\w+)?(?:\s|$)"),
        lottery_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(банк|bank)(?:@\w+)?(?:\s|$)"),
        bank_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(дуэль|duel|кдуэль)(?:@\w+)?(?:\s|$)"),
        duel_command), group=0)
    application.add_handler(CallbackQueryHandler(menu_callback, pattern=r"^mn:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & private & filters.Regex(r"(?i)^/start\s+promo\b"), start_promo_command), group=-1)

    application.add_handler(MessageHandler(
        only_messages & private & filters.TEXT & ~filters.COMMAND, menu_text_first), group=-1)

    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(топкубик|diceweek)(?:@\w+)?(?:\s|$)"),
        dice_top_command), group=0)
    application.add_handler(CallbackQueryHandler(quiz_callback, pattern=r"^qz:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=[MAIN_CHAT_ID, ADMIN_CHAT_ID])
        & filters.Regex(r"(?i)^/(баланс|balance)(?:@\w+)?(?:\s|$)"),
        balance_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(богачи|rich)(?:@\w+)?(?:\s|$)"),
        coins_top_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(шоп|shop)(?:@\w+)?(?:\s|$)"),
        shop_public_command), group=0)
    application.add_handler(CallbackQueryHandler(shop_buy_callback, pattern=r"^shop:buy:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & (filters.Chat(chat_id=[MAIN_CHAT_ID, ADMIN_CHAT_ID])
                         | (filters.ChatType.PRIVATE & filters.User(user_id=OWNER_ID)))
        & filters.Regex(r"(?i)^/(мустат|myprofile|mystat)(?:@\w+)?(?:\s|$)"), my_profile_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=[MAIN_CHAT_ID, ADMIN_CHAT_ID])
        & filters.Regex(r"(?i)^/(стат|profile|stat)(?:@\w+)?(?:\s|$)"), profile_command), group=0)
    application.add_handler(CallbackQueryHandler(profile_callback, pattern=r"^pf:"), group=0)
    application.add_handler(CallbackQueryHandler(like_callback, pattern=r"^(lk|dl):"), group=0)
    application.add_handler(CallbackQueryHandler(purchases_callback, pattern=r"^pu:"), group=0)
    application.add_handler(CallbackQueryHandler(title_callback, pattern=r"^tt:"), group=0)
    application.add_handler(CallbackQueryHandler(shop_page_callback, pattern=r"^sp:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/(гайд|guide|help|commands)(?:@\w+)?(?:\s|$)"),
        public_help_command), group=0)
    application.add_handler(CallbackQueryHandler(shop_admin_callback, pattern=r"^sh:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & ~filters.StatusUpdate.ALL, count_message), group=2)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID), profile_input), group=1)

    ROUTES["/викторина"] = quiz_command  # регистрируем здесь: функция объявлена ниже ROUTES
    ROUTES["/выдатькоины"] = grant_coins_command
    ROUTES["/шопс"] = shop_admin_command
    ROUTES["/скрыть"] = hide_command
    ROUTES["/пользователи"] = users_count_command
    ROUTES["/эмодзисоздать"] = emoji_set_create
    ROUTES["/рассылка"] = broadcast_command
    ROUTES["/блокзаработка"] = earn_block_command
    ROUTES["/промо"] = promo_command
    ROUTES["/сундучки"] = chest_command
    ROUTES["/эмодзинабор"] = emoji_set_command
    ROUTES["/открыть"] = hide_command
    # Все русские команды — через один роутер
    routes_regex = r"(?i)^/(?:" + "|".join(re.escape(name[1:]) for name in ROUTES) + r")(?:@\w+)?(?:\s|$)"
    application.add_handler(MessageHandler(
        only_messages & staff_chats & filters.TEXT & filters.Regex(routes_regex), command_router), group=0)

    # Владелец может выполнять команды в личке с ботом (ответы видит только он)
    application.add_handler(MessageHandler(
        only_messages & private & filters.User(user_id=OWNER_ID) & filters.TEXT & filters.Regex(routes_regex),
        command_router), group=0)

    # Меню шаблона (кнопки) и ввод владельца; остальные личные сообщения — как раньше
    application.add_handler(CallbackQueryHandler(template_callback, pattern=r"^tpl:"), group=0)
    application.add_handler(CallbackQueryHandler(log_callback, pattern=r"^log:"), group=0)
    application.add_handler(CallbackQueryHandler(start_log_callback, pattern=r"^st:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & private & filters.User(user_id=OWNER_ID) & filters.TEXT & ~filters.COMMAND,
        owner_private_text), group=0)
    application.add_handler(MessageHandler(
        only_messages & private & filters.User(user_id=OWNER_ID) & filters.PHOTO, owner_private_photo), group=0)

    # Личные сообщения: заявки и диалог
    application.add_handler(CommandHandler("start", start, filters=private & only_messages), group=0)
    application.add_handler(MessageHandler(only_messages & private & filters.PHOTO, private_photo), group=0)
    application.add_handler(MessageHandler(only_messages & private & filters.TEXT & ~filters.COMMAND, private_text), group=0)
    application.add_handler(MessageHandler(
        only_messages & private & ~filters.COMMAND & ~filters.TEXT & ~filters.PHOTO, other_private_message), group=0)

    # Админ-чат: ответы пользователю
    application.add_handler(MessageHandler(
        only_messages & admin_chat & filters.REPLY & ~filters.COMMAND & ~filters.StatusUpdate.ALL,
        admin_reply_relay), group=0)

    application.add_handler(MessageHandler(filters.ALL, remember_message_users), group=1)
    application.add_error_handler(error_handler)


def main():
    if not BOT_TOKEN:
        raise RuntimeError("Не найдена переменная окружения BOT_TOKEN.")
    if not OWNER_ID:
        raise RuntimeError("Не найдена или некорректна переменная окружения OWNER_ID.")
    if not ADMIN_CHAT_ID or not MAIN_CHAT_ID:
        raise RuntimeError("Не заданы корректные ADMIN_CHAT_ID и MAIN_CHAT_ID.")

    # Храним в pickle только user_data/chat_data (шаги заявки переживают рестарт).
    # bot_data не храним: рабочие данные живут в data.json.
    persistence = PicklePersistence(
        filepath=str(DATA_FILE.with_name("persistence.pkl")),
        store_data=PersistenceInput(bot_data=False, callback_data=False),
    )
    application = (
        Application.builder()
        .bot(HtmlBot(token=BOT_TOKEN))
        .persistence(persistence)
        .post_init(_on_startup)
        .post_shutdown(_on_shutdown)
        .build()
    )
    application.add_handler(MessageHandler(filters.ALL, log_incoming), group=-10)
    application.add_handler(MessageHandler(filters.ALL, drop_old_keyboard), group=-9)
    register_all_handlers(application)

    cleanup_expired()
    logger.info("Единый бот заявок и модерации запущен.")
    application.run_polling(allowed_updates=Update.ALL_TYPES, bootstrap_retries=10)


if __name__ == "__main__":
    main()
