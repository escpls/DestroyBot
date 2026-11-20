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
    "heart": "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",
    "gift": "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",
    "name_tag": "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",
    "pencil": "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",
    "crown": "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",
    "fox": "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",
    "sprout": "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",
    "autumn_leaves": "iVBORw0KGgoAAAANSUhEUgAAAGQAAABkCAYAAABw4pVUAAAqm0lEQVR42u28W4yl2XXf91tr7+/7zq3uVX2b7um5z3A4Q4keirFISkNRlqxIFsJYIpAIRpAgCRwgCpKHAA6Qh0CPechDAgOKEyOAc4ENMwYSy4liyTI1kUxSJEeUhmSTM9PdMz19r+66nKpz+S57r5WHr4aRnSDhrSkJqD/Q6DpVB+ey117X/39vOMUpTnGKU5ziFKc4xSlOcYpTnOIUpzjFKU5xiu8B8uf8Mwrgf+Kxn5r0FH8uPUT/xV98BmT35P1n/y+f4ymQ42eQwxqtGkJnSDEhVAfowghlSdk4IQt5nlnIlHYDMpDOgH+29xb/8+Y1PxSDvMrlwYz220ZZ7iRdbR6UninCnFAM0dYJwQlFhRQgjRHDgFHuWA3CigZWzNnEWKPgzHHNZXUqD0xT4veScy06h/WAOzZkPh6QJvly89qNGy1g38u6vMqrAeA1Xss/rJAYfwj2CA1ZOkwSJo9vPlBriAdHlHFAVexQYMRBTYiRQiDUES2VKjhrEtiKkY0Y2CFzbt6yUWa2fuQxVu8eUe4v2Ywl77TOUdtQVM6iqLFFogvp2P8iF6XjbHqd19P/x4LKZ0Cv84ruPPO6LrvL0uQs5a1v6f2z8Iqe9yIEr0LwMzdudJ/tPfHPnYfoK7wSnrr4ejzcROcNOtpFPRFTpiAyMWHVMiOEjbJgJ2diWRLEMBcGCo+J8nIRWLWO1QDbzz1J+ws/zvInzpL+i/+FM//7W4hG/nDW8a1k7Bt8TZRbTWZRGIfjgkUXyJslqb1/OT9gbABDhj5h4re5HUZnr8ZBR8iOaCJGI6QRGjIBoKuxboVcLcgjJZ9Zudjs3nq6e43X0p8Lg3yGz4RdvlSUH7oRAOYNOq8J5T7BMuWkoMqwVUYuGKzGwGVPPFEoRRCSZTqJjELgcYEP5YbRpXN0P/+THHxwA118k7XBAq4m8n/1BpMOrh8nbraZg874gyxcVecow4OQmcoqrQxohyU5HuCwRaHqnT2QtIFoTVwcEEdGUUdGwRhIJBpocCQkLAjNYaJWpRlvsaianZYHo/QaN5ofZCgLj8LrVi8eVbG6GesSXbZotUuYLAhtYjjKjGPJJCrnYuByFTgjzuMrJRdbWAnKsCpZKSKrntkZFGz+lU9y/69/iunkHmt3vsJWrOHOjHJlRPvVfeJxYpGMJhvRYVdLjqxDNFIXQ1I+xrXG8wDrSrQrl7qIizAs0YOGKDWDAQyASRE5R2azFFbHMFChmDvlNFOuKIUH1KFbjBd2GKO8tDwjN5jmP5M55FVejc3F14quvFUeGjFN0ZUphRilOoOqYjNXbCmsFoEfLQtequeMP/6jrP6bLzH4R19i+Lm7iELODeG585T/2qscXBLC3u9y/sERYXuHumvRZo6cC4Sn1+ju3WMtKLjRAk+kxL4LUYwDMWLrFAPDeQgq/W6eOCJO2Cgp68SIwEiVbc98qAhsqVPNjfXslE+NsccH3Pn8Id+0zD1boj7nsFvda29umL56cBm4kV6D9GfFQ+TneKZKO7eqerQo9DrD0DFayYxLZyNHzsTIBZSnVXm+LHl+EPhYTnz4A4+z8zd+Fp884PzzA8rnNon3F2y9cJ7wr/8I3fHbbBxeZ00VY4i0Ad65T5UEj45mx752QClC0RkDh4ULM1EIzp4HFrlCUgPiqBnRjLh0SisYaMWKOpsinAnCU+J8HOGlUnj5uVU++nMXeOkXL/Kyt6x94ZhlMELO1JLJ1iDjcW3TQbRuuRou8gJ3uWt/6h7yGV4sdneuFIyI3X1KX2NUJsbWMSEwqQJrCpsKF4NyoQqsY6w8uU36T/9lDie32dw7wI/m6NkS/WvPMEuG3nyDtc6R7RUyghNJh0cUnkBL9LhBLgzogsBJvC+yMxRnXRXPwnqZORwYUcdoof0OdkccRI3AkqHD2qRgMzjnWuHCduTcLz/O4AOb5BK6vRn+1oyua5nEiscQ9pqWhQVMOpqN0V56uLmZRvu3yld51b+fZB+/f8+gfGPrfrkujOpDhhWMJXHWhPVYsKaBc6JsB2EzwHYRWVNn8tga6//xp3m4ecR6PQcp8IVDWoAIxXSOZoEQsHmNLCIalVzPUYkQBR9HZFKgaxG50xCDYCJs4TyZjG0XFl0mpI5FKJhJZtn1X1oyxBgoAmxXkQ/MGi4UgWc2A0/+9CbV0BgdLUiHDfG4xq7OqULgfG4ZEJgrROnYb5w7NudgqPvtaJXF7Ej9GZ4JV7nafQ/9z/dnkBd5sdjfvFJVcW9Qt2zTsN4UbFTCk4WwHZTNIvCMOmdUGEqgioFIYvjjT2NPAg/uU6wNMU9onZFSyAoyKrFpSzRBjjLBE3nUUZmi6yXdJOLmyFiRCwPsRkMxFFqBdXXUhQbHMQYamavwsA4cutGhxKgMojDCueTw0x9d4/K5EZMLJTpyilkL8w7NBndb7HbHpFDOdDDCwQIryZhKx9ACd1JH3RoPB5fvWnljJ73C+bBkI13hSvfdVGHfTw6Rx4lVV87iyBmkmi2UrapiOxpnC2G7DGyPlceysAMUo0ARA4UZ1Ycfwy63TO4/IC4zmhOp7ggYIoqY4Z2hZYBpjUyGyGSAnx/TrVXgQnDQMmIdpC/tU5QBz07XRzCCBFpRWhHKEMmq5BioVBkFYTXASjbObxR88JfPsPbUmFgKEgOyWuGNEdZK/Fsz0ptzuiiYOeqwFCEDhQRaNRpVgkSSQzsrFq7N0Ie08hxb4QbT9Mg95BVeidXzrwe9Q4gVlShrQdmiYwvhUhm5kI3tv/oyW+cHFP/rNcb350ilmATKYUCWLdlA2prsECPQgcxrmHXEUcSOOqo2YM9s0aWGaIYkAzPcHUvg786IScEFVSg9gGSyOjsCKQlLjJE6Q3c6FaIIQ4TKlDMrgRUX4rRDlx06LvBxhPOB9sYCrswJphQmDIHgzrYZUaA1Rw0qM6YlSFlTV4kwnDxoZtVW0+2ZfIYXy89ypX2kBtlhqndrQjmgaOYMLbAZhG2BMzHwAs7ZlQHjj19m8OyQ8iNbtL97k/K3bzO40VAMI22XUM9kF4iKtR3F7pLYZnJjiIG8M0N/9Dxt7gjLFg+hHxgm0KjIa3cI//AeMZa4A0EpVSg0YIAKjMRpHM4inFdnqU5CUBEKF85fHDCsFH1Qo0EhKN3r+8Q3jojfnOMLo4sQszB0pVAo1TljTgrCOY88HpxDMaousxhkjm3J0WRlj4ONje76wYH3e+3/P3R9zwZZ0knTEVKiqCKDQhioMQrKWqGMUsfgg+conl6hXe4zih3Fp7ZJz63Q/rP75HOQLFPEgIkiuV89Sxl38Chw64gwHpIujfH5HCkLzAyrHQmO3Jjhf/8eRSxgpJieVFCAowQRShOG2SjcwIVkxkCcDGg2yqisv9cgnztAdgrsXIV9+Qj5zV10lrFRhAGIGWJGUEUcAkIZwcSREPCcKB3OubCVA5qFHA7Jcf2AJTv5kYYsB/lZ6jAwNBpFbZSlU0mgEqFSJWig+PHLuBpjhRwjfrhELg+wl18g1Rk5mpNq7WdIXUKj4Kp4l/scst8RP/k4S+8ICWxRI7OWonZCqeS/d5u4n2G1wKqIKFhwxBJjIGmBmUMS3JQiQ2FCMnDLqPa7ffRug1yZkceBUCmy3xEE8jAi5ngAVIkKcvKzq2AqSGuUrVGUgTWDGcJ+07GrSgiZLibS5JkHytVHaJCPQAzP3A/ttJ/QFg2FCAN3qiAUQQkmUC9QarSuoYZQlXQaYNZCUSBrE/JRTdG0aLa+Q5+UmCb05gwdDUhbE3jvLrpISHI0OVJF2r97A/3WAl0psVGJBPAShsOS7sUf45vzfbZvvcf2osFyxLrMGNhywV0gOdkMkmCDSI6O10ZeJEIpZAeyowrigkQhRiFGhSAwDNgwwgdGhHMl4+jIl6dMvnBEFZR7lvlqFzkMM5bD9v/JB/1ADTK5fDkcdjd0NROyE9UJBIoQqdwpPeNB4Qs30Z87QzpuGbhjMVAMC5oQYP8YuXbAuGvxc2Osdjx7X1UdtnBnSXhyFbt+m2reQFA8BNiMpN95gH7+iMEwkiYFPnKKQpEnnuf6L3+aN398zGQxp/3GPvc+90V2vnWN1cZBQPTEw7tEmGd82UJjZAIUjutJODsJ9l4G1B1JjmVBk/fdRZPRaYeXjn54HTtTUdQw+coxF6Iwap1ddYalUTXO4lEaRA7qOlQLQicMRChRRsAKxirC2AwJQvPWAdWNI+xCiXUJsmN7x8g7hwzuHhNThnGBbw1pBXzZ9+O2u0QR5PExedlSlAWeMrhhf3wMn9ujXKvIKxHGRnn2PAef/jTf+PlnabnCS3tvc06E/PI28x99lYPdX+BGa2R3gjvRncI6dNAx+NzXmfz6b7KmkWSCBO0Nd9ITyFhJs0xwBzX6DNV7GAJ8fYamW+ivPkF9pkJXI2vTliDCNsIkKcdd/s7X+bs2yKu8Grr0mvqI0LUM647VYWAH4ZI6Z1VZNUFDIM9b0jf3Cc9cpLu3JIojBzXF7QMKCVhVQmvw3hTdGWGdQXQ4aIhPr9IWwMzxnPHg+HHGv7RHOFfhP7YKqwN0/SO89fN/iXvr73Gx+zxnF8eICa057N1mXOyyurHOeTICmENQ8MWcMBpBlakdQqFINlwEEfoCAWBuBBGYhH46IEAGaUEwbDVihwn5O7cIyXF3RiKEnNkoClYkM9XlIzTIkNthuYH4HVSGDIqK1eBsiLEWlJWgDN7n0KNgX9pl9KlzeJMIYuTVAVzeoLl9RJUdw7H7NWHp8PiEfHdOOGgJrwzoGiMOIhYEc0WrjPzKE1jXUQy3WLz0Kd67UFIs/gkfbipEhLbrKFUBw4nkWJHaJUoGFVQV6ozsHRBSSfPmPbR1ZCSQFcneV2oi/ZeIgheKDCJWKV4oGvqJseeEzxMyN/ztBb7sMAlEAdPAqOvnaqUOUZaPyCCHF69qNqQYENrMsBTGpbBiwmoZmUSoslEmoygC+rV99HZN2ojYvEPc8cdWyPs1ea9B9OTL31xQblcsr00JKxV5dQhNIqvgZtBlQHAR4rkPc+fFV9gL73Lx6AYTDbR1h3VOYYbFAlFBBgUeBHLuc5CDdgbHC4KBDCZ0d/aIqaOoJnhQvEm9B0ifT+x9In2Z0KX3xikF36yQrYq8rNBlxu8uUQMxhwTiTlSoOqcIfOdJ/bsdncjZo/PF0GbFzBlH5UIB56LyxJmCj6TMORMmVaRSYaBCPOio1gv8w5tYY0Qc31sQ9mu06VAFLwKuDg9awl5D+OAO3fYQP1riKSHZEQTvMuXa0+x99Ke5nz7Pc+mAGEs6jciiRudLQpfRk55BJxO6MuJmaDbUwdsGSb23oAPS8y9wsHTywSGjpiFEgVL7v7sgGST1hpTsiPUJ3hf9Y68U1kt8HMnTDjXozMGcvQTX1ZhJxfRBw8EjMcjGzqzSAUUJY2s5Pyg5kzLPfuoiL/zSBwgP5gyOWyKK0C9CmLXIq2ex/WOK28fofkOwPkGKKyL0I5X7S/QgoRcq8IRifc0PIP0OD899grsre2zaMaUD4niX8EVHiWPmSNOiDLCNNbICIWKxwLsOlg1BFJcA7RHFTmbw8x9m8aMf4KAV/PCIql0QzNGgSNF75f+9x6XvRQBrnTCIcGFAmhRwb4lmJ3VGTs6+wzVxjkeJg7uZvUdikGcvURU1RZ2YeObsoGDLE4+f3+TJf+fTHH7qMm2aUnxjn0IVigCHHbFtsLNC3m0pg2IiiPalrjgIAtfmhErJH1ol40iMiDuSDM2JMDlL/fxLHMkukzCik4hYC4dzymwggosjs0zYukQzNGJOfa2rkPcPqZoW5aSXSMDhlDi9xepWx+inXqZ59RMcXjxHWymdGWHWELuOiKHmiICb96WzGYwi8vImqTHk+gztMl3nWHIeKFwVZebGwX3jwaPJIfv4iqDZCQXknGlEWN47wI/vEVaWjH7mDPz+TfxBQkXILqS/e5ti9TLLp4eEu0tC2c+MJCeQgB91yGGL/Pg2FiOh63A5KS0N/HBJeekZ7pQ1w5RwjXhR0hxlqoM5ZRVpywhdRvKQenuLZd6jknAixptRdg2CYF1GvC+DNQS8Ndo7u4RuyuraDqu/sEPzCz/F4sBY3phRXNtFr++i7+4S33tIdVRDIaj2nIyvl3BnQWgyZMjmtCfj/+SQ4ncxftfv1iBRex4iOGpC7pwuROqbx9h//U/ZvHIDWQH5yTO9B5qRcVKC7r9/j9GR024N+pwh9CP2LsPdGjHg0hhcEVOYJ2y3RW8tKKZKurCDc5+RA5YQawnLJRVGWjTovEXvztHtC9TaIV7ShiGdCXn/iOiKi+A4ngx1QzUgMRC21+iGa1i3xPevUd17g63Z1zhzaZeVVweUv/oh+NWPUZsjQZEQIEb0iQlZAnJnQQg9oda50gosTajJtFl4ZLMsH92/aH7mlr8/utSMp34+1Pzjdxn+4V3Kj22glwZ0paBT7/PjesT3a+xvXWf4Hz5JEwLV7hxJIMsWbi6Q80NyGeDuHI47Qm0U5liXCM+9wPF2omrmxGJIi6OLY6KCro6x44bQNMhok/biBnSzPjRJiR3eY5g7ZFBiGnCz/jWTYamv3uzhEub7vUeWgeyOtwna+0Q3iheeZv7fvM7kqEEnA1wc3yywp7doDxp0d0kcBOplR52NhQsLy9RlQRLFaR/h6CQFcqF0XSIAZZ3xIOxpxPcbyt+4z3gcCCZkrJ8JBUfXSnivRv/LaxT/7lOkLFSW8cb62v9chV8/opx1EISUpO/igsCzF2jbe4znB1TFKqEsSIfT3mBFgaxCe+OYwTNPUgfFQkkg4N2cSIdZoLl9RDnLyFGNHPayJF8d4Kslor1qxYcB8Z7rgD5f6MtPsvjbb6Ff3CWsDzFxKA35iXOkx8f4//Ae1TD04arNzNXZx9kTofZE0hWc40dokGFBTomu67npIgBmTJsOtcAkODqFUkCjoKVQeMYkIOuQrzXE/+4G9ktn6WJAd2t0JeKFwrTBssOgXxhvMmF9Qn1hiMzuUnUJW+5RaqBMHY5CFDhcEnVC89gmi+N7lLcfIm/vM7z1gHI6Q446NAZ8u8J2xvjlDboI2mTk5L1YOiEb5gErC3TZEF+8QPOPb8Dfe5PR2pAshgcIHz2LvbxN+sJthuKEKmLX52QVZjlw5B1TNZaqdEG+c279uzbIQwY2nuIDSJ5JFnGFnITWoHUjqdB3SQKVwIc3aL51THXQQEnv6tdr9O/cI/zsCt1xRxgU+CL1BNGqYlWEBHpvjl46SzOoiQ/nEIZIMHJdo7Ek4Hhr5AczyqVgn/0Ntt/bp3qY0GzkCxPs6TN02wN8UiIVhCLA+33J0Qz2lwQE2gSNoYMEVY2/fJHF2w3d3/wmK6tDfKPAS0E+skP+1OMs7hwTVwry2hCuPCB2QsrG3J2FK0tzlqWylOPvNGB9DwZ5jE4OAW1wUbIobidVRD91OOkvBAkOGfTGkrA8YZVd0dKhMDwlbGGIBmy7wC5NUOtDnIig3ks47ewKfrTfa7HI+KIhqBDbhN0+wK8eUr41RR8uqbZH8NIZms2OOInwoXN0w5PdvuywxpCm6wsTAy8rbA3kcI6q46Uiewvk6S3sZkPzN77IWhuQzUAKjn7kDN1ffoJ63hFGkW7u6Ff30KWxEOMhzntReRiMe1GZR2WRerbwEXLq62CHiHT9TMcMiUIQIbgQACn6+C8ReFAjpaIjoO0dR0qQn9pkuaLwpTnVN2foXk3+ybOwUiJHLdxpCJMBdm6ILw+JInjbke9P0UXCbxwR3jyiSJCf3KL9xBP4c9vk9QEs5thbD4h/+B7VxVXy5gomjr+vXOw/ONp0UEYYVfhR3XfxL5+hkxHNr73OZJFhe0iuhPAjO+SPnqf5+kMG5nRXp5R/sEuonYVllubclsi1EDjoah5EZekddS54dCKHGTfyTsCPQFBK+u9TKgyiMozSz7CCEIahTyRVHyK640Sp4MuO8MlzLD9xhvbvfovxzSXczfDHC4rfP8ReWSP9yAZptUS3NmCYKMjkI0eu7BGvPKRYtH2/8uGz1B97ijQ0tEnIsqF4OEck4k9v4RdW6O4eEW7tI2tDUlH0JW82MMfdkNZ6+tggXNyiu5lo/+YXGU0zsjHAd0r85U2WT63hn7vJcNHBcaK6OkU7p26N1p1GYS8buxkWUVlkoVkKafQoc8gSZJjQ1ogirEVjIpGxwmpUVoaRUo3yqRX08TVs1mLTJdxfEFLuK671kvyrn2T3995g/WFNXJwsxkRpp0L8R3tU/8cevuL4f/IRZnenlF+9S7h+TLw7g3MrpJ95ljQAv35AdecB4fI6edk3fGgvhGDZoqrI45vY3gz2FhTDiA2LnkBzR9qeg/HWiZc2SG8uaP/zN1iVQF4v8NVI3qroHizRP3rYn+TCyYuMmNNk5xjjPsI+zrtROFSYqXM4nzFfHdO28RF6yA6XNXMDj5Rk1oChOINCWa2EYU4Uf/Ey+q98gFYy9vl30asHjBfWl2PeIn/9FQ7377Dym2+xcgze5H54uFZStBlCJJ8ryVuROD2m+N/2KG4sCE9NyJ9+mnxhBUuZUqF7Yp326h7lfo19YAeXAm1bsivBQXLG2u6ECxd4OO9ZyUGBD0LPQmZDgmG5Iz6z3vdDnfbGiIK8M6NIuW9kM1hyTJSuHwzzMASuBbhryk2HI4XpoOBovMLy4SbZ67MJ7j8agzTcEAypnNgKVVCKALEIRDfCK5fwf/tV5qsR/sGXGX3uPYaLlk4VaRPFzzzJ7CfPsvjb/ydn9jv8foveqdHHxuS/sEP73Cb1xQq2hXw4p3rzkKrNpE9fJm0NIAg6WxLNMRHCQMnPbZDePSR89Q584CxdpWiXe5IpO9ImZNmhEUwFnSeYd0ipsDrA3PCo+KxFnlojfvwczW/cYlgJeZExpM852XFzDCG7kaNgDkuFIxOmkjl2mGnJvIR24OTjAss31B+Vh8jiLFpkVI0iFER1YiEM1CnPr1D+W/8Sx5vr+D/4Z4x/922GLmQN6LJDzla0v/QCyy9+g9WHDWqCqsMvXmL6medoLgxgOie+9ZDq9UPCw5Zw2KLqhI+eox4VxAdztIAcTojvNqMG+uQa+bBF39kjnp/0XHtthLZD2owbWNFTvmY14gKdIfMaHVa9l+YOv75L9Vef4+i1e8S9Dh0L2U6WU6XveUSh7A1EFqomMxwKq4MKWyxYdkqSXdL8KXxYYg3h0RjkPwP57bSlud4LphQhIyoMioJJdAavXsQujeAPvkH5uW8xmme6pIQiIIUj//7LHLb7DH73LsP9DlYE+2sXWbywSfeVG6y9eYimjJRKLpX0sEOHkB8foJ99m9EvPsniQ2fI9xd9cWCCesbEsUVCRxFZVWzZEeYtqCBBsM4QE0i57/rLElk2uDm+yAQHm5TIhXW69Q2W84q8vULee0iIxcnrOOaOd45WjlEQVwV/bMCFZyacXQ8svrDP7329phsLtpzgQ8VlD+dRGQSA7T3mt6ByNAjDIAwDDLYHyGND8u4DwhffZHjckpOgbvi8Rf+NF5h+4jL173yTuNdAJ8g4ku42DL56nZX9hiY5nQNLh6UR9xLhXIl/cpvEnPA/X2O0n1h84jG6h0dU7qQQ0dT3FbQOZoQiYAp+0CCFIt6PV8LOCCsU6Yx83PRypGT4+gjbWWd5bY7/+h9TfWmXdQ8QAyk7RHBVZD0gf+ksOZ5w8E9OsNXAMDkrD5e8cXPO7mZBTELz/nLd5yzP9+ca/ZH1IWOAikKc7UrZLoTxE5N+F732DuW1KSEEMMOOE+WHt1l85nmOP3+VyZV7FJdWSFePCddqytjiajQLx/Y6dGrE2hDpJ8u8tSS8Oad7uiKbI79zndG0pv70sywfzhgsGnI25P0xe5sxQAYFTAr8qMFViSnRvj2FYcRdsEawZeqT+pUp+rkrDK/OKDqDKmIjxbRXoCBAAfKvXqD7+A6+OyMKxNWKdHtOWLbIrYa3Z0q37Uit2JkZRoldWFlJn71/5dE0hr8G/pl9/BY4RpXgQqnsPLPC6OKYLCDf2qM4aIFegSHPr1F/5jmO/9aX2bE5uGDjiA+BsZCvN8hBR9H23blH8IFioT8B5a3Al6eEjz1BZ8JgvSD/0R2q44buV16iDlDOGqRO/W6XgJRg2ZDyRJQQA9Ik2v/xTVbrE35l7nBo0Fe/SBX7Gd0QTPp/uEFxIgv62DrpR1bRhzUybdEiIm1NaDpojfqdJXeDUegAl5a0u4YxJ71242rzKM+HSGP9TjR67tqheG4TLo6xJiH7NdIm0kloiE+P6P7pW6x/5SHVB1ZYFgLXp1TekiqjniYmCTwqVmjPt5wkbBdF1yC/UxNudaQLQywv4Il17Ot7lL/+FfynL9NsDtBVxetMcdz1DKQZiuCDAnLGd1YJ2xV55lD1ch7fc8Lc8AYsCK6Om/TaK/c+xGSQkeKPl+jbUyLg7vhY+uprpSDMjcMbx+wNItJlmnKJ5RKPxXd/Ove7DlltPwMSEboIx61RB2U8LrEbU4p5QoL0BA4Z++ouwxXBhyX5MBGPGuRhiwWnebNhUHsvyazk29dgiIDnE4q3CIg6/PYu+h88QTstKAslhw3s7WOK//brxCrg5ybkl7fpnpzAmQm6MkBThx61/WyqPVEdDgRZEdwV3RTsMCNvdgSU5L1Xo44JuAu+TOizI2QlInXqxy8LQ45bwigiAyW/t+SdfeNgA9oI9YGQh4Ivr373Fwx81wTV0Q5u+wgdrSq7y8zZm8esXhzjB01P6rjghSAL8OsNnI/YQJEjQ0ImryrNVxaMZo6WilX0XtFT1Zj3laUj/XByFLErM4q7HceXxsTdZc9fTOt+GHjcIV/bR1/fo1yP+ONj0rNb2JNrNKsDdDhEBhV5vQB3tND+TQZKeLYkP0zkB7kPWyH3WjEDk95b/SPrWKVoY8Si9wpvMulGzf7VBV+/teDLRWA3RRazOR3bpOUY++Q+9tqj9pDZm2dteOa+m9C5M62No3ePaF/a7EUGUbH6RCUYldAY/vU54WMTunHAbmX4VsOogzBS8ij2ecP82wZw8T6ui/f9QulQC/zDu1T/0XM0smSggp0fwrjFZgHZqdBZwpaGvrugfPsYHAbRyFsj2Blgk4AOtdfr4piC7QzwnyjpfmOfKvYSLrNeuejeV1f2W/fxlQAjpdmuIDvz60tu7XZcc7gyDFwLyt50ybJQ8rLAhnPSr/0Qzhh6gfpS8JDpPDOLgaOHC+q7c3QYMVFY1ngZetcfBXS/RQ46fF1p3liylhQtwMYFFNoLoO1khl/2ulnPfaJycdyAUYl/5YjB1444fm5EfntKMSz6DrtKsEz4SsADpJmhiwxdrxRBQZqWUAUkSt+LxL4c9rs14fkN0gtL8rUaiYrnjJ3Empwyfq056c4hq5LEuV0Ib48CN4fClbLk5rymXsssHgzphiX22tXvnAP5vs4YXjg/KyZQWM2gNc6VBaNsrLhxdnuA31ui06avFscFvuiQqMjNhnCtZdABhWDDiBcBLXqpv2wXyGpAWu8fI70K0PpYjgg0jjxcIp/YoVlR2Kjw1QGM+2GiCkgl+FqBnB/CWLHVCFsFMo74egHrJaYOleLjAh8GfLVAzg3pvnaMqvQyHods/VhkUQSOC+V+CTejcG1Y8Ecj4ctk/lAD7+aGaSvMbIdlc+98d/HB490VHqQfikHGs2d0srkfvKFKgW11hkFYO85cnEQoBHZrYpvxtQIvlNDm3nO6XrHBUPuYLNI/f0WQf+8p8ocmyI1lr/MNJ8b4dkclSKH4/YbwW7uUXz5E3l3AcSaXBensgO7ZNazq+RjdGPa8yvoAVss+/gTDhxHGJQTFBGQUkeSEZ1bI92q405D1xBuAhRlzc6ZZuItyU+CuB65k4003HoizXAaa0TZdWdMt5893/4Q3Or5HfNcG+Wn22Q/EuRJJjAwizmrnPHHcMdwZUCenqFMvl7k87qW1y55895MzfIj0goLC4FceJ338PIoRLpak3QY58l6f2xmWBfFenqk4vnDkICHvLAl/NCV88YDiSweE3RZ/cYP09EovL6pzP3uaFPi4xEvFBUQFquKEyInI6gBfKdH1Ad1X9kACKQs5GfMMsywcivCOOXeTc0DmenZ2UZq0RmcrpMPZVr784Mn2+zHG92SQK+Af20KPA5KFJMIyG0mhmGeSCOFshTbW9wSjiF8a0u13FCdGUaE3BgY/f5786nn0sCPUHZ4zeq7EdhfoYeoVjclOkn4/rbUyYAPFqkCqIlmEvHDy1Rn8/gPCUuDFLZbrJbJMFPQ5g6pEHLQ7UbjTe6GYoMuMPLuGvVeT351RR2Fq8DV1vibCmw7XMe4G4W4R2RWY6xptaDbafG8tsdxpX/sOT9r+wM+pf/AIX1RbutSlaX/QP9XGQAxZZIZLY30SkA5kryVWEXliTFcnwqyDSvtdGgUeG2LPbeJnVvBBhNqQocATY/y9BXKY+gSbeyV6cif364gBWZys0BZCW0VyVsLrh8QvPiQOK9q/sE23PUQHBayUMIpYFZBhCasVtjHE10qsCuSLE9Izayx+6x5tcnYDvG7OVXPuBdgvlP0Y2W8Ts7VA3RldPlxLBRfbN75Pz/i+DHIFfGW5hE1C2+Fl3xlvIIxTZlhnzjVGGQViQI87tBB4dpU8VJjlfuhYBrg+J375AUEVv7COj0PfkB232FGHv1ujGcwcNyNl68vR7ORsWHZSr+Dpb24IEIeROEvo6/sMrhwga0Pao0y+U2N3W/xOTdpNpPstfrvBbzfYvYS9foh985D61oJpY+ya8Y0M+wILL5k3HcfmzOMqy32nCdOdtMUwf4Fv/kCMAd/nBWavcH40X7k7HEfGi8R5lPMkHlfjx8rIk1FYGwW2RgWDUUQfK5FLE3zaIdePKe7VhK4va8USvDDpSaWDDnnYwcLw5OQ2Y8lIyWnNOaHD6YDWnVqFY4XWhRCgiBBEKERYm3WMzXrBhdILpt17Rbv3/U5G6ASSCgtT3hkJt0W5ifBmMvYxjuKAmXbU8wmtdGvLtemgG1HYX+ZW8730Gz/wc+oAf4W79edHZ+VmuE/Y50454qjLHHTQSuZhEi5l49k6s9kWlJNAWEvouQG6WdHdWWDvzgnHLbQBf2sBKeOmvf7W+tyR+3xOAhqEzoVOnJnDDJibMHejESdnpUHpin7xN0YFO1koTirnoGBqmAgmkARSVBpzlggHGninzTzMzl7oOKBi6omZZOpmjWz3V9Mmg26DF5rXeC19kR8svq/7sl4DvzT/iC+PF5J2FiwTqBDMGWUjei9sHmdnuMzEo0Q57QhtRipBN4dwYUjeKshVANW+1MX6/9PJ1RkJPBudwfJEVb7Mzr7BYXZmnpi6s3ChRZjhzFJmgTFDOVTjYRAeBOVeDNyMyg2BWwj3EXbNuJtht4W71nI7OQf0Sf3hbMixG80yrHSyP0wVMV9mvfsdvtrxCPADuXPxFSjC5ubwsNovVw4YHSo7wHboWNeC5wrhssC2wKYK46BUo8hko2S4HvFBQKKibtCBzw2dN9hRhy0y3dLITWaZYS87dXZm2bkjzqE5C4FjORGjqdBZ30NI6EOJqxICuBhZAwmhlkwtJ6N3ARfBMjRkjruKOiQWKTLvwmpXHoU8IOaI+pRBvvEDvmfxB24QgBd5sVzful8dDveKvMcgFIxUGTUdZzxztghsBdgRYS0KQzPOmnBGhCrAIAqDKH1I8Z6udoPUGdPWaJJzaMa7yZknZy7OHYTDlKkVOvkTlyZH+vimQtL+tQRABnio6aLQakVdKp32BYLmlpwbko3oCLRLXcvFNNiIIl9gJT1gzV7n9cwPMF88UoO87ykdZ0tZq4ujalqVDUPrWHdhR2BbjHUVVlWY4GzFwA7OOGXGLqw7jE76jTY5OTu1C/uWmTncE+dbJszMWJDZLSLzLKT+ZFs/rhHIAiYdLkXft3DC+AFoixl0vkF7cj2Gm/c3ElU6SWlWdANiHhJtyjg/xmP5UVwH+0MxyIkQQv8nninC1kFZpr04LRgULeMqMWmMIc4gBAaijElUKIUKq+6smbNCr9Nus9EFYZmceTJmQTgQ5cCFhiVNrjgupV/U99/bTs6ivP+7RnptsPmJMU5kpEGwNqylqGrZTACKabA1qrRkI32QK/mzJ+GOHzIe5UXK8iIvFuw8KOuUwtgOtMyExgmdEcKAOOw/gC/o2cVshOgEa9FBv5PTrCKXShfAZqC6HFqBppaQAmIB9f6Cnn443LN8J4tMsHDyt8A/r40aEq0g+DoDW6H0Xa7Ya33u+VO9K/6R3/3+Kq9GeDceUIeEyWQz6zLvh2ZESIZO/sTOtZMDnnO+fXjfwwJbysRkJif5QS2iVqD2Ly7ynzRGr8OIVpw85/3Ff8Ca9SX76/nX/gxe1i8/5PeSz4B8gxfDDle0udi/fxX++UVpMnLr1sWTujycLGjhJaUPGX77uU/x+rfD1XVe0SVLaWml7E9M80Gu5BfBr4D8aYWgU5ziFKc4xSlOcYpTnOIUpzjFKU5xilOc4hSnOMUpTnGKU5ziFKc4xSlOcYpTnOLR4/8CCS9aFl1JCMQAAAAASUVORK5CYII=",
    "coins": "iVBORw0KGgoAAAANSUhEUgAAAGQAAABkCAYAAABw4pVUAAAn4klEQVR42u29Waxl13nn9/vWWns4851vzRxUHCXSosuSKFk2ack2ZNiJ2+4WOgkasAMH3UAAI0CQxwYEvQVB8pK8NYIAcQcIOkza7rbUbbct2ZTTki2JpkSZxalIVrHGW3c889l7r/V9eTglywPyxEup3H3/L+fcc/bFPmv911rf/G04wQlOcIITnOAEJzjBCU5wghOc4AQnOMEJTnCCE5zgBMcM+Y98LHayBE7wd2uHfAHc5Xu/6+691wkIl35wzXyOfBgY18i8uXdNjWt0+T4qkhQZGJLsB2P0grEGrSE6CWjmscJjrQx7L8daLaz7ErYF9sLyt9gXQf+jJeRzFynmOdm8xs1rfNuT+xE+K3FqiBriBHMJvwhkzAkuw5sjl0gpjgJHhhGikotQquEBQ4hOiBbQIMwEZgul8bAIxoKGWAUaF6mDQ3vrxKOa2GqoX7xG9cM63u4LQj73OYp0i3AwIcxrfGgI7YwsLeiQ09ZErolShFYwggiFBloukuNpiTAAOqZ0nKPE8N6wBJIgIjQYjSqIR8WxK8YQpXaOIwfTJJgotcDMAgvvmAnMF5F6ukJ1+TIzfgi7RX70u+JiMfJX8vGc4OslEb6mqIRWrOm7nNUMuinSc4GBg7YJLYECoXRC1wk9gTZQsCRMzFAR1IxGjWhGNMFsOam7KIcIjfcMEcZJUXHUqkyTMlLPoSjDxYJZXrAo+lRnPdULl2k+yN3yIyXkuecIzR1a3ydjLZAPK8ogdMwzEGPTO7Y9dNXoCnScoy1CW6DlHKWDtkDphUwcQUDuEWK2POZSUpJCMsOSkXAcoAyB6BxzBwtZ6lyVFybTyMR7btZws5oxbq8wXQRmsSI+eprqhT9l/h8iIe65J2nvjsizGa3a0W5DL885o8YZb2yGwCMGZ4HgFBMPQfAIHYEV78idELzDZ+C9AxEQQyKgBigWFU0GUdHGiAITEeZOEOdpOSgyj98oiYcL6nFE68jryfjDRc2NCu52c3a5d4R5YfrSbWYfxKSEHwUTlyDrPklxMCFbEcp5Tr9wrEpkIxpPFI6LTlh18HDwbHggOWpxNMGBh05w9HOPD4ILDvECIpgTcEAyiLbUtqIizZIYyxRVo8RRe8FnjnYno9zuEH7ps7z2L77EI4s5JKFQYy94eqYU84YkDZORMclb6JNPEi9fpj7uufE/imMqZbTHc8KmJ68WlFFYDcJWELa944lcON/LGTyxzWbp6VWK5B5feFwrkLUzinaB6xW4foHr5vhOTugWFP2CrJeTdXOyMhByB+KwzGG5h8xjwUMACY4QwF/cxn32k7z06f+S/yEfsr2YsX04Yq6Og6gYRuOEuYI4IxUz5mmA7e4Sj1ue/DB3iHv2HMX16+RhTlY4yvGMdsropcRFZzxowlYmPJFlnG47Vn/+s1y+8irue9c4VykVhmUO8oAb5HQ7OXglekdTBGbOMSpKZiEwwrNoGi4cHrExnNKZG1KDkaEKvk74lBCEIAp5gebbxO2zVCvfxXyg6yKPesd2TKyaYeLYpSZPnirsI09vb9srOzuz4yTlh0LIk5CnxygORhT5iEwCeRPpqTDIE+seHgUeFs+aOM6sZWz+yvMcfObX+d8/8i0u5f8P/9W3rlAUBbZa4DsBej3+1zMPcWPrQcKpc4xbp1j0LzDsr9GlpEPBfrzDQ/vv0L/xOmd23uTDb71B7+YduvM53SJQqsdwNIcz+IOv8qwP/Pdf+WMuvLlDMiMDNsToeyE0xl6E0jIkwrAU0p3JVJ/juepFXox/Zwi5dInMDylHYzJq8q6ndFDOHau5sQ5sGKw7GAShmwlZBF7+LlsX/y2/8sqf88jr7xIyT1opyS60qdZP8d/8g9/iL4BHgFLf5HEd0k3v0Z+9zVZzyLotyKzLrf4adunDDHiWiLJ7cJedK2/A5e8g777J1vCQzZTIhwn7V7/PhVlDYwHnFBeEkIykkKvSNaVr0DIjWCTPW5NqMnnxWBWjD1TL+vyT5NdqynmNH84o29DLMnoe1izxoINtJ2wIPOI8m7nQzj2r7YxWAdlT5wnDCX40R7sFfrvP/MlH+Me//M94Z36Nn843yA//Nb/kbnGp1WNCSUMLB5i0iNpQNrdZ0QUqkLRE8nW0u82cATt1xeFbbyLf/vf4G29yfjxiexSRSaJaRNJCqeYNsYns1cafVQ07deSGer6jjiPvGb56i9tAvO+F+pOQzwdLMiYL8r7QtsQ6jlOiPBAcT3nHRQfnM8cZL6x4R0+ETARpZTCe450g7RLp5fDUs/zTv/e/MFy8w6dDTj35Mr8qIz7W+Tiv5D/BS/4sh/kW8+wMh26bQ9+m09rG5SukrCB3EVvcwB+8RTl+m0034vT5U3Q/+nMcffx5Xl47xev7u2STIVuSkaKiCk6hAXbMqE2Z4dirlLqEamfK6Dgt+A+KEPno05SzCj+rCK4hL5WOCGtFYF1g0wsPZY7t3DMIjnYeKLwQnCMLDh/AOY9zgnQ8YVAy/E9/jZeLPuYgqAKHbHaeZJh/iD9Kjl0CIxxTVTKOuMCQzTQnE3Auxzy4sov0B2iREXWMTO9STvYoynOMH3iMrU9eYnzjJpPdG2yFQEwgmqgNdqMyN2Vqxr5T5nXDbLW6OD3gIN3vhPjz62SzCl9HfOYpPHQQ+l7oBc9W8DyVe04PCvqnOqyJkYtjqZkKzju89/gA2ivIN/q89+zHadsuDzWP8C+zSK/1Id7Rmjruc0kcyXnEEmtMeEinnBZPEkVkgbNDRGd4jQjgpI3Pz5CKB0g6pTN9lXOayPIBW5/4JLenMw6uv8tpcWiEOkb2orJQY+IdO3Virsa0XWXzHab395F1CYKskTURV0VCaZR1oN3O6DqhmwW2c+HH246N9Q7rv/YLvDa6y9lJRek95paEuAxcmePaDr+6xa1PfpJDGfPLbo9OWuFbNGxkK+xYYJjGPCNDPso+H3EzNlzEAYgn6pSMKQ5FzGF0MdfG1CPisPYqMe9g1Xt0nbGwXR74sSfQJrD481foCdSNsR+NWpWJwS1VZpKYV3Ux+03mzYvHpPp+IISsQig3CLOK0PIUhVAWgVKMXnB0y4xNJzz12AYrv/wZvvdT/zX/4xmhF4c8tDNCvEe8ICKQe8ghbJzm2qUfp1vd5nRo8ZANeVQ6/GHVZ8cZqy6jJcvzfY5QoxRWkzOjcIKTDqYKOMwvnYzOe5IETBPOZQgVfnGDTjjFXtrl7FNnkSZj8eq7eO/YrRJ1jEwS3IyJWcqYp7KcXF8s0u1jkiMfhNorhxC6CakjvpuTm5DhyEQovVAGoXAeGtDdXdbn13j07Zts7o0R5zBRTASygMsdGgS6XeYo68FwJBqvPGW7/BO5RRVzrsuAG6HD29Jj5kssDvmQHnFBJpyXBad1TGlzHBFpllOnImQux3BQj/C1Z5r/GLd9TqHGKBrFP/p7pL1d5r/7Z3SCpzHoJyPTZcwlRFW3s5zHY7Haj32HfA6KydpanmQeJJDnnhZQdgv6wbPpYS3L2fLChVkk37vLZjnj6W9+m0evHQBhSUYekCJAL4dWwD/9ca4/sMq5ekiXgKdkIS2moeExd8RPyA5PxAqs4GpSptLjMAyYSAE4WtKilg5jKZkmD2oEEhGj0RYTusxbZxmFmjU3p5cN8NUC3vgD0re/TX2lwmNkdSKivE3GzBKzRbuarEw2dZfZsRByrDvkOZ4L721ezlqtXW+erHXPJZ4bRYBCPIXztLynFLDMkeae0e9+nUHumXc7uKhL+dESJAOfCc5HZHiTR+OjZLEBP4O8RRSlxFM7pVajn8MnmPOkHuJszigqeylS0GHq2kzCJkc+UGUzerrPY66mjSexwoQ1RoxpM2OmQ+TP/4jw8p/SGgw52h2RVMmdsQAyApkoISlZS3H1WnIc4I9D/T02Qj4P/jpvZ7u7u5x+mKwQ8lCRZ13KdkErZHQyWHPCdoBNjJ6DTuEp2hlFEKgbtNdCW54FwlQcsV3iujn17h3sRuS75x/kMRlyISomY7Zcom0RTFHLmHhYyIQtv2DdJjyediBCNKGeeqa0OcxXmWrGzvw2D9RzQjNnXTrgArWDyTe+wsrlV2ht96i7gdkYus6YqqEYSSNqDtf2ZGPFYSYsncz3hQyRi5C/wXaAhvYDhDric8haLTre0SbRscT5UPCpENhslXT7JXWRc2Wlx9GpLQ59wX6/x/SRB3iyX7AVApezDFeWdIo1EjWrzR02r3+XTpbRnP0ESRd0mimZ1CTJSM6hNifQoAgLTSQTMg/S1JRxSpvEJu/BcELz9W/jJnNsHmGrw/l+iWtnxFvXcb2C2FKmwynpKJEb7Ceo1ahRBLcUGinhO51Df+4Qd+N+IWTAad9sK92VHbcwQjcRskjuS1qW6K5ucOaBB1l/8GF2Hn+cy2fPM93awHqOnqu4mGp6vkNgzkDHrLJgNQmf1BazzJG0JJKRucC52QGdb30bv/4mrWcuwdnTLAhkCBYNdEZXIpkJrp4RYgITLClqHm0SGhO2d4DEBCFAO0PKNokcnUVihBATzdyoD+bYKBHEMAxlGXl0yQiVERScKtJn08OuvF858r4J+QLwJSDqjkwX+HKBcwXBFRS5o3U0ZP3Zz/DMb/46p90KNwnspxlRA+0m0kmBK6ZkThErmViimwUuOOH8+A6NVrTKwLbMCNWEcLCPqxr47p/Re/u7NKfO0Tx8kfqRj5JWHsThcCSKtECrCa5JmBPMKswMp4aPSto5RKqEOYeUHgoPMWF3x7iDGoLDbRvV3YgmCE7wZjjAS6DlhHYwijlLuQfJ3fMN/mgJ+SIAt23bYaeAoeK6jjw4sqKg3SvZDp5TaZfPNDcJMmKmNT5sohLx+RZvSYtkNSUzMvbZkhmD1JC560tbxPexWCGhJnU9+sTDxP4edjAkXL9K9p3vQvZ72MNP4B++SH3mDNVGByk90i6QOuJmgCqYIg5YzLGoiCnkGaaGiIdFjW95bFvY6ddcfTvymAg4IfNGCNBSYRNoTBl5yJtEdY+Q+8YOkQ9F3NiQssTFgC89ziVCmdEXIctKptHox0CPGu+EJIJDOA8sXEBwdKxaBoNwRAugCUmg9fKY0HEkF4NugdUlw7zDbvc0O/WIx9/8Fhvf+BOYQFwboI+dIV48B6fW0UGHUAa028FnoKUjtALMGjRzYA76GbpmjHuOyZ058Y8qfnxHaReeuS3nKkSjlEgXR1cCHVeTx0QQ7P4hZHMTV/WWbg4irmOI87ikeOfIg5KrkksiiEDU5YoXQ51Re0ipocuCIlaQFCwhTQM6B5fjUKyKBAu8xhZfOneW5qOPMF4/h7TOU0/f5pnLX+Gjf/pVzlx/m/5kSvj6ZfzX/gIKj66U0OnA+hppu0883MctEjatkWGDnq7RytFcn6BvzNgcK2X0aM8TFcSEvKrpWyDhWLW09GvlgWKqeOukwPQ+IOTzIO/08DEhQZEVQ7zhXI3LCrImklU1uYsEtWWKjjQ4iagpwWa0G8N0zsDNcdaA3kv/FEVMIGQYsjxeLv4iL5z5DLBggKdHzTkarPMA9cf+C9772N9n5/KXeexrX2blylsU7Rb4DNkb4+7s41+/CQsonRBzjx8U2CDH9xvuvjxlcGD0shztGJUKUitWGQ5l/akHWbx5m5WbU1LwbDSR3Du+Y4orWlN/XxACENMyzTMpEhOuleFyj8NwFsiORsT5mJiD5jnkA4QuSo2jJFCiKIKQfEC8gjg05rhqBrv7NHf3ybXF8NnHOV2/yxmZ8RG/whtH1ynGb7I1v8PmYoptfIx3n/wF5o//NPrSl8m/8W9YvXYH181I/QzW29goIgtF1kp0q718PduhNQxIViHtAj9KxGlEU4LScA+epfnVf8jvfO0P+NS//wu2rg5RhK1Uk6nH2XIRyf0iQ5bOIV0SYyAqqCViO0euXmX8W/+SvdNGp9/CegWJHNTQVJC7glTP0dkYme5iscZig1Rz3OEUGde46ZjwxM/y+qcn/Oys5lZWMHNTPhmvY/ou/VMPMyeH29/j45dfZ3LuEnsf+xzy4Seo/7d/Dl/5Gi3xkOfLwz73kDtsEZGU0Tzy8+Q/8xTzq+/xvf/3X3PB7XDKOWqLpKC4Zx5k9PjTvHXtNS6+9BrnDbyHPHkKM3xpxxN9fd++rA+DG66TJ0V8wHWV3HvKLBBcTrcdeCjPCLtHlBdKttoV5egAd/sWYT6BeETYu0q+ewu3fws3GeFIeIs4J7hui1QW+KLH4pd+g1f7nsfTnFO2xks251x3i6a7AsUT3Go/zd3Nh5i1lPbkNdYPXiPrrCM/+YukR7epv3uFcDDEneljuUMWET+tseEUP5tiq2vUH3ma7GM/w+tJ2bt9jfXxlFwd6Z2brNy9wo//3jd44PqEicF8YRyI8QaJUV2X1TjG8ftVe4+FkMNVcjMQjy/vEdJqE9o5g1bgQrfF1sYW88/+NCvnTpGHLnZ6Ez17Fr++jR+0kfNb6HYf2exgGwPEC+YFUcGGU8LGo9z49Gfp1UNOe6OtkSgDXmbGRYNm8Q4bYYUJPUbFBovOCm2fyK5fRkb7uA8/TfbcJap4hA53yVoZ1gqwUmKDDq45RN76Np0br9Id5Gw98zz+4YvsXHmTzu4B7cZTvX2LYpKo68ikSsscYFNeXyjDuYXFIsbRfUOIGpIg62cU7RalLyl6gb4XfuLxp3jjv/uf+MbqRQ6zdfbXNlisnsPSgINFxvWwyWHnNNJeRVtrNNkmlFukbAMtV6BX4D76HDsrXc5YReEcla84ZSVvWYdrwXM+eKpml42QWI0VXTJSq0cx2IDRTdzuVWR7DfeJS0imxHffIyvzZbx+tYOtbyDdNjqe4r75LfLZdfpPnmXtJ3+G/Wu3Sft79BqhntekSplUiXlSRsD31HO0iL6qUhreN4RUET9okeeeoiwpAviVNg/+xE+R/5N/yk7c4SfMUzd3WWOXZzQw6J1htHmR2fpZiv46K/1N6sEZZOUUrJ4hnTpPeOAU7sFVkq/oFX28cxhGsMBccs6mkuuWceS79DCSDlnxC0qbEeIU0gwZ9KFI2J23cBg8+Qzy4Ab1lbeXmt9KFwseWe3BSh/ObmFHd+CVl/EbOa3nf5bd19/D3rtN1xz1PDJOyyz53aR8txKGTQyL+4aQ3T5FHfFlRugU5KWnXY/xH36Mh3/tl/kUQ8pU8ho5sVin8Q/xJbfBHyfhVoxgNX2bcRhHNHGCNGMG0ZhKhx3foyof4ui9r9Nv5jA4h4sVIl1mLifJggsp45qChA4lMK9vU1Z3cItD0CmWpjjncFmO7d9BYo2cfxT/oTPEq9eQm/t4EbTXQcocNlZx5y8QfUH802+SD98h//Gn2Xv9Fvn+FK/GYZ0YJWOnjvyFZYzqJlRVSu/7yDo2LSsqLlOcJLzLCUVJUQku7vPR1k2ekw63Uk7TbHBDNjnUwFW/ytAqmpjzsniCzFn3M37Kz1CNOCu5s2iYTO/y5NTDN36f8KubLAZnyJKjQTFnEKZ8PLV5Ve9yys3pCcRmRq4RSYJ4jzkPPsNtnyKN9vAHOfWpJ+A/8fB//g5JE8yn0MswSaAee+xRdHRAeuNt/PwQfXaF6+/sch5IGI0ptROS1KhUciwx9WMjpG3LkK1FgiVCluOaMVZFtO9wKGfyKbm2WHVtPuSMaEO83GTDGZOoNHs3kGuvseUcKVVk/Q7bEpDFFNkZYtdv4f7wd9G//5uMJMNUyVAsZMTqZT6hU2ht0ISMVvcMi9mYkMZ4hRQyKPpEC7itM6TDXbK7I8ZbzxB+rU/25X+FLKZkfpMYFVsc4G/ewBcZs7xDfHuXclrT3FPvK4GFCjVgjWByTEkO75uQJ8HeBGKJy3Jc9Pio+AJC1eCsxvCQGlSVRiB6x1CV2oQ+RmmRbm6QG2l+gOQ5ISWsztBy6UO1LMDpNdJrb5L/8b+g8/w/oI4FKh6aCW5xm0xrXCoYt3+M7wXHoO+Q+ipb2QHreJIGXLZCModfX0FH1+hOSg43H0c+3yL+9v8Bb18nrA9IGOwNCZnHN4kFhu4ovWQgSm1QY0uClpmSko6jjMcd1w4xQ3SBJMUpZGIUqSZrImIJTXPQBkdD0IYWkQ2UQVIsJeoItQs0WQHiMXOwiFA1qC5X5bKMIEe/9Ae0vvJ/0c4bCgc012j5BgmB6Gesp5tsaou3pMvN8iO8xIO8boa3BS7tk0mDSYYbnMXqG6yNDph1zuOe+xzzm4fwzh5y5wDnHFolCh/o9x3T3UhflZigUSOZ4Q1cA+bmcixZJ8dCiBpSLl0nLiQCnlwT2WhGqZCyDPMewXBWEbSmbRU9bWhrwmlEJOJcQpxiFiEltKmRFEHT0rrOArLdgU4b+91/R3jlq6h36Pw2RUqoZfg8J/q7PGKv8VQKvKqeHfcAV/VDvJoMTUdQ3ULiCCUgK5vo3nfoD/fR8w/R+dSzzN65g9+bYTFhCCkzZgc1epgodBk1bAzUDEvxeOtD3reWtQVucppW48hKoSiEjhj9LFAonArKM9tCJhHNPRQDGreFuhznG8RNKDNBsgDawJ33EJOlGyIPUJTQKnBBsMUC8QEVwSYL5JuvkLfG6IUVQp3wWZtEhsMRC9i0HR7UFV6XNtPQI9HhaHaLrcUuIc7Ag2QBW+zj7l4j5AH3oTXkcI9044jMHNpUVKHizqtTijtKH2OclJ0Eo2QcqPB27RhLnVUzmul9oWVNJ5g3CAHXOEJQAtDKPcWf/AWxP8E2K8rDOT6sURTb+NYKbLSxYsEsOGi18Ys5No1kVUJnFVIEtFVjVcL2h/DeHuzP8arL0GvdIP/8d+jGz7D4qWexWpAYkSJD6oYmbzhVf4dfi4/yb8sLVEWbVfkw4/l1Wosd8tuvIqkiuABNBIWJ1fQ++wzNS+8R3x3iNwtaeUVzZKyaoSZYgiYl6mTMo7LwgQbk/kqUU0OahJdIQUEnKisi9Lst9PFf4dpZZXD9Dbrj27QOrtMevkW4Wy8TZ+YVWi2wcURGM6gVyTKk8NDKMOfRrEQefRAr2+jmCrQy5O4OzZu3cF/6U/Jxov75n8GzDNPiElIZNTUuvsQv3vom+ytPMG1vMMtXIO9CbMhHU5r2NrMPnaUuwOs+401H6+MX0a+9SiRn9lLF+aNEIbLUwEyoDWZqzEKkUiMuS+Lvk7ws77A8Ic7wAUpN9FRZiQ3deYblNRvtLcrHn2fKAaHpcDnrcqcZ0kqJvhzxQL1PezxDRmOMgvn6GZJXmnZOmfXxzsPsLlnuoYk00wnBMtwrV5GZ4n77RYr5jPo/+1XqJOTVHDThfSBOdol3r7G5/wYrvSc5OP0I2urgzj6CbQvRNRTNiF5cIKGgzrdpPveTxG+8Q/6dIStTwyyjlggOvAiVCbMgTCtofJvEwul9o/a+DtBaRvmSw6vhky3TgbRGY0UmE3rxiK5UqOuxZoHSbzN3I1rVLdqhh6ytIxsDRr7PnhjeJZrJu5ya3qA9myJ713GjPVyjFGa49+6iKaGlQ4sO8pVvkY8mpF//PDVQNDWaFnB4lyCOmObw9lfZeuNr1I9+nMnZi5ALob5LHpRUdKCa4q5eh/FtZnMjmzZYmZFSIgQHU0O0IYoxV2MWhEYX6PC+ObK+APn/jE57NB7qIjFPgSpCFY2FT0SL4AKNE7AF6sBJpCsNg3hAJ+3QSpBSQopt1vLAhhN8ijB8CxZz1AImC9QvM9Y1eGKnhF4J8wqbJ/Al/N8vEW6MkP/2HzLvdsnfeROZTCDkoAkaJekMf+VrrNy4TLP9CPPzFzmYXaN35W38K1fI9+8w3z+kvrJgHSGdWcd+4x/x9te+Qf+3XyT3juiUmVtmwqsI6nB2fxxZX4Tuk6T5iCrLmTTK0DsOwvIoW0NQn1BqVL9f129kOCoUVYeSo7ksOy9kLZJzJKtJyaGa4S2COsRlmKtQDLIAnQIXHNYtwTWoGnRK7E+u4G7+M8Jv/BzVSqIUhzQNOplAqqDbQ/Ew38e/e0jv9ZcpXnuTfFYj3lGfSuz8eWTDB4yErbSoPvU8zbU37qUOFVQaGWnOdGKoSx0LHB6LDHnfau+LII+67RBbU9GE80oQo/CB0AqstEoe/ekfo7tqtFNcGpBSIAieSM6CQoZ4EzBdrnIBNOJSws2G0DRLJpsGmc0h6XLg4ym2P8XnYRkALrNlis80wdUh4auv4Fue5qEN1BLuYIRrlyR3L5vFZUjRIX7rVfKDGdYKNFuO/esj7Ds1p9RoksBkjvvqv2P1629QjhrGtfJKUq6Zsp88R56y2qnrBv7Scv+RCnX1vV707PgUiHbIIrUYp0SehKOm4SDOWWNAzB1OE94FfDKcJdQMmrjsTaIKPmEpgdYIgmrCecG8W5IJGHZvqwVIkGKCWYUdzZC9GqkNOdtBFwn5re+Q/8lV6v/8ozQXBmSV4RZp6crp9tF37yD7YyhyiJGmqhl/bcT5mUNzR2NguzP0+ojGjNocuxgHsWGSchaZp3E2ThxTfcixlCM889kDprtkkxluw+ETuHaGhgycEnb2mY+PyI526E6nIB2qokcTOsTgiOWQMmSQBAktLM+QIuCyEqtn4MBCjk4bOBph8zkMJ8jdQ9if4hDcRhdrd6B02EqGFca0Bw2e7PUh4ZWbSFTihVV0UCJJcNHQ710hz4TUE8abyu2XhrRei2y2HRPgMCmHCrtOuG7C28l4xeDNCDsCh3rUH82qbpwzb46DlOMqi5bnnqOY3yT3ShmmdDptemWbU92cjzaw9UiLD28mfnYyhm4X7Q+IrQGx00U7QtFbJeYlmvXBJajHhKMZbucOTIb4piZOG0JSZGNA3FzDAsjkCJcUWiWMpuifXyWbNAgLDoqK8XuJzpXIhrE0Njda6KcfIP7CR4g7u7gr12nmDXE4p7lek7/X0DcHwTEyuBGVKZ4Jxm5K7CbjusAbdeJ2lXPQPVo7zDlYXOZ4+p4cl2Fozz9P/ccvEKoRMcuoG1i4yCR57qhg25tc+NQGNjrAqhpXK/nhbcq7c9idQhXJ1SAD7beh3wI8Mq0gOBi0yboeyi62tYoUHpku4OoObrqAolg2nFnUy4IflvYCqtSzBEHAB+xuhXvhdYo/vobvBHQcyaYRZ8sSOgtC44GkzBWGqswTjDH2TTlU4dDBwSwwbmdUDQf1FY6vCc2xWepf/CL67LOk7oLUMmKdUxeBqVduT2oWnRYX11axUhBVrLeGNhE9msJ7N3ApogauDMipLbQsochJd/dxkwniM7h7hKsm2L7iTKFpSNNm6Rn27l4flBybR8wJmvtljhfLzkCmslSZC48dNth+RDxLWZEHknNEU2KElIx9NXYxRmYc4LiRjH1x3MbY7ZZM9O6gusaw4RhxrHlZ50ekmxlqY2Inpw7G1DKO6iNclaiSQ/I22kScBKTTQcoeqhWq8d6kZtDq45JiteHnEakTFgS8x9oF9HM0giwEvEC0ZW8sSyxbxhl2L021SgYNOH+vgRnLy9QJqfCkICTnMYNUJSpxS1eIGXsm3FQYaeKuU244Y2jKXtNm2q+ohbKBod63hLxwmfhLlwi3G2LLkNkIoU9ujuxowkHTkPo5LhVIZwVzOYpgK0OoxrioiM+wPEerBc4FLLhlVmOMy5jIsqMlgmH3YikSFTUF53GZwwYBnSdm1xfY9URfjSSAcziRpcveQS1CSkKKSlKlTjBzxkyVBuOOZNxIyigquz6w44ypRsadgrreXY9vsFPDfeZ+/5uy5I3bxK8/DdUUq5ulWlt0SNZw+L2brN0aMshLmlNnSKvrpCzHxrv4arF0CuIgb2OxwrkAVYVUC3CC1TVksrS6k2JVgx1MkSwg3RJ1jnR9DG+N0O9NyN9sWJuCy2DqHEPv2BXhDsIdNXYV9hTumHLNjHeBq8m4bsJV57iS4DrCjvfsBGGvzhl3+syym9vVZXbnHGOPk+PWsv621vUARSsj31DKWUErTwzuTPj0IvJTWeBD6z1OPXyK/GOPIKeM1gpIJ8eXbZzPkViBD+jeHhzsL6OIh3McSrJAGs3h7hx58w4yicgsITsLZG+OzBONg7pwzJwwM8cMY6TLOsEZwsI5oghJHBOMoS0/nyNU6piZMZbEQeYZqjFpcqbtnLrfpvnmFaZA+iAm7oNqz2RbH6fhVcJdiMWcRSXkmz1umPBn4xmH13Z47M1bbP/+y6yUgfZ6i+yRdfTx0zS9Fm5eYzEitw9wtw9grvhRhSwiUhvZqILZsuZcDFwyonNUmTHsB2biqaMuCTBlZsaMpaHXiDFSmFuidpEjAiMToijT4JhqTe0d0xIOJzC3jKqTUxcZadAmfVBkfJA7BIB/fInsO0NaD+SEWUNrMmd1PWegib4LbBisVInV0YwHxpEzqqymiq4areRwZnhVnDpUjEqg8oI6t6z1857KKxMRJh7myTExY6EKUUlmzJIwS8uy6YWCisMQZiZUbknCLAhzFaLzzGJimjka89SdmqoekIrpIFlZNo+t7zR8mPTCC39HCQH4uafp+Bl+1ZEfLMiyQCZCPqxoZVC2cgpfEfKCDsLaLHG6atgwxSVQjOiMqMsa8QUsS6DrZUy7SsZCjaYGtEY1YRpQgwalcoGoiaRCcpAimBeid8QEKTmiOhqN1EVNbQPqPJBaOck7LHjs5hsPNNe4tuCHgA+8o9xDGfUbOcUoUa1CYk6TcmofaKipmoaszgiTBUOf2LXATTE6CJInVAWd10uNVmXpmrjn06IRUlORRNDEUqg7pfEOi8vK22hp+V127398QQoNMUFsWmhYepVjKNGsR2zly9XvHdbKl/e7xrXIDwk/lL69v/k5ind38VWDTCtcu8F1F4Q6I6sVxwyKFlIlvCWCKN5AGjARrKmwJKTgUDWkvpeYNm/d074Wy4nLPCnM0EEPG3YQJuAnS7U0gWgHmQm2CKR8SnKCwRpwgBesm5MyjzUJWVOkXl/Oz82a5soVqv9gCPkCuIPPkY3my/vtT3Bugq8TMt/FrazcS0e9t4oHAxgCYYRNR1gQLN/EtLtcva0d7K5fTnQrw44W5/4ynam5sR3hJTa56HZPT/+GWn+bHY/5Gw/Yg/c+mXAtvfQDW+L7MY3wc9sU3ydkmclBbGXL6+ZnSVtby/fvvIPjJejynL3Ii+87JnIchMhzPPeXA99l121y+S+t18klZHOI62389RyweYNUDVLH///fUPVJK3vohQH6Rhd7/nn0i1/8WwO274/jCyB/9fESnwd/l+cEroaKJLfxdo1r6Tmes+d5Ub/EJd/lJXvxr9sTAoSfe5p8WuFiWpbqeffX7xs89v3vYkKOjgZcGw7H71cDOw5CwlODQY/hvb8GMBgMf2B5ynIgmcdm2fKZHQBNWt4781gefjDYekjiQeLWFvbCC+gxWcICcIlLYZOh65HbC1yu/8YcGODOQdFs4851CNMFIU/4ZWOAZWaNGZLKZU2hGVLek2khx5/Nufl77/NoOw6hnubD4QzgItAbYq/+gA9af2VCuywflgLLh7Vs/Y3JfnL5ABXj2rE/fcAAXuKl5gt/O1vzr97LPgk1Pw13X1gWcQ4v4s42yFXg9DWEc8vF9P2Hx2RLNZqmQj7xHs3vcYITnOAEJzjBCU5wghOc4AQnOMEJTnCCE5zgBCc4wQlOcIIT/B3C/wfQrUtjvDjYCgAAAABJRU5ErkJggg==",
    "masks": "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",
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
