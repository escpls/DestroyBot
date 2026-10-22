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


def in_admin_chat(update):
    chat = update.effective_chat
    return chat is not None and chat.id == ADMIN_CHAT_ID


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
        f"👤 Пользователь: {profile_link(uid, app.get('user_name'), app.get('username'))}\n"
        f"🔗 Username: {esc(username)}\n"
        f"🆔 ID пользователя: <code>{uid}</code>"
    )
    status = app.get("status", "pending")
    if status != "pending":
        text += f"\n\n📌 Статус: {APP_STATUS_LABELS.get(status, esc(status))}"
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
        return "✅ Ты уже в чате.\n\nПовторная заявка не нужна."
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
                f"👤 {mention_user(user)}\n"
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
            "Перепроверь его и отправь еще раз!"
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
        f"👤 {profile_link(user.id, user.full_name, user.username)}\n"
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
        await message.reply_text("❌ Не удалось написать пользователю. Возможно, он заблокировал бота.")
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
                "👉 Нажми на ссылку и отправь запрос на вступление, бот одобрит его автоматически.\n\n"
                "⚠️ <b>Ссылка только для тебя.</b> Не передавай ее другим."
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
            await query.answer("❌ Ссылку можно выдать только одобренному пользователю, который еще не вступил.",
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
            else "⚠️ Ссылка создана, но бот не смог ее отправить. Возможно, пользователь заблокировал бота."
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
                    else "⚠️ Заявка одобрена, но бот не смог отправить ссылку. Возможно, пользователь "
                         "заблокировал бота. Когда он вернется — нажми «🔁 Выдать ссылку заново»."
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
                "❌ Не удалось связаться с пользователем. Он должен открыть бота и нажать /start"
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
                f"⚠️ По ссылке заявки №{app['id']} пытался вступить {mention_user(applicant)}, "
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
        await message.reply_text("🔒 Шаблон меняется в личке с ботом: открой его и отправь /шаблон.")
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
    """Фото владельца: либо фото для шаблона, либо фото заявки."""
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
        keyboard.append([InlineKeyboardButton("🔊 Снять мут", callback_data=f"unmute:{complaint_id}")])
    elif state == "ban":
        keyboard.append([InlineKeyboardButton("🔓 Снять блокировку", callback_data=f"unban:{complaint_id}")])
    else:
        keyboard.append([InlineKeyboardButton("⚠️ Выдать предупреждение", callback_data=f"warn:{complaint_id}")])
        keyboard.append([InlineKeyboardButton("🔇 Выдать мут", callback_data=f"mute:{complaint_id}")])
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
    text = f"🚨 <b>{title} №{complaint_id}</b>\n\n👤 Нарушитель: {offender}\n👮 Отправитель: {reporter}\n"
    if complaint.get("reason"):
        text += f"📝 Причина: {esc(complaint['reason'])}\n"
    if complaint.get("kind") in KIND_LABELS:
        text += f"📎 Вложение: {KIND_LABELS[complaint['kind']]}\n"
    if complaint.get("quote"):
        text += f"\n💬 <b>Сообщение:</b>\n<blockquote>{esc(complaint['quote'])}</blockquote>\n"

    if state == "warning":
        text += f"\n📌 Статус: ⚠️ Предупреждение {complaint.get('warning_count', 0)}/3"
        if complaint.get("auto_mute"):
            text += "\n🔇 Автоматический мут: 1 день\n🔄 Предупреждения аннулированы"
    elif state == "mute":
        text += f"\n📌 Статус: 🔇 Мут на {esc(complaint.get('mute_duration_name', 'неизвестный срок'))}"
    elif state == "ban":
        text += "\n📌 Статус: ⛔️ Пользователь заблокирован"
    elif state == "unmute":
        text += "\n📌 Статус: 🔊 Мут снят"
    elif state == "unban":
        text += "\n📌 Статус: 🔓 Блокировка снята"
    else:
        text += "\n📌 Статус: <b>На рассмотрении</b>"
    if complaint.get("handled_by"):
        text += f"\n🛡 Обработал: {saved_user_link(complaint['handled_by'])}"
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
        await message.reply_text("⚠️ Чтобы подать жалобу, ответь на сообщение пользователя и напиши #жалоба")
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
        await message.reply_text("⚠️ На бота нельзя подать жалобу.")
        return
    if target.id == reporter.id:
        await message.reply_text("⚠️ Нельзя подать жалобу на самого себя.")
        return
    if await is_main_chat_admin(context, target.id):
        await message.reply_text("⚠️ На Администрацию нельзя подать жалобу.")
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
        "🚨 Жалоба отправлена на рассмотрение Администрации!",
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
                f"⚠️ <b>{link}</b> — предупреждение (3/3)\n"
                f"<i>Мут на 1 день, истекает {fmt_dt(until)}</i>",
            )
            return {"count": 3, "auto_mute": True, "mute_error": False}
        data["warnings"][key] = 3  # мут не выдан — не обнуляем, админ решит вручную
        data["warning_expires"][key] = warn_until.isoformat()
        save_data()
        await announce(context, f"⚠️ <b>{link}</b> — предупреждение (3/3)\n<i>Истекает {fmt_dt(warn_until)}</i>")
        return {"count": 3, "auto_mute": False, "mute_error": True}

    data["warnings"][key] = count
    data["warning_expires"][key] = warn_until.isoformat()
    save_data()
    await announce(context, f"⚠️ <b>{link}</b> — предупреждение ({count}/3)\n<i>Истекает {fmt_dt(warn_until)}</i>")
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
        f"🔇 <b>{saved_user_link(user_id)}</b> — мут на {esc(title)}\n<i>Истекает {fmt_dt(until)}</i>",
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
    await announce(context, f"🔊 <b>{saved_user_link(user_id)}</b> — мут снят")
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
        await query.answer("⚠️ Состояние жалобы уже изменилось.", show_alert=True)
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
        await show_complaint(message, complaint_id, "\n\n🔇 <b>Выбери длительность мута:</b>", mute_keyboard(complaint_id))
        return

    if action == "warn":
        result = await give_warning(target_id, context)
        complaint.update(action="warning", warning_count=result["count"], auto_mute=result["auto_mute"],
                         handled_by=actor)
        log_action(actor, "warning_given", target_id, details=f"жалоба №{complaint_id}, {result['count']}/3")
        await show_complaint(message, complaint_id)
        if result["mute_error"]:
            await message.reply_text("⚠️ Это 3-е предупреждение, но автомут выдать не удалось "
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
            text = f"🔔 <b>Мут истек</b>\n\n👤 {link}\n⏱ Срок: {esc(item.get('duration') or 'неизвестно')}"
        else:
            text = f"🔔 <b>Предупреждения сгорели</b>\n\n👤 {link}\n📊 Было: {int(item.get('count', 0))}/3"
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
UNVERIFIED_REMIND_BEFORE = timedelta(hours=6)  # напоминание за 6 часов до исключения


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
    await announce(
        context,
        f"🎉 <b>{link}</b>, <b>добро пожаловать!</b>\n\n"
        "Ты вошел в чат не по заявке, но остаться можно в том случае, если оставишь заявку в боте\n\n"
        f"❤️ <b>Ссылка на бота:</b> <b>{bot_link(context.bot)}</b>\n\n"
        f"⏳ <b>Срок:</b> 24 часа, до {dl}",
    )
    try:
        await context.bot.send_message(
            chat_id=user.id,
            text=(
                "🎉 <b>Привет!</b>\n\n"
                "Ты вошел в чат по ссылке без заявки.\n"
                "Чтобы остаться, подай заявку здесь\n\n"
                "Напиши /start для показа дальнейшей инструкции\n\n"
                f"⏳ <b>Срок:</b> до {dl}"
            ),
            parse_mode=ParseMode.HTML, **NO_PREVIEW,
        )
    except TelegramError:
        pass  # человек не нажимал /start, личка недоступна
    try:
        await context.bot.send_message(
            ADMIN_CHAT_ID,
            f"🔔 <b>{link}</b> вошел в чат без заявки.\n<i>Предупреждение отправлено, срок до {dl}</i>",
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
            f"🚪 <b>{link}</b> пока покинул чат: {reason}.\n\n"
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

        if not item.get("reminded") and now >= deadline - UNVERIFIED_REMIND_BEFORE:
            left_hours = max(1, round((deadline - now).total_seconds() / 3600))
            await announce(
                context,
                f"⏰ <b>{link}</b>, не забудь про заявку!\n\n"
                "Ты еще можешь остаться в чате, подай заявку в боте: "
                f"<b>{bot_link(context.bot)}</b>\n\n"
                f"⏳ <b>Осталось:</b> около {left_hours} ч\n"
                "После этого участник будет исключен из чата.",
            )
            item["reminded"] = True
            save_data()

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
            if ticks % 60 == 0:
                await stale_applications_job(context)
        except asyncio.CancelledError:
            raise
        except Exception:
            logger.exception("Ошибка в фоновом цикле")
        ticks += 1
        await asyncio.sleep(BACKGROUND_TICK_SECONDS)


async def _on_startup(application):
    global _background_task
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
        lines.append(f"👤 {saved_user_link_with_id(uid)} — {int(count)}/3{tail}")
    if not lines:
        await update.effective_message.reply_text("ℹ️ Активных предупреждений нет.")
        return
    await update.effective_message.reply_text(
        "⚠️ <b>Предупреждения участников:</b>\n\n" + "\n".join(lines), parse_mode=ParseMode.HTML, **NO_PREVIEW
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
        + "\n".join(f"👤 {saved_user_link_with_id(uid)}" for uid in blocked),
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
            lines.append(f"🔇 {saved_user_link_with_id(uid)} — мут ({esc(punishment.get('duration', 'неизвестно'))}{esc(tail)})")
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
                        f'🛡️ <a href="https://t.me/{esc(str(chat_username).lstrip("@"))}">{esc(title)}</a>'
                    )
                else:
                    lines.append(f"🛡️ {esc(title)} (<code>{admin_id}</code>)")
            else:
                lines.append(f"🛡️ {saved_user_link_with_id(admin_id)}")
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
        await message.reply_text(f"🛡️ Права администратора выданы: {label}.", parse_mode=ParseMode.HTML, **NO_PREVIEW)
    else:
        if target_id not in current:
            await message.reply_text("ℹ️ У этого пользователя или чата нет прав администратора.")
            return
        current.discard(target_id)
        data["admins"] = sorted(current)
        data.setdefault("admin_chats", {}).pop(str(target_id), None)
        log_action(user.id, "admin_access_revoked", target_id)
        await message.reply_text(f"🛡️ Права администратора сняты: {label}.", parse_mode=ParseMode.HTML, **NO_PREVIEW)


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
        "💡 <i>Участник — ответ на его сообщение, карточку или @username</i>\n\n"

        "🛡 <b>МОДЕРАЦИЯ</b>\n\n"
        "⚠️ <b>/преды</b> — предупреждения и срок их сгорания\n"
        "🧹 <b>/сп</b> — снять все предупреждения\n"
        "🔇 <b>/зж</b> · <b>/рж</b> — запретить или разрешить жалобы\n"
        "📋 <b>/запреты</b> — кому запрещены жалобы\n"
        "⛔ <b>/наказания</b> — активные наказания\n"
        "🔓 <b>/сн</b> — снять наказание\n"
        "   ↳ <i>⚡ /сн принудительно — если участника уже нет в чате</i>\n"
        "📢 <b>#жалоба</b> причина — ответом на сообщение\n\n"
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

        "👑 <b>ДОСТУП</b> <i>(только владелец)</i>\n\n"
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
            OWNER_ID, f"⚠️ Ошибка в боте: {type(context.error).__name__}: {context.error}"[:500]
        )
    except TelegramError:
        pass


# =====================================================================
# ВИКТОРИНА И DS КОИНЫ
# Владелец включает викторину командой /викторина. Вопросы выходят сами каждые N часов.
# На ответ 5 минут, попытка одна. Первый правильный ответ получает 1 DS коин.
# =====================================================================
# Банк вопросов зашит в код: отдельный файл не нужен и не потеряется при сборке.
QUIZ_BANK = [{'q': 'Игроку нужна Призма Конденсации Ур.12. Какой варп ведёт в нужный мир?',
  'correct': '/warp ice',
  'wrong': ['/warp hell', '/warp infinity', '/warp underworld']},
 {'q': 'Какой моб даёт сырую говядину?', 'correct': 'Корова', 'wrong': ['Свинья', 'Овца', 'Курица']},
 {'q': 'Сколько всего локаций в 2, 3 и 4 мирах вместе?', 'correct': '18', 'wrong': ['16', '19', '20']},
 {'q': 'Сколько всего локаций в 5 и 6 мирах вместе?', 'correct': '8', 'wrong': ['7', '9', '10']},
 {'q': 'Какой инструмент минимально нужен, чтобы добыть алмазную руду?',
  'correct': 'Железная кирка',
  'wrong': ['Деревянная кирка', 'Каменная кирка', 'Золотая кирка']},
 {'q': 'Какая команда ведёт в мир, где находится Люцифер?',
  'correct': '/warp underworld',
  'wrong': ['/warp hell', '/warp ice', '/warp mystic']},
 {'q': 'Какая команда ведёт к Жнецу Всевластия?',
  'correct': '/warp infinity',
  'wrong': ['/warp hell', '/warp mystic', '/warp obsidian']},
 {'q': 'Какая команда ведёт в мир, который идёт сразу после 3 мира?',
  'correct': '/warp ice',
  'wrong': ['/warp hell', '/warp mystic', '/warp infinity']},
 {'q': 'Какой блок нужен для плавки железной руды?',
  'correct': 'Печь',
  'wrong': ['Верстак', 'Наковальня', 'Сундук']},
 {'q': 'Сколько локаций суммарно в 1 и 6 мирах?', 'correct': '24', 'wrong': ['22', '25', '26']},
 {'q': 'Какой материал нужен для создания каменной кирки?',
  'correct': 'Булыжник',
  'wrong': ['Железный слиток', 'Золотой слиток', 'Алмаз']},
 {'q': 'Где можно найти Призму Конденсации Ур.8?', 'correct': 'Лава', 'wrong': ['Цербер', 'Демон', 'Покор']},
 {'q': 'Где можно найти Призму Конденсации Ур.9?',
  'correct': 'Цербер',
  'wrong': ['Покор', 'Soul Reaper', 'Лава']},
 {'q': 'Какой блок светится в темноте?',
  'correct': 'Светокамень',
  'wrong': ['Песчаник', 'Камень', 'Обсидиан']},
 {'q': 'Какой моб ночью на поверхности стреляет стрелами?',
  'correct': 'Скелет',
  'wrong': ['Зомби', 'Паук', 'Крипер']},
 {'q': 'В каком мире можно найти Призму Конденсации Ур.14?',
  'correct': '5 мир',
  'wrong': ['3 мир', '4 мир', '6 мир']},
 {'q': 'На какой локации получают Алмазную Кирку VI?',
  'correct': 'Падший Ангел',
  'wrong': ['Разрушитель Миров', 'Повелитель Небес', 'Королева Эльза']},
 {'q': 'На какой локации 5 мира получают Незеритовую Кирку?',
  'correct': 'Разрушитель Миров',
  'wrong': ['Падший Ангел', 'Последний Воин', 'Жнец Всевластия']},
 {'q': 'Какая локация 3 мира даёт переход с Золотой Кирки III на Алмазную Кирку I?',
  'correct': 'Демон',
  'wrong': ['Лава', 'Покор', 'Цербер']},
 {'q': 'Какая локация 2 мира даёт переход с Железной Кирки III на Золотую Кирку I?',
  'correct': 'Дракон',
  'wrong': ['Визер', 'Кальмар', 'Посейдон']},
 {'q': 'Сколько талисманов получится, если выфармить каждый из начального набора по два раза?',
  'correct': '8',
  'wrong': ['4', '6', '10']},
 {'q': 'Где находится NPC, у которого получают первые талисманы?',
  'correct': 'Спавн рядом с порталом на /warp obsidian',
  'wrong': ['/warp ice', '/warp underworld', '/warp hell']},
 {'q': 'Что нужно увидеть справа, чтобы найти NPC Улучшенного талисмана на /warp obsidian?',
  'correct': 'NPC в виде чешуйницы',
  'wrong': ['Шахту', 'Портал', 'NPC «Талисманы»']},
 {'q': 'Что делает жемчуг Края при броске?',
  'correct': 'Телепортирует владельца в место приземления',
  'wrong': ['Лечит владельца', 'Даёт невидимость', 'Ускоряет движение']},
 {'q': 'Для чего нужны два улучшенных талисмана?',
  'correct': 'Для получения следующего талисмана',
  'wrong': ['Для входа во 2 мир', 'Для продажи', 'Для ремонта брони']},
 {'q': 'Какой блок нужен для рамки портала в Незер?',
  'correct': 'Обсидиан',
  'wrong': ['Алмазный блок', 'Камень', 'Песок']},
 {'q': 'Какой моб взрывается, подходя к игроку?',
  'correct': 'Крипер',
  'wrong': ['Зомби', 'Эндермен', 'Призрак']},
 {'q': 'Какие талисманы выдаёт NPC «Талисманы» в 3 мире?',
  'correct': 'Кольцо Демона и Люцифера',
  'wrong': ['Ледяная Душа и Божественный Дар',
            'Дракон Разрушителя и Сфера Опустошения',
            'Талисман скорости и Талисман жизни']},
 {'q': 'Какой ориентир помогает найти проём к NPC Дракона Разрушителя?',
  'correct': 'Блок изумруда снизу и блок угля справа',
  'wrong': ['Блок угля снизу и блок изумруда справа',
            'Блок золота снизу и блок угля справа',
            'Блок изумруда снизу и блок железа справа']},
 {'q': 'Как выглядит строение, где находится NPC Рыцаря Пустоты?',
  'correct': 'Напоминает фиолетовое пламя',
  'wrong': ['Напоминает красную башню', 'Жёлтый домик', 'Зелёный дом']},
 {'q': 'Куда повернуть от NPC Рыцаря Пустоты, чтобы найти дерево со Сферой?',
  'correct': 'Налево',
  'wrong': ['Направо', 'Вперёд', 'Назад']},
 {'q': 'Как попасть внутрь дерева со Сферой Опустошения?',
  'correct': 'Подлететь, обойти и найти вход',
  'wrong': ['Сломать ствол', 'Ждать открытия', 'Найти NPC снаружи']},
 {'q': 'Какая башня в замке Эльзы выдаёт талисманы?',
  'correct': 'Правая с бордовой крышей',
  'wrong': ['Левая с бордовой крышей', 'Правая с жёлтой крышей', 'Центральная с синей крышей']},
 {'q': 'Какие два талисмана выдаёт NPC в правой башне замка Эльзы?',
  'correct': 'Ледяная Душа и Божественный Дар',
  'wrong': ['Дракон Разрушителя и Сфера Опустошения',
            'Талисман скорости и Талисман жизни',
            'Талисман урона и Супер талисман']},
 {'q': 'Куда нужно лететь, чтобы найти NPC Рыцаря Пустоты в 6 мире?',
  'correct': 'Вниз',
  'wrong': ['Вверх', 'Вперёд', 'Назад']},
 {'q': 'Какого цвета крыша у домика с NPC «Талисманы» в 3 мире?',
  'correct': 'Жёлтый',
  'wrong': ['Бордовый', 'Красный', 'Синий']},
 {'q': 'Какой предмет нужен, чтобы активировать портал в Энд?',
  'correct': 'Глаз Эндера',
  'wrong': ['Жемчуг Края', 'Огненный порошок', 'Кость']},
 {'q': 'Сколько ячеек в основном инвентаре и хотбаре вместе?', 'correct': '36', 'wrong': ['27', '40', '45']},
 {'q': 'Какое животное даёт шерсть?', 'correct': 'Овца', 'wrong': ['Корова', 'Свинья', 'Курица']},
 {'q': 'Сколько улучшенных талисманов нужно для следующего талисмана?',
  'correct': '2',
  'wrong': ['1', '3', '4']},
 {'q': 'Игрок продал аккаунт. Какое наказание?',
  'correct': 'Перманентная блокировка аккаунта',
  'wrong': ['Мут на 1 день', 'Блокировка на 20 дней', 'Предупреждение']},
 {'q': 'Игрок написал пароль в шутку. Сколько часов блокируют игровой чат?',
  'correct': '12 часов',
  'wrong': ['1 час', '6 часов', '24 часа']},
 {'q': 'Игрок создал мультиаккаунт ради выгоды. Какой срок блокировки аккаунта и IP?',
  'correct': 'От 1 до 20 дней',
  'wrong': ['От 1 до 7 дней', '30 дней', 'Навсегда']},
 {'q': 'Игрок использует VPN, но его IP не блокирован хостингом. Какое наказание?',
  'correct': 'Блокировка от 1 до 30 дней',
  'wrong': ['Разрешено', 'Мут на 1 день', 'Предупреждение']},
 {'q': 'Какое наказание за распространение личной информации игроков?',
  'correct': 'Перманентная блокировка аккаунта',
  'wrong': ['Предупреждение', 'Мут на 1 час', 'Кик с сервера']},
 {'q': 'Какое наказание за читы, если это уже четвёртое нарушение?',
  'correct': 'Бан на усмотрение администрации',
  'wrong': ['Бан на 3 дня', 'Бан на 7 дней', 'Предупреждение']},
 {'q': 'Что можно использовать как топливо в печи?',
  'correct': 'Уголь',
  'wrong': ['Песок', 'Булыжник', 'Золотой слиток']},
 {'q': 'Игрок продаёт коины за донат без участника команды проекта. Разрешено?',
  'correct': 'Нельзя',
  'wrong': ['Разрешено всегда', 'Разрешено только в ЛС', 'Разрешено в клане']},
 {'q': 'Игрок отправил в чат три одинаковых сообщения. Это спам?',
  'correct': 'Да, от трёх одинаковых сообщений',
  'wrong': ['Нет, спам начинается с пяти', 'Нет, спам только в ЛС', 'Да, но только со ссылкой']},
 {'q': 'От скольких символов считается флуд символом?', 'correct': '15', 'wrong': ['10', '12', '20']},
 {'q': 'Игрок отправил ссылку на свой YouTube-канал. Наказание?',
  'correct': 'Блокировка чата от 10 минут до 3 часов',
  'wrong': ['1 день', 'Предупреждение', '30 дней']},
 {'q': 'Можно ли отправить ссылку на Discord-сервер DestroyCraft?',
  'correct': 'Да',
  'wrong': ['Нет никогда', 'Только медиа', 'Только в ЛС']},
 {'q': 'Игрок оскорбил персонала. Какая блокировка чата?',
  'correct': '1 час',
  'wrong': ['10 минут', '3 часа', '1 день']},
 {'q': 'Игрок оскорбил родителей другого игрока. Срок наказания?',
  'correct': 'До 3 часов',
  'wrong': ['1 день', '30 дней', 'Навсегда']},
 {'q': 'Когда принимаются скриншоты с телефона?',
  'correct': 'При полном обзоре монитора',
  'wrong': ['Всегда', 'Никогда', 'Только видео']},
 {'q': 'Сколько дней актуальны доказательства на мут?',
  'correct': '3 дня',
  'wrong': ['1 день', '7 дней', '14 дней']},
 {'q': 'Сколько дней актуальны доказательства на бан?',
  'correct': '7 дней',
  'wrong': ['3 дня', '14 дней', '30 дней']},
 {'q': 'Сколько минут реального времени длится один игровой день в Minecraft?',
  'correct': '20 минут',
  'wrong': ['10 минут', '24 минуты', '30 минут']},
 {'q': 'Можно ли намеренно подставиться под удар игрока с сетом ниже на два мира, чтобы получить право '
       'ответить?',
  'correct': 'Нет, это обход правил',
  'wrong': ['Да, если это в 1 мире', 'Да, если он в клане', 'Да, если вы не на спавне']},
 {'q': 'Что удаляют за ботерство рейтинга?', 'correct': 'КР/БР', 'wrong': ['Коины', 'Инвентарь', 'Аккаунт']},
 {'q': 'Срок бана за ботов для фарма вне спавна?',
  'correct': 'От 3 до 12 часов',
  'wrong': ['1 день', '30 минут', '7 дней']},
 {'q': 'Где по правилам фармить AFK-монеты?',
  'correct': '/warp afk',
  'wrong': ['/spawn', '/warp ice', '/c top 1']},
 {'q': 'Во 2 мире и выше разрешён мат?',
  'correct': 'Умеренно, если не направлен на оскорбление',
  'wrong': ['Без ограничений', 'Нет, полный запрет', 'Только в ЛС']},
 {'q': 'Игрок написал политический скин, первое нарушение. Что получит?',
  'correct': 'Предупреждение в чате',
  'wrong': ['Блокировка на 3 часа', 'Перманентная блокировка', 'Мут на 10 минут']},
 {'q': 'Игрок вышел из сервера во время проверки. Можно ли разблокировать?',
  'correct': 'Нет, «крашнул майн» не основание',
  'wrong': ['Да, если был краш', 'Да, если был АФК', 'Только по решению куратора']},
 {'q': 'Можно ли очищать корзину во время проверки?',
  'correct': 'Нельзя',
  'wrong': ['Можно', 'Только по просьбе проверяющего', 'Можно после проверки']},
 {'q': 'Проверяющий просит включить веб-камеру. Что делать?',
  'correct': 'Отключиться и сообщить куратору',
  'wrong': ['Включить камеру', 'Закрыть игру', 'Ничего не делать']},
 {'q': 'Из чего создают факел?',
  'correct': 'Палка и уголь',
  'wrong': ['Палка и камень', 'Доска и уголь', 'Песок и палка']},
 {'q': 'Куда подать жалобу на модератора?',
  'correct': 'Жалоба на администрацию',
  'wrong': ['Жалоба на Медиа', 'Общий чат', 'В личные сообщения']},
 {'q': 'Игрок выполнял плагиат топ-10 клана. Какое наказание владельцу клана?',
  'correct': 'Блокировка от 1 часа',
  'wrong': ['1 день', '30 дней', 'Предупреждение']},
 {'q': 'Какое наказание за спам командами в чат?',
  'correct': 'Блокировка 10–30 минут',
  'wrong': ['1 час', '1 день', 'Предупреждение']},
 {'q': 'Какое наказание за помеху PvP или /vanish для получения ресурсов?',
  'correct': 'Блокировка на 1 час',
  'wrong': ['10 минут', '1 день', '30 дней']},
 {'q': 'Первое нарушение правила сетов. Сколько длится бан?',
  'correct': '30 минут',
  'wrong': ['3 часа', '12 часов', '1 день']},
 {'q': 'Срок блокировки за обход мута через /er?',
  'correct': 'От 6 часов до 1 дня',
  'wrong': ['30 минут', '7 дней', 'Навсегда']},
 {'q': 'Срок блокировки за подделку доказательств?',
  'correct': 'От 1 до 30 дней',
  'wrong': ['1 час', '3 часа', 'Навсегда']},
 {'q': 'Срок блокировки чата за выдачу себя за команду проекта?',
  'correct': '3 часа',
  'wrong': ['30 минут', '1 день', '7 дней']},
 {'q': 'Срок блокировки за обман команды проекта?',
  'correct': 'От 6 часов до 1 дня',
  'wrong': ['1 час', '30 дней', 'Навсегда']},
 {'q': 'Срок блокировки за подстрекание других на нарушение правил?',
  'correct': '1 день',
  'wrong': ['1 час', '3 дня', '7 дней']},
 {'q': 'Что такое ЧСП на сервере?',
  'correct': 'Чёрный список проекта',
  'wrong': ['Список привилегий', 'Список команд', 'Список сетов']},
 {'q': 'Что означает символ «*» перед пунктом правил?',
  'correct': 'За этот пункт банить может только Модерация или Администрация',
  'wrong': ['Пункт отменён', 'Пункт обязателен только для медиа', 'Пункт действует только на спавне']},
 {'q': 'Что будет, если жалоба не рассмотрена в течение 3 дней?',
  'correct': 'Она сохраняет актуальность и рассматривается в обычном порядке',
  'wrong': ['Теряет актуальность', 'Закрывается автоматически', 'Переносится на месяц']},
 {'q': 'Обязана ли Модерация предоставлять доказательства по запросу нарушителя?',
  'correct': 'Нет, не обязана',
  'wrong': ['Да, всегда', 'Только по жалобе', 'Только в суде']},
 {'q': 'Может ли Администрация изменить игровые вещи, полученные нечестно?',
  'correct': 'Да',
  'wrong': ['Нет', 'Только валюту', 'Только на спавне']},
 {'q': 'Куда подать жалобу на сотрудника Медиа?',
  'correct': 'В раздел «Жалоба на Медиа»',
  'wrong': ['В раздел «Жалоба на администрацию»', 'В общий чат', 'В личные сообщения']},
 {'q': 'Принимаются ли жалобы от игрока, который в ЧСП?',
  'correct': 'Нет',
  'wrong': ['Да', 'Только на Медиа', 'Только при оплате']},
 {'q': 'Кто ведёт логи всех действий игроков и сообщений чата?',
  'correct': 'Администрация',
  'wrong': ['Медиа', 'Игроки', 'Бот']},
 {'q': 'Может ли Администрация изменить правила без предварительного уведомления?',
  'correct': 'Да',
  'wrong': ['Нет, за неделю', 'Только с объявлением', 'Только медиа']},
 {'q': 'Сколько досок нужно, чтобы создать верстак?',
  'correct': '4 доски',
  'wrong': ['2 доски', '8 досок', '4 палки']},
 {'q': 'Какой мир идёт сразу после 5 мира по команде?',
  'correct': '/warp infinity',
  'wrong': ['/warp hell', '/warp ice', '/spawn']},
 {'q': 'Какой варп ведёт в мир, где находится Ледяной Дух?',
  'correct': '/warp ice',
  'wrong': ['/warp infinity', '/warp mystic', '/warp underworld']},
 {'q': 'Может ли игрок с Лунным сетом (1 мир) драться с игроком с Обсидиановым сетом?',
  'correct': 'Да',
  'wrong': ['Нет', 'Только на спавне', 'Только во 2 мире']},
 {'q': 'Может ли игрок с Аметистовым сетом драться с игроком с Обсидиановым сетом в 1 мире?',
  'correct': 'Нет',
  'wrong': ['Да', 'Только на спавне', 'Если оба в клане']},
 {'q': 'Какой минимальный сет для PvP во 2 мире?',
  'correct': 'Кометный',
  'wrong': ['Драконий', 'Соул', 'Лунный']},
 {'q': 'Какой минимальный сет для PvP в 3 мире?',
  'correct': 'Драконий',
  'wrong': ['Кометный', 'Соул', 'Ледяного Духа']},
 {'q': 'Какой минимальный сет для PvP в 4 мире?',
  'correct': 'Соул',
  'wrong': ['Драконий', 'Ледяного Духа', 'Последнего Воина']},
 {'q': 'Какой минимальный сет для PvP в 5 мире?',
  'correct': 'Ледяного Духа',
  'wrong': ['Соул', 'Последнего Воина', 'Драконий']},
 {'q': 'Какой минимальный сет для PvP в 6 мире?',
  'correct': 'Последнего Воина',
  'wrong': ['Ледяного Духа', 'Соул', 'Драконий']},
 {'q': 'К какому сету относится улучшенный талисман?',
  'correct': 'Кометный',
  'wrong': ['Драконий', 'Соул', 'Лунный']},
 {'q': 'Что нельзя делать на начальном острове нового мира?',
  'correct': 'Убивать игроков, пока они не получили первый предмет нового сета',
  'wrong': ['Строить дома', 'Торговать', 'Использовать /spawn']},
 {'q': 'Как работает PvP на точке бустеров?',
  'correct': 'Только между игроками того мира, в котором находится точка',
  'wrong': ['Все могут драться друг с другом', 'Только игроки с Лунным сетом', 'Запрещено полностью']}]

QUIZ_INTERVAL = timedelta(hours=_env_int("QUIZ_INTERVAL_HOURS", 8))
QUIZ_ANSWER_TTL = timedelta(minutes=5)
QUIZ_LETTERS = "АБВГ"


def quiz_bank():
    return QUIZ_BANK


def quiz_state():
    return data.setdefault("quiz", {"enabled": False, "next_at": None, "used": [], "current": None, "round": 0})


def ds_balance(user_id):
    return int(data.get("ds_coins", {}).get(str(user_id), 0))


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
        "🧠 <b>Викторина</b>\n\n"
        f"<b>{esc(item['q'])}</b>\n\n"
        + "\n".join(f"{QUIZ_LETTERS[i]}) {esc(o)}" for i, o in enumerate(options))
        + "\n\n⏳ На ответ 5 минут. Попытка одна."
    )
    keyboard = InlineKeyboardMarkup([[
        InlineKeyboardButton(QUIZ_LETTERS[i], callback_data=f"qz:{rid}:{i}") for i in range(len(options))
    ]])
    message = await context.bot.send_message(
        MAIN_CHAT_ID, text, parse_mode=ParseMode.HTML, reply_markup=keyboard, **NO_PREVIEW,
    )
    st["used"] = list(used | {qid})
    st["current"] = {
        "round": rid, "message_id": message.message_id,
        "correct": options.index(item["correct"]),
        "deadline": (now_utc() + QUIZ_ANSWER_TTL).isoformat(),
        "attempted": [],
    }
    save_data()
    return True


async def quiz_close_round(context):
    """Закрывает текущий раунд: убирает кнопки, ответ в чат не выводит."""
    st = quiz_state()
    cur = st.get("current")
    if not cur:
        return
    st["current"] = None
    save_data()
    try:
        await context.bot.edit_message_reply_markup(
            chat_id=MAIN_CHAT_ID, message_id=cur["message_id"], reply_markup=None,
        )
    except TelegramError:
        pass  # сообщение уже удалено или старое


async def quiz_tick(context):
    st = quiz_state()
    if not st.get("enabled"):
        return
    now = now_utc()
    cur = st.get("current")
    if cur:
        if now >= parse_dt(cur["deadline"]):
            await quiz_close_round(context)
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
        await quiz_close_round(context)
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
        f"▶️ Викторина включена. Новый вопрос каждые {int(QUIZ_INTERVAL.total_seconds() // 3600)} ч."
    )


async def quiz_callback(update, context):
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
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
        await quiz_close_round(context)
        return
    if str(user.id) in cur["attempted"]:
        await query.answer("Ты уже использовал попытку на этот вопрос", show_alert=True)
        return
    cur["attempted"].append(str(user.id))
    if idx != cur["correct"]:
        save_data()
        await query.answer("❌ Неверно. Попытка использована.", show_alert=True)
        try:  # владелец видит неверные нажатия в личке, в чат ничего не пишем
            await context.bot.send_message(
                OWNER_ID,
                f"🔘 {mention_user(user)} выбрал {QUIZ_LETTERS[idx]} — неверно "
                f"(правильный {QUIZ_LETTERS[cur['correct']]})",
                parse_mode=ParseMode.HTML, **NO_PREVIEW,
            )
        except TelegramError:
            pass
        return
    await query.answer("✅ Верно! Ты ответил первым.", show_alert=True)
    coins = data.setdefault("ds_coins", {})
    coins[str(user.id)] = ds_balance(user.id) + 1
    log_action(user.id, "quiz_win", user.id, details=f"викторина, раунд {rid}")
    await quiz_close_round(context)
    await announce(
        context,
        f"🏆 {mention_user(user)} ответил первым и получает <b>1 DS коин</b>",
    )


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
        text = f"💰 Твой баланс: <b>{ds_balance(user.id)} DS коинов</b>"
    else:
        text = f"💰 Баланс {saved_user_link(target_id)}: <b>{ds_balance(target_id)} DS коинов</b>"
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
        f"💰 Баланс: <b>{new_balance}</b>",
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


async def coins_top_command(update, context):
    message = update.effective_message
    if not message:
        return
    top = sorted(((int(uid), int(v)) for uid, v in data.get("ds_coins", {}).items() if int(v) > 0),
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
        "🏆 <b>Топ DS коинов</b>\n\n" + "\n".join(lines),
        parse_mode=ParseMode.HTML, **NO_PREVIEW,
    )


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
    application.add_handler(CallbackQueryHandler(quiz_callback, pattern=r"^qz:"), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=[MAIN_CHAT_ID, ADMIN_CHAT_ID])
        & filters.Regex(r"(?i)^/баланс(?:@\w+)?(?:\s|$)"), balance_command), group=0)
    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.Regex(r"(?i)^/топкоинов(?:@\w+)?(?:\s|$)"),
        coins_top_command), group=0)

    ROUTES["/викторина"] = quiz_command  # регистрируем здесь: функция объявлена ниже ROUTES
    ROUTES["/выдатькоины"] = grant_coins_command
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
    register_all_handlers(application)

    cleanup_expired()
    logger.info("Единый бот заявок и модерации запущен.")
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
