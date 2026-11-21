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


# Какие обычные эмодзи заменяем кастомными, если такой значок уже создан в наборе бота
CUSTOM_EMOJI_MAP = {
    "🦊": "fox", "✏": "pencil", "🏷": "name_tag", "🌱": "sprout", "🎁": "gift",
    "🪙": "coins", "🎭": "masks", "🍂": "autumn_leaves", "❤": "heart", "👑": "crown",
    "💬": "chat", "🥉": "medal_bronze", "🥈": "medal_silver", "🥇": "medal_first",
    "⭐": "star", "🛍": "bag", "🗣": "shout",
    "❌": "cross", "✅": "check", "⏳": "hourglass", "ℹ": "info", "🔔": "bell",
    "⛔": "noentry", "❗": "exclaim", "📝": "scroll", "🏆": "trophy",
    "🎟": "ticket", "◀": "triangle", "🏁": "flag", "🔄": "refresh", "🎉": "party",
    "🔓": "unlock", "📋": "clipboard", "👥": "people", "🎮": "gamepad", "🔗": "chain", "👮": "cap",
}


def add_custom_emoji_entities(plain, entities):
    """Заменяет обычные эмодзи на кастомные там, где значки уже созданы. Остальные эмодзи не трогаем."""
    ids = data.get("custom_emoji", {}) if data else {}
    if not ids:
        return entities
    covered = [(e.offset, e.offset + e.length) for e in entities if e.type == "custom_emoji"]
    result = list(entities)
    i = 0
    while i < len(plain):
        ch = plain[i]
        key = CUSTOM_EMOJI_MAP.get(ch)
        if key and ids.get(key):
            seq = ch
            j = i + 1
            if j < len(plain) and plain[j] == "\ufe0f":
                seq += plain[j]
                j += 1
            offset = _utf16_len(plain[:i])
            length = _utf16_len(seq)
            if not any(offset < end and start < offset + length for start, end in covered):
                result.append(MessageEntity(type="custom_emoji", offset=offset, length=length,
                                            custom_emoji_id=ids[key]))
                covered.append((offset, offset + length))
            i = j
            continue
        i += 1
    return result


def html_to_entities(text):
    parser = _HtmlToEntities()
    parser.feed(text)
    parser.close()
    return parser.plain, add_custom_emoji_entities(parser.plain, parser.entities)


CMD_MSG_IDS = {}  # id команд в основном чате -> время, чтобы удалить ответы бота на них


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
        reply_to = kwargs.get("reply_to_message_id")
        kwargs = self._convert({"text": text, **kwargs}, "text", "entities")
        text = kwargs.pop("text")
        sent = await super().send_message(chat_id, text, *args, **kwargs)
        if chat_id == MAIN_CHAT_ID and reply_to in CMD_MSG_IDS:
            schedule_delete(self, chat_id, sent.message_id, 1800)
        return sent

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
        JOIN_BATCH["task"] = spawn_task(join_batch_flush(context))


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
    spawn_task(set_public_commands(application.bot))
    spawn_task(notify_interrupted_mafia(application.bot))
    spawn_task(set_bot_descriptions(application.bot))
    _background_task = spawn_task(background_loop(application.bot))


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
    spawn_task(delete_later(context.bot, [(MAIN_CHAT_ID, cur["message_id"])], 60))


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
    "autumn_leaves": "iVBORw0KGgoAAAANSUhEUgAAAGQAAABkCAYAAABw4pVUAAAzXUlEQVR42u29d5heV3Xv/1n7nPP26Rp1WdVNkuVeAXcwYAI2MDJgkh+5CSXABRKScCHcjOWEOIUWQi8XUmga5+LQE4olF7nbctHY6n1G02fefsre6/5x3rFlEh7klvbT0jOPnhlpZs67V/+u79ovHJfjclyOy3E5LsfluByX43Jc/guKtD6Oy3H5/5H0g7n1EvyNfXi/7P+cDcGFPZx7RienHz+xF1ARCuZYg9DZEFwC/vGTewFkI3izingPrNu4hPd+8zTzpuMH/u8sCqItZfw2LN/Yzle3vjk7U/lOp2673tcPeVwNyEZ+efj6ryrmP6NXiKAC9pPK6379Qv+OK/+q+JY1r/cCf0t9Zm6n0wUL5DWA0nfceF/QcnXWK34DFv1jD1/d/ofdSXznvKT+sWx17Hwaw+ukXnurJBvXyd7ToKsVzo6XuM81HP1bidsIIMInoW/Ledl9lYETNL5zSW1yfdAYOZ1w9MWEh88nrL5OGvdeJvpWePWTeeZ4yHqWyujHiKCqSH/rd98K/gbBOSX4Vkb//Ko3lr59zhdWLvKqYXXyvQdNtCs2tINqqrDmDLqsS1nZxcv/Oxqs/++qjA3iQAsi1EkV44lIcqPqiRecIJ8+430LX9ZzVbFe/exewtsagZQQDGChpQ+imppCT4fmS9GlTDXy10GjFbb0uEKOVRmKiOC+OV9/Z+1L2z8wsbO5/Y67ow+K4cH/E+jb153r/+naDUvmBEVTr/7xHi/el4h0Cy5RUDACruXOkUWCuBT3dAYrLzy4b+1dcF8fmAGwL0QPtKYPYeDpX992lPI3pI/2X0YhoiAi6LcW8MHz3zn/T064pstw3/6l2SBZs+4Rd9sZ6wtvnPfuTmcemmqEX532MUCboIkCiBEkm4MwAuvAGDSuVpNT5p2WX7PrwIvuarj7Vr8AiT31aNwvKuNflRHPs1/KCx+mcN87VW44730r+3uu9KrJTTs9UwJ7sp9xYcHLvbwzjL88hNwXSZwTGrFCgqCpZxmBtjaoNyCKBIcSeCZptF2c+/w9D9z8kfFK31FO9HwZEQL6FlhyRgcXxAYvinBRTORb6kOWqZ1QrUL5bjj8X8JD+sHIjbj3wAkLziy8e84lptm8aZfnjTjPjoBOxDZ7XpTEf3LQ45BVLaHGKjiMIniAE8XPCEYg4ytRpBgjRIkzflRhbkfvaYxXCkakjupzziP9YDaAE+DLZ/rnnLzSfHrZKe48W3dJEmGSJmLA1Zs061YalQmJH97mPviHh93fbQRv/fMQNl+wKmtNX2rlpxV5+4IL8j32RwcSOWiNtoEUQcpK8n/rxkxYTBuiiQgWAk9QBaugCBkfnFOMQBAIakVdAoHWw6Xzlp74ax4Xq0Lfc3wtG8G70cOdDR133jDvS6/9Xx0/O+c8d/qCqm0sbbp4eaLhiZ5rrMy4cHWbehcu1Px83MLRGZf9r1D2ynUD2JdDduFSubbjjLyC9aWISCvuKiAlgaD1eZoyCLw06TgHnqd4HuBaD2oVnKpvgMZht7DQbRYXg5c916b91kvw14N9kaVr/Ynmlp626m+3Hax47s7ERfvVj4bx7RH1kzH85iHxwn1Qf8Rl7n9CR+6o8sNfTPT/6UJWP8gG0IvgpEVn5pfnOiS22cSYEpCAS0AjwaJ4kiZrVVXPpME740OoaFAUUNQ6RAQCH4kTFVXRJC5Le6mmS3rmn035oHediH02YUtBZDPJBris7w86/rx7sTu3e6haiXeoZ/w0fKqXlooaIi6EjI/dH3r5bQ023409/HzmMPNc4q3+kqLg0kswICzNcsGil3TkvHLdkgW6BBLQOP02q6KJA1RUJA1VXqoDHpiEJIuqBaeoU9SYtNFXBKdIMRqJuvLdp5wCK7VlCM84z4H+zWLzrte8rfTdE68snjPHhvVovwbiYWyCJLFiQ3B1gSj9BRkRHhwTdlftNwEufR4jzbP+QRsQJyK6sQ+vBV88eRiXbkpbufmny6s7V2ewozXwPZhvcEna6BmTfqkai8aqKkaxgC+4fRPocF0161IT9jzwjBgFEVRFFRXENA/GXcG87qWGi1AYfAYK2QjeBnB/2c7bX9mX+/TpV2a85CdDzfhA5IcNpDYtJowQFZBYEU1dIOuT7KuY3H0j7uGtDX4MyObnsQd6dgoR+EiPnvKbqr3rB7DrBSuCbgSvH4wY9HpYPP9U73wj5cRNR0YMSGF24N0C2FEOTqMHZgRjUnOtNOGRSfTkpVDIp69UDKJWIRaMEURARfB0ipWloszrWHQuKKvpP9ZwJX3p+frLlso75pdCbX53EntEfDctkjQQNUq2AwJpaVkBi2qs7tb9yuPT7m/2Q7NVTDxv3cgzyiEb+/DWD4j95BJ91XkvX/SNq7KMvOynQ99/4nH9zgbYsh4SVQTB78hwescJ2mNmKs140vl0GkQUaQd3JDWFZiSECUzVlc68yOKSsrMi+mgTzp0PsdX0HGLQBMQoniJRIhqI0nB57jsyJWNhZcGTffMx5jgB9zZYNXcuJ2Ujl0QRnhek4SlTFNRCc0xxNi27jYF8IDpWyWS3Tdod046NgAz8R3bqvaOpseSrnLj4nHltS64pmBUv9953+t3ld637l/ojgw9GXxDhG0Dtb0qcnZ9njJ1R1aZiZhzGQ3ShICOqjUiYrEFiFYOwbxKZl0W3joOfg/lZCKfT0pcEETdrhqqBUcLE07uOXM62mRkp18u3gDCIyjOIDG5BG+fNXyAFr+YaKJ60vNTVlLie/r7YphEhdsq4DZLH7Emlx5K9/7CFaqUPvOcbsnlWVVYpgwTBqCY7a7YtG9a6XpfzVryk/eyz70m+eO6t1fc+cHeyMTT8Ws5z1o2qZwxITJqSI1AVKpHi0qpAARqRcvt+2DKsnH0qdOVhZljQMDVnY0QTpxgRrBruH3lJcijqKU0kdwzcCX/Xzx+bDWw4psNZ04cyAHN65Py5c5VkHPwiJCHUhyGJU5WpA8+oViP04HgmeXCmvfRgcuTWoXr1c7NN5H8CcFHxcwR+wQmNWOxY6NtyIiarzaWX5fSE0zJrVpzBhr0PapwtaKKTziCt/sOBToLnqXQUoObAR2g6VVHY10QqoCcXobkXbB2Mp+IUVVBVIcaxZWSlHghX+w81fjTxSH3yQ2mU3/C0UnagD7N+APdvxffrbsYCZuEiTu2aY2xUttqYQOOR1HV8H7GtCmJohmTnRIfuaeZKD4Uz/3RzrXk9UHv0BUKYn5FCLp2bPkA5IWNtDJEVYhUpGBHFiw41kfGkeeK5RpdfGhg3HgsWxEszo8agdXUKksuIeHko1mCyieQMjDRhYSdy0hyj4bBDUJxNo5Z4QuAJ/3wI2T4zzx6M780PNvbe9Diy6xLU3wDJU6WsOAbE/lsGnJ4zenaJbgnMyY9sxdvzmBSaNVQNzkOdqKiIasnP2OF6T+7+St0MxeOfOti0vy9IrKih9cMVZD2Y1Zc8vcJbsxntS2EYfcEUMgt8hlDEN6CIQSBSoSApV8dioiMO8UJ0t2ByBulB1apqA1xTUFTVpU9bzApeWQkTGGnA+SuMlAKRiuKQNGwoMNWAHTOWA9Nrbehn8vdU775zq5MNoGwCK61Sdj1iP4j2Lm7XMz9z1epNjw8MRnqUNQvpgOyGs5m++wn9xE/vdleFPh1NI/N9oaRWgqyQyRsJir5ky1F128565YafWG5uqVQUdKAPr2/gyQO3bP7lhdC2AfRYw9uzyiHZgC4/cOnrM4I4p9oUkaYDVWM8ASO4STQaU/VOhuwJQlRRiJlt7DQTQDZQenKwuyzUUFk5V9FqCtpnfNV6KOyZgj1VxxPlLKX8ybK1fG+NKP7hpZjre0saSpV/VDAixvZ77uKXXt375ZUXn3Fix+d+8q03I2/US9TbBIzNRfuATaPImrno+s3uoxg+yq/hnTKgnSUo1CHbGVDKKW1xEgY7CO8ZgVo/mMGU6aICjoE0mV9VYMGqNk7uzbLSKCUDEiXUqk0OPDrFQ+sHGD0auHxeFdK3OrWybIa8AXVjTjV0mHYfRhKI0s4OC5oomqjYUHTsLihOKd05JbSStpEKakBE6c3BHRNoZwlZmhcaY4oxIpMNODilOtMQ9pfBuQ4dto+zYv5Bd+1i84Fl8yUntXZv4b2Vz8qEvOeviu7151+86Ktn3HRTqXhqo37e1Ngb/vITW++QzXzml04dHHAz9gnDBDABQPz0KNMH3po0S1kB/mghS+ZkuKyU4Zp8lgs7MvR2ZvFKWchmoanCTAgXVRh61bj+YOc0N22YYe+xKOWZhazB9JUkCUmyuypSip0tO8QmmKaihwSZa6AdjFWqdZiqQqRQ3ga1TsOCbIokqgIqFHzYESHb6ypnrRDm5QwzzrKnohyYQjKg44myuBNW9k6xbN2EthclkCYajrvQ+W1m55J57/zd8s7iSy9fds3az32tpO7rjWjLP3kr3/266Ly9Ux/569uHX+JlTV2jMMo5rRDppIup24ioFhLVY8pjypEyTG6DygMw0g/xYKvPGAA7ALxvHmtO7OB/dgS8bG5RFnUX8AqBxp5KA0V7Siq5LBLklUyHERvQOzykb731IV79RyXetOEwP/9VSnlG2M9s3f27WS674ky+f+VbPaXmfM+IEKthV3rIzIHYwf5bHc26qBjUOpHRSHVOEc6aL8RWSZziq8jf7oAfHVZ55xWGl3YKWx92HKwq4gudJdUTukUXdhp8dTRCtF5B602k0lQ1hSLj8VLVjkr+om9/K9H4ZtXd3wA/p9LWprbnahNPTgaaRGjUgDAhiUHDJq46Tlyt0qw4anUXaT2plKcq4cN3T/7o3ffbd6YBFtaDOXel+d1FeX1Pm8cc66irwZWyeB059UXFdOaRzpx6QQFjfPBzqN8rZBZ5ydRjtnjLJhm944g77yvTHJjNZc9HUrcbwVsfcmvpIT5zyhb3BysvlHqc4IuTdHqTKGZCiaYgaYLnI84iqNLjqTwxhuvICSd2C0lTsYrsrUM2g/qTKrfucsQKJy4X5hSVoo9IqFKfsi5JwIART/ADpSNjdGKqhjfnCOu+9sWmNr9sdO/NRrJz0+Q7PYEZ+orL+35TggDjBZDJQDGj5HLgKi0UzgA5oRgUk4O5nr23T7yko4OCKTOtivmzlfJX7QHvsyrlkYZaoKOYwc+lZXvcUyLsLpA4g/Fy4BVBAxGXF8LEBV0LpPbiVTr30DRvE/ij/vTck+clqfeR9nPnhPzlmru0b4Gvi1khNiiBswpOsCrkClDIK7WGpnUrEIgwN6ty5wGnbZ4wvyRsnxKGao5FBbQ5rrTNETlthdJhFVcWkobinGBRg0nzThyD5xuaFSdhdydrv/QH5PimSXb9GMl1gW0i4iHTdShXjYoYp2BVEefSOgnUxUdZqQUvg524Dd1/mMMz08ykzRMaOu9bu2vJd0brZAKP9g7PdGc91531OLHL58yFbSxf1ik9K5dl4vwcmzQS63nzPCTroKbUJvG6S+iSLl7EEbhBsRvkeaqyhBREfADGbx3mM71b+Kuz0Tg4UcSlOVrUpRBEqQPiSAitYhEihY6MyIGG6vf3wFtOg60zcKQBpy9DXvISxJtR3KTQaIAxCh6trlJwms7WrQpWYcRmWfvpd9PmfkT04G2Y+ctS4EsEV64plQYmyIi0il5tkfFEHWqtGD9ViGraJ/lVR1y1MuF0GEG/3RrLbtib3Pv0U3haCsi8fz6rHh/XVy0ZSd5+/jpvxYpzTEMz1qMJOg1RBUGgq8Ty1dAtwuRsP/ScFKIgpB0w/WBumeLLS4u848JOs4wGsRg14lRMy+I650DcUBpTLVxIhUiV+Xkj9447vW/M43AjRVHXnehpKRFqBxMhA8ZvHVRruphY0XqkkrTavYPjjlV//S46unaR3H4bJpNDxyeRng60FsJUNcVZ1LWmkSCqaDaDNONUKa3ORGhNLKc8rTeEWhjvA2RbK8fOlryz5zDLclkDuh6ijx1hEBi8Lue+OTLtvnB1KXjFmnNMs37IGZ2B8hEkGxCrSs+pRV08WGPyhl/S6fvP1Dtm6+/+1WQeHmT6pHH++N7H9OuXXErYrIuYRFU8EUQwCknDYROeBKltAhlUlhRE7jzgONiEE7rg1C4lOow6H7xU9SIGEidUGqKNUDXwlEzGyMS4Y+mH3+tOeFE78fc/jgR5QRGpheBmoJYgRo3MjoYFSCxkAiQM085QJXUWFcUIbtrBuNUDU8o0PCyCrjkV0z+ID7iNv7zrln6QSy/BXLaZg98e5tVz74q/2ynmqjkl1yyXxdNECRXqIV6bR/Y5z0NmaZ+fOYNz/261/OUbYN6GQaIvnE0w0GTjD+7Q2w4Paj7w1bomaFPRhtKcVgJJy/pGDNa1iG/A4lx6WBNNZW6HSLc4XGjJG1StaDOEiTKMzEC5oWKd4mcN5VFH4SVzdeUblhD+8ydQZ9AkVg2T1NaPNOBQI621WzYt1RjN90D3PIgTnlpDlNRyBKQGzFhzcMi6eo0OVbLrB4k2QLJBcCKo9mP6L8HvA++oaaluAHfZZpJbL0mT9dY9/MnOHS4kFGlU1ZlAaMRi6jFhw1F9zrws7cOTAezXz5ePX31d4Xfv+kHjiTvvcu//0zo/VEWu8XnZNSv43vWvkFgn1BebjnBr00pYh7G6cLgieK1JjwKeCnfMwKNTjlethTedgu7aKTqdQMkhRVQiwLZyhxfgmtNKsqTAuk8twXtoD9KMBa811/UEiYDxFtaSEVjso6GFmoHLL4ftdyLlRjrcaMVCMeCsqD5iVWZU9xdF9w0Tzuxnz9SIPjw+onfuqfPwl2AXMHX0qalDBlKyK+uPSiwvhs53ny73Xn4yy8KGxs3EmMmyZh4YZd9Hd+qZe2DmueWQVofue9oZdFl7+WXeivacfNe7y/6eCJ/q7+cn2z/Jv4yPc/WCXtOMjjg8L83FiUNKGch7ijqIRYlsilGNRxAEUGzC3Y+JjNRE5+WUfJCm2RbhBCE914kynPbeReTGZohGYiPtHjhNq1bXUsYs57ThYMoSDlpYs4oco2itjqZx6ilzzHnwmEPGHQQiy/PIqnPINc8zp0ehnlmZ0reMDGnz1cMcmRznodEh3bRjnPvvgV0ijPL0eYgAegc0fz2kEUUisROdKatNEpFGokN7oPzLlPGMc0g2SyGoRJ6MucZFyyXwnPfX4UPatWGD+5Nr8tx438N68eXnkM0XRcNxpRkK6lRxSMFDKra1LOiUiRimYqWYE5YUlWKoLOxQg0NtygUmdJA4kEC0Ou5Y+KqizF9QlnDzCKZg0n/0JPWGEUVnFCkATlAjJI9aqofa6Xx9ER58ECFARVFFcYIUjLh9DvYlKf0lVpL9kOxVjOeiQhFKBWHRYszpp8pS68uy6RmuPbRP41cfcGNHRtg+NsKd+yvcdhdseRjqAlwCxbyv7TYROzSl4lm1TSvadGyjBUzO5uLnmtQzJlRsgFefUs6da+veOnNDJGI+Pqz9Z41wS/U2fv1l55p6h1g/boITIYzRrI/MRBBZtBwLe+swFQsrupBVvUJtJLWbyCGKpgieCgo06kpYMCzty5HcP5Euk2jqcaIKRxTGNXWpJqifzpGrj0Dwmnb8if3ohCBFRQJJy2KDMmSVQYuqpnauYAJERMQp4mqKHU3ZDcbTxMtJMrcN5s5DTpsvc0NYOFOVy44cgrO2ua/JAX4TkFM6WdQR0JUkLi7XkI4sDNVERpruVoBtA788VRwbyeGG1L3ihMDNKFpBTMFIHGFWZ9zMyoK+99puLtgv3LhpgsY/P0BQjcW1F5RmlMIogYdmPFRVNQHdHaERqguK6rSBWkF9D0o5KGSEphNGImFfCE8cUVO4os2UMk7s3uSpZC3prJ0DQPxUv+J5QnmbUl2ep21NFd07kSaLukNnLNpIRGas0UErLk4bFLVCSkZCUBWjiknS8tvLgHiIC/Gbw+rVt6uxO7D+bm0sEjPTZoQDdYlmU25Xhgu7M5QqDWMx4irWZA9U2f/wCD9uTf7t88I6sQLiRKWJUnXEDZFKFXNRB9lTsnzsK2PsHRf50L0TJrj5wUDGY1whoyQWEiea8UQFqFmotmL9SSVBQzTriWY8tJII+2uwvwYH6spITQkLwklX5eCJGsYDrYIkAp6gw6BVRauCa4DxoDkBW3dC7sU+mdEa+pRHqaiqVFXZ4ZBGaxTg0lLjqIkyGoEmrU9nP1ARAyYQVFR8I2Zsj8t9ebOb/O64fryVQzJL2ri+PSAZmVHJe+hoXYJDDf2zzTC98Ums+zl06q1Kwu4Z4r5DO3nVsk5J6tMqtUlluk7QlSE+t10uemtD//BL0+6mlxVN4rngY43HuuWMRTN2SbHhlesp5uIL7GkqAdCbQ9Z0qUxNiR6owngTmUkcAizMCj0ZODwBC1/kuzm2SrgvwuRBIsWV08qKcdQJIrEKM6lFP7hF8c4osmChED4e4xVMq1NXUQEdRnVCnfEFv0VsMAacqHMWSeqAQ8RvdcO2lbrdk1pLQTWDu2WXy2+p84FHhe0ofGgh/2N5SV5cbuhMHCuV2LTvLPOtz427L/aD+VWE7GPaz9uYupk8OMnWBSGvmgtLipb6dC39/qbF5FRkpCnLt9f45sOx21RL3CMFv+MVk5VF7bUoaS7oaHhFH0abwl1lyBrM/DxyYk645xBypKnULBgjUjJCTtICaKqBntvn0duIsTOK+CCudUDj6fgyNWBRT5DRQ8LgiHDe6wJylQbq0jykIhijBJPgHVbxPVRECCPD5JRy6IhQnoLhYahUkPZOET8AFz3FWGxV7DiEfM64LXsl/819etePY97dD1rtov1lXfIPK9q0NFImESH7yLTs/86Q6zsC9U0pqU6fs0I2tJrDH0NTIu4Yq/CK+VmZ12mIRmupWweeRHlf5labeuh1MfdvVH3icFj+mQiX1qMFC4YqxWROMaTuWXlgRvA9kU6jzFXBJuoW5WBeBunykba0YaEZKaZdOO8ykP2KGkVtq8StgR4B8QXjpSwKi+i9D6r0XpTnpDOFeCLEz4LvC54qOgVHtsEje4TbdqO3PwYP7VQOTcF0LNI9X2TeYugpIkEkQjMleLcgsCcP0veFoUmPr+1Qva2s108J+zaBvq2X3zmrW95Qi6XuLOZATQp7G/q+7ze4aw14734+J4YbwPWD2VDj0WqNy0PL51aVzBXNJn6bCFlPKGUNi0ty3Yaa/XxrEPPAg43Ryw76k3++wM174/Y9c0WDw8nidpWdM8olnTA/QLP5Fh7dWkFQlMDAdA3aVkEBR3O6tcbgpw2KK4PErfDlIFs0bN+tjDaF86/yIWySCTxmhhz79yi79sOuw8q+cWgCXSU4fRmsPVlYOR+KTRFTVecaoCEtQnGrh+Qphr7xIG4Sf3cXxZ/X5JM74E5R6Otg+dIc70sszTBSHaqb0s4yN3x2Wv/+meyOPKOy90mlwN7bR/Tl54/o+StLrGtaCupMM+9ZJ77sB9wGcOlAS4YOJslv5JPDnznBl29f1WkWFz2SSuicD2QD1XyClMO01PS91i6ISdGP009B3Vg6PZBQUr6UgJ1JWwfnwFihWYVDB5RTLzVqp2ty7yZl5y4YPKgcKKffs3ye8LJLhVOXwqIOpYRCFeyQYhvqkqT181oVjIvThGHSfIEKJJHEP3pC/J9MuNsearr/3WK+B6cW+HRvjgXWabivatoem6T/C1V3Y0sZ7hm0Fs+O+X5D+ny/kuJyCfjv6kPfMZA5+bXzks1nzzEd28etu39cxZOcnFtqc5fPqbjFQdO3ikxFKbweI+ytOV57vbjeWLG1FhyShaQG0UElyEE+K5hAePyAcudBlUa7yJ6hFGFuy0JPFyxph7VnCqvPEoJIYNKRVHBxM81B4rSF+YJaFY1QF4E6jLMpdKOCtufVPnTAT27a4SZ/GrkrqrDLAe/okQ0X9PD7c3Ka7Cub/I5pfu9T0+7TLWXpM+FvPSvWyYbUA+gDb/VqvIV59O0PpOPOf8XlArd+APeKvL3hiuXZOeWZuD5eU9/LtHHAkkSVTGa0scxbmqvEa9pnku5MJEYj6fLVhB3QHoihISpGVZ3iYtBJoein7MetE7B1TDk8pTSayPSQ0t0LV7xUOPcMQ3FEGXpYmXlI2TcGixcZ8kUvLZ1MCgkcbZWeoOqDESGJVHEqTgXPU5o1322ZDEoPJ43+irBLFX5rDq88p4t3tGeFrRMytXtG3vLVqv3OxhRDeMY00+e0sNMHrB8kAnhtBytOLnD1dMLce8e46QGo96WUf7sOLr9sWfDKnDHVh6acN5Vk4rpfKNpw6gN73eFHxzX33sGk/fz76vM6l+bbWZTVpGhHXK532GQDHxsm4hT1PSHjVEaq6JZRuH1E2FtR4hBO6kLOP8Nw0jph5QJLhwM3o7guwTtPMLscew4pQ0cSli0zLFxgTEacJg5JJ1iCKO7JosGAlxWsg4JRxqviNu7xCj+rxN/e7fgUwIeXcuockb+xjvwDE/zzror7X9+usuO57Bs+W4XMbqrat/Zy0eI8/3N5gQviRJbtrOsfPAD1fvA3gFsL807tNJ9ftzAbPHqgHu6vY8elmDvUrG0ddtGngOYR1/wRNFcu0NFXlJtzXnfEdp853sjkVudNLJiMc05zPqYRe2zZB997wsrjNZw6WNyBXH62yMVrhQVdBmYcdjfaqKOIk8CH7qxI9zo44UTDgUPKYzscO3bDSSeILOpK47azgKoRURRRZ1FnUd+Hibq4f9gjmR9MRXffEev/EEjeeAJdJTEfjVWH9lT09z81qt+ZJYI8l+VP/9nkjxvTYY25YYl5z9IS/UuLrlCPjH9fVb7050P2o/1gNrVmnYUsH7ry5NKJzcjOTEXWr9mcnVbxhpPqR1PkiUw/JDciu4edfno4Gv/06tx496jjtMs7vQGT9+eoNcnP96r8bL/jQFmxsXBSJ+aEQDl1kfDiVZCfVGp7krTJ88FkWtNZgySJouNQCpTTTjIs7IbdjymDe5UjE8KKuUJ3MU3oGgs2QWwC1qLZAK2LkQdqNpryeY/E1P8YzO6QYCpjbvrpweSeB9KRj9yQrvI9Jzb8Mx7htnbp8p8+WT6/ssR1nYFWq5G4rZPc+61D9v0KcimY24QEZdlFi/NvXrMw17xn53Qw3hAXU8pXkvo24JbWRWTuRnApQTN9pqEya9tF/r9qpG23bWkmd2xT2V9Vyk3oboOXvli48jQYf1S49RHlHw8oFy0TVi00uIymAKWmiAnaGg16KQnDjSldGTjvFKHeEEaqyp5RxZWgI6M4O7uAmtJkGyF6YtG51y432b96zL1E4b5BkIERRiEZnfUKeRKefG7iPRNlAHwfOv5infm7lyzitYQ6kzjJPjFF+MC4vn5TzEHAX9aP27QJ6evy/89bzm0/c9vBerhrMvKGqllXMYX8ocb0J0PRn+8T3P7WJhOw+hyfN53fZT5+TnfwwRfP988qCHbTDiuHKyptPnrlOYbfutLIWUWH7of2LCzqNVQasGNEaTSg3YN8AdRD1KmY1nBQZv84sA2wIXiqdBWEOUXwSVFd1dkPQV2KV4ahykldeDsrrLu3zle3pfermEvTzpvB53Et4Zg9pOWO+tW18uVLTuDauMJkTgj2NaTtQIP3fqOmj74Ngk2gmzfgzgvkz68/p+MaUduYrrtguOJcjSB3JK7tncZ9HCXw4YK1Htcu6PAvW9oVnHz6nGy+pA5xtnmwmkS7y85rGPTUZaLXXQAnl4zE+53WqogfKCLogryTrpXCziPw0IiyfQouWGZYudRgMjbdaWxBLZqkDHznSBO4E+IaqNW0z1DEJiJu1kVSMorEKlKwGv3mCllweFr/VGLe+ULdr3JMCklX2bCfWsk15y/h9e2eliue+rms5PaO88hNwylwBugXITnf54+uP6vtA91FrW89EPsTlYgkFkac9fY06ntWwu+f1eu/7rTFxdWn9uayBeOo1uP4yHTUOBRamahbMxlZphPYU4FXnwInx8r0YKJBJmUFzka4sKEaR8iJHdBbEtk6AXuGlZlpy/ITDN1t4EKbjvKctCisqM56A4qm8E1rnTTVgku3IVKNCMw08E7p0OiVS+U3G7v0qwPppTf/IRtU0rcRhxCsXMD7l8wjmRnGZALc9hnJTDbdJ4Fw4dkEb3+A+EWGt19zeulPLl6Rrd+/NzQj5YREwYmYkoni1y7wLz6z17/ipJ4MbRkvrDQatW3jkTlUc+ZgxXq1WFWdWhQmQ5X5GczBHfAvVcOly5U4VpwKnmmhfTZdd2smom2B8rKVyHQT9h2BJ/ZY1iwWOootiN21vKWlTNUWlI6ira0p51SdVVEVnKaoQSYjtJV8F5SILlniSluG9UPUuHb1v84Zoq1oMpgulrKNY19FOCaFbEx7JPvBHl68eIE5SxOavqfiPJMfaejunw/xj/1g3v4A8SV5Xv/Gc7o/f8GiTP2hnVUJ1ZhmZGnPGS6b63FCt4exVoemXOOxQ3UZrVmZaODNxGjojFMvkPHEZSNrxQfGHLyh14avXox86VFH2RlevTKlEiWuReNJVESUjBEVAzZROjNwxgnCZD29Gc2F6eE/yZhD0jK3taOSThDThG4EvCCdzUi6/OsmIvEfG9XM1sc18+iUG6kaNj0NtehD2Igz5sklRwUY0BfCQ/pSUu+iXl7Z0615ZqgWiqoN3wRNqz/eApX3rSbDINHybv+1Zy7O89Duik7VE68eWaxzVCIoxvDEkGO07thXdl41QcNYbd7zMEGQi9UzM4kyEdt9ZevuyajcFoBakY91ldScXULv3etMtSm8aR1irJNGQxCbDmtE1HgmxTiSME3QHV46VIvDtCJJmZACBjGCiod4BvFVXCIQ+WhksdUIN1FB9kyQ2T6jwb66Tk9aHpm0/ONdjoEajMzCThvAbRh4EoTKrYbOk6BrLvQUs5TsHHZ/6jA7OcYVuF+pkNY+nvR0sLbUpU4rmGKX6NCoMlHVRwDp7U3JIU5YsP1gVWsRXjGflUgjyuWQnG/YN6MMVRzVyKlVcZ4xooEUDiZQrsY7Z2xzc1P1BxFsTuk2Key9pyLvLKucurpLw4KP3Dus8tc1+O2z0gOvNHny2gKvVZSre4qUp1ZUVWcZpCCK8QR8kTCC6TpMN5TRKhyuiuyqamGoDmMJrmb10SYMTHn88PGYh34By6O1Wn3WhafIb+Q6WFXIs6CYpdcPtJjPSVZqFO8f5KegL9NjBA5/lUJEQbuhLZdjaX4ONqkiXlFkYr9jrMEYoFfcRgJ0GcMSVXEN6zRGdbLhpJEosTpGyg6beFoIijLqkvxQmCRTNvmniupXgVuB8tGj5VUQ7IJob1W+sW9G/+ykNtyhGt7qTnhgCj5yO/zW2XDqHKUyLSn6R+saIVqDcZ42lRUFnBWCjLiB7fDdfSpFo64d4VCsjKjWppzcXRO9J4Gf73fcDtRw6WG+Pk3iuibN8/ZdAW+7ti/45Dlnm7w3GjkfrNdUSyIaGKKtj6J7xuRnoDqQmo19TgqZ1erJkMsEUjIdqCxUIVGNHETmaYBi0BkYL+OhHo6wGWkztAqYwzWHtZ61ppjZ3bTxkTj8uqKfCeGuf6MncoDble5jsS1yX/zuPvmtPziNpYs7SUxV5IIedEdZ5bO3K685V7hyLdgxJW4hxSb1LjWS3rmV7qCJCipW0/yzt+bY3VRdlRN6As/1Zntzw9WJ2x/R6MrZFDyrhNWtxDwAtnUpm+1fzu+9/ELvY2cvp8ljUcVW1EDKzNe6ah3yt++UnV+pu88d1VA/Nw+ZvVJiDJq1aWrxtApFICPq+wLuaXdFRZ2BhNVGLPunQ5xTROBAQ10l9q3JtGcPNMtTMy55fcKTK5Iyu8T/b1iPtsrKiW3jeuNjZfnbSxYRmwPKaAM5ox32CHzvHmWkLFy2FLo9pZAXiNIyNrKQJE+9EjHgCeISlXqInp+D+RklsYlZldGot3PhxZNj+965DT67GjKDEB9d1vaDMRtwLw9Yt3qe3HhBt4bl+2L1S2SN17oox6FZn+SuIyazreH+cgpmjtU7joV1ogLsgsrUjA43DonviaiLlW5f6S2auYDY1+MBlZ1j0eSO4VD2TDm3exrZW4F6LDab6TL7m9Ww6pL1LWUEPMW++KWQw0BrIPYzxzc379b7o7zk5s0xbkER6c7C8jY4sQdu3658+Cfw/tvgi48q907BlEBQTK8HLOQgF6QDLRGwYjBWWZCB+TlYUgRxR3Rlruau6Sl+7DVF86ZBiH7xdqEbWg96+WI2XLzMFKN9mvgBnrFCUkaaUyImQg9XpbBpiPu/MMk/tIgNx1z2/koa0LdbBzdS47HpwxgzhUsqSptAMdDLAP3inpSV8mhV/u6eCTWqXrHk+XSYrJuf7QjGo3oeF70lTHNFkLKonrQY2Qie9uHdegl+/9OfSVtrAPG2Gf70rsNC7zzjZQS680JnDlYUYW13ikM1m/DzXcKn7oEbbxNuugu+skvYNAlH1OAVPAodHr4obUAh8xTjxPhoHI/Z9QtdZnnWfALo3fAkk/VJvMq9KctlZyyQq+cbrSWqnk2gPpOyJTOBqnVivrcPfWTafQAIB5/hBQPHDJ3sneC7h2d42wkjSL0GPSVtLu+QK1+bZcXbHmDvT8EbCN3nTzbohOg7Cr6sKnqSGbfNZDppvn8Sbm79vvhpyLHg1iv26Ns/j16MHEjTtBHLPy3fYX943ny5uqeLsFZVz/dSXnDGQMlAQ4XIQS1BK4lyaAIeGlKcB+0ZWFiAhQWlM1CpOKNzMio9OZW8Jy5j1KBIt9cIL+00c3dMc/UPHV/rT2c6yWwTeMoc3rt6Ed7MhHPNUIzG6gA8HzqKktwySOn2Yf3w9xJ+/mw6+V8JLg60eqprLAfOy8hLl7azXOvEmQwa16S9EdFxcYVb+sDbDDqh3D+m+sVxa//v4TjeWLHJx2fgxy1vtEdVb+ay9NC93/F41btO4x2v7JYXrWow+hcxo/1gZikzg2AeB40a7J2fkd88Z4m4pAalLLQHIgUPMkY0I0jGQMZLL9EseFAMhOU5YZGneIkyWlMZawgdGZE2H1mYE9oD1YIHOS9lGC0v4R1qyPzbm3xtE7hZxsjbOrji2lPkw6sCbUxN42FFxIhpOgJE/B2Tkv2Hnfqdr0e8e/Y+rhcK7fU3Q3KKQLfh2q4CzXqDwFjCRiRnLob7/6LOji9A8P2n5j3jCRyMYPKoxE1rKUNvAP0NuOw9q/naK6+Q3z9/jVx4So+5tA3py07p7Z9IOLixVWYOgvaD+RYczFU4c+kcWbs8L1EUIsYI1gqlQNVPqykpeEhnIFrwoGCg04dlBaErQObkkfYAmjHMzUFPJiVf+wYyHoQWacuKrVuWTlXY/BZl3+rV+JvHsK/q5erAmpfevU/dI9PIveNw7wTNe8c5dMcRdt83qd+bMrxvW0hzANj8LOD4YwpZGyDpB3NPB99YcoQ3z8nL5d15LSN4q9qx5UQ+d73qVW+fYHtrUihHbcXo0feCtK62KPXP40+vfIn322uXulyxprX4EHjOuhctkY7RCgNPbOeK9bDjF/a6ZUedD9w8qJedcpEp5Bpqp2pqoiSdd7QHKRRST8AXpSer0GLyLCikNKOwhVFNNyBrlPZsuqyV89NaOZcSuN15XSJ3jvHGn9e4dc1g6tkDh/hiO25zDgpNiKcgbkDtAEyAzhxVnQrPEpI/5nnIpSBfmSRZoNyRRLx2aTs9+SxRHIvOy9HjO16+1OeOj9YZmrXsp6C8p+YpO2Hp/34x37r65d51q1cSeodIoiMaiOCpw5eEeF7e9M40OPdAlZu/A9ENwGWtMvgnMJ6pMtZe5NoTe8TYOrYjjytmcIWsaN6HpoXQpm7pGSj4SFsAHTnozkNPHuaXoCMrFLNpWJutJIwRIot0ZzFDoSz4UYWvDUAdkDGwh2B0Hxw+BMMTMDqTLvGEs3etDByFZb2gCtncOpCvh0wuM9weRrx6Tl46M6KxOJKSx7wwlutOzZt976/pY9KqTAafygPeenDn5Vi7vFc+vK5Lq7rbGXEa+Hkx4jCaYKar+PUqzWU5VtiQeVc1uaUVMt1g6xl+AA8UK/j3HmHFXVPkBstS2FOTYCg2wUyC5n1JFpZwkU0ZPl0FkawnGD9lHbrWPY6ZIFWeauv2WlWsgzjdWog7snQ3pxh/2LJl1sj6wcwF05dORmV2SDWbb//dJoatQ9WN4P1hg8Ndlp/VmnJFb46FJUMEkmSFLPC6UwOCu+rcOZiGOv9S4LOtnuITCQeyw+x0NXnj2qWeBiLENfVcHeKGkMSGchOvZDQuenKmq7PlM5bds8odbBUZ10b8fEudr402+N7jVe7YOsPuB8Z16vYJtQ9Oa9ucjJTOnSuRMSLWYbRl/RmTLg0ZkfR+YIU4QdObUVM8TFphrzsvZk9VF29q8NWbU+RANreeYfNRH8/nPOQZvxnKQEspHw4Z7jT8U9NyfsmXlXMyqsWAyKjEhUCuPC/HFas8dn+8yd7NrdHDZ1MigPlj5dFVMFyt6DXzi+IXLHHYxLjWkKIQCLVEXE8GYwNz8RPT+q0tUJ2tvGa5xpuhMQmHR+DhIfjJfvjGIuXvm/Avg5PMG2+w5sRu8efliRoJGjukECCm9aoTRZ2IhnE6WjECGYMWA1wxa5jTIXENWTQ8ro/sVbYd7fEvlDyrd6eZVcoNTabHsnzbbyC1mDNKAR0FT5KSp5XOrKxoC+T1pxfp6lX2vyFiouVhAJk/q3PfCsdDj4/qpb4vPUvaJRGLi0I0n0G7cri2jDQXFWWhs7pgc5XvXXqURbb+ltZNPaYXvH2gvw3hfsehnco3GzX2PDLJ6Z4vvWvmihYCEnVIYHC+wfkeLhugWV/IBuKJIajFBOMRwfa6BD8fweyv4mKnP3s44sEb0rHtC6qQ5/TuCEdXQH29rDrJ5/1LcvLmORkttQXUAyPxWEzboQYjo0394VCTv//76adf9XUeLF7bwf++cC7rT+uQzl4fGhE0FEbrSjmW6d0NfegTw7xmAirHMFeQ/tQTVUA7oGu18N6X9/J7r13ltZ3crWGj6bxyE38qgsN1YbgBUyH16aaOjDTZPxMxOBqxdRj2RXDkbBh8Iebnz7tCjoI+nlxE6evgjMUB18/L8NK2rKzq8Cnm/XQ/cyKiMpHozyZivr6vxq23VFr3UwGnwWnr8rx5XknOGW/q9HTIUD3hkX2O+2uwfTitdJ4ps/LJTnktrDsry0fOmM9VIzXKh2qMTcXsGEu4twyPjsLeKTj05Ooz/Ie8b8/z9v4hRw9tWl/Kre/i7Pker2n3OStvZGnepzsRcrUEacR6IDFsGa/zkUaZfS+gBcrRDJHT4KwyTO5Pp36No0+hdXu1DID5DMhc0NXPcCb+n0YhRytmTXox5NMO+BToWVpkftYj32kolAIKAlqNuOdvZ5jua+WzjeBmSQKjaVnpNjxDBvmxMvZbDEtz1MEr/03ey+qXWaa38enXUPyHSz+YFqL8n/L9D/89H0r6W5b/izOP/85WeVyOy3E5LsfluByX43JcjstxOS7H5bgcl+NyXI7Lf1f5fwUVb8sroJoBAAAAAElFTkSuQmCC",
    "heart": "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",
    "crown": "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",
    "chat": "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",
    "medal_bronze": "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",
    "medal_silver": "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",
    "medal_gold": "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",
    "star": "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",
    "bag": "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",
    "laurel": "iVBORw0KGgoAAAANSUhEUgAAAGQAAABkCAYAAABw4pVUAAA02ElEQVR42u29eZRlV3Xf/9nn3vuGeq/mqau7elSrW2qhAaSWmIRAEgKCjcG4ZOJA8AA4NhDbxD/bsbGLss0P+5c4JHYwieMVz45/3Ti2fx4YjJEEQiCBkJDUrZ67ax5fvfndd4dz9u+PW43bMghJYOMkvdd6q9aqqnffPWffvb/fPZ0Hl+WyXJbLclkuy2W5LJflslyWy3JZLstluSyX5bJcluckCjI9jflH+7x/xM/6X13k8qK/xZYhwK++mT0ibHv37/G5Z7OO6elsLe+bQQX0mbxp+jYK27fxsmSYB97167Qu28ClCtHMdXzyg+Uf/PwHez7xzqsYVkX0H+ChOTKFp4r84U+UrnnoV8qPHPkhbrz4+2/1PvyT8J/ZRkwzNUp5Yk/xVbtvGL75NTfwPSLow+/AfxpLFgV596vJf+Rdw1f91+8Jrp2+jYGns35VZOonMSKie3cXX7Xn5ddeuWOINwJM3Ym5jCmXyEO/xC9UTty50Tp+5er5D3DiP700d+jrKxI+85PFXzz+s7SPvoHah18tfwLI1sZ+Tev64o/ytsrH96w3ll65svJf2PjzNxZuvYwh2efL0fcGV+/f6/+LHYcmv6e0/0CvWb1X7bnIXz/P3Pyc++DZDfcn3/s71LfeoF9hR+9DP3x374EXTjbv3/PylxaXTp9JvvCJldLZhnnbL37e/e6RKby7j2Ivxak/fA/D1x0s/ouJvaM/VTq0p6TNJ2I9Uw0a82ahtuyOhh098vxf4clnikP/27isrSdY/+CtHLiyP/3Irsncj5SHgwIrD6rWo0ACtaM7dPuY0d8Yw/yAgB6duuR+jyMi6Pb+8L3brugdKdz2C+6a1076+3aSbi/ygfe+jCvvPoqd3lqjKiKgu3vlvTsGvf/YM9YX6PqphMVNH8H1jrrJISPTpmt+9z9MUbiowH/sffG/ZaYxgwIyMsL80pz+Yv1s/bv37qwfHrlRkEi19STB/EncSkc+vJy4jygIR3EXlSkz2N9+29B3be/bfF3/S/5lR/pvyHVPbfKCwyQrK7JtcV3+45Hpq9/A8eOWo8iWacn/t67/+fGPt+y2zz/x1omrUNNPak+rrC6Lf3aFP5kPvZ9vHHbRFuvT/13gQI5M4ek0RjXz5xdf01/bKsuf/uHgw6sfMvXGf6X65I/K+m99m/f6v0dVt0D3P377wHVfnM5dqPzhWD2sfSrspvNR9+GrovZ/J/ziD3r1D90hyc+/0vzY12JPR98U3H3sR83C6v/D0ol3SuMTb+XnvpbHUBA9srWerdeRKbypfwKs7BnHE88Gu+6Zziz1B25h/JH38FDtl0x67/fIH160hkuUKNPTmKkjU97/fHv/J078LHHr+E/XI21FUfeeKH5kfxT/T7rt3wja976F+syLWXrHC4MXXKrI6WmMHsk28mP/XD58/qek9lffKV98xz76JYtN/K99r39/Zd/srMI31WWpZn4d4FPvKd3RF3febSPtaTZpOsE1YvGOr/gzP/fZ5MvT05iZmcwFvWKGVKfw5Cir//wF/JlZ4oalxPymTlvDcWSGDJiPTGHunsH+9vf99Zu3j7RvH73l1o6/63V54jWUENShBjElMXt3CV+a1fFSmL4PeB0z2T3OzOCu2bLePzyuf7SyJv8qNPI7v3FO69O34c/cR/rU9fzknfR/1028P6zpRLctrhNp0krpzjb4nZ+Z4b5L1/JPRiHT0xgR3LtfWh59/Q3R7+3pa9/ZO5z3uk1DHAtoyvyTMSVJ9v7r23n1+2ZYe9+lfvooTkF+Y5k/WvVIT23YByTDDLm4OYB75529w/tGOj8/tl20+KJfCExhp2hyDkwA+KgFyanZdqXJHzzjut0FvWvmZbxi+tPcc5F13Z1dV3/pTh4NYv5dM3V/CQj3/Z1NFYDpKcp3jfE/Du4OXhMf7KVyoUmnA52uJYndv3j/S/nln5nh57au7fgGccf/Zrkp3oeefYDSt12r73/+AfMq/4qXdnJXe/TlaiK+Il+Y05Un4qTSkkP1SJ8n8DdT4LH19H9FMX/KWXC//HcvD0fvxtx9FHvkrbxnx0S8d8fr3hjSe7Wn6RxoFZFekABjwFmHKahcdyV0I4KlDu89BJ+dOkS6tdEK8FOfpA76Exc/aOaSzZyeRkRwP35LsM/rT2+nGLT73vSr2tv4qND6KyTM6+RHVuWBB/Vn/9O3MXf3UX7zqTT7W0V75X3TyN1HMT9wuPShG65ov7nvVW9rF+78fd/kt/uE656eOufVvlTzqi1ynUhNvfm3buGrKfepIDw9nSnjV75j8NqJUvttQwcPdr3dP+ChESJVQFFNQNPsAp5ggYmdeDfsIUzavPy2a/jXMoM7MvV313xkCu/p6G21mtBsm24+7Hhu4X94Gs/52mr5SuRPXOXxvEkaxYgPvONa3nYpzf6WKUSnkZkZ3Et+vzA10RtODbz0VYnddkegax+EzmPQTvAabVoVYa2OpIqzHtHToL0+5SmT9wFTh8hdvyv+xSuu9voKN73fOV4Deha0ATjQDdAUFRAjiAeuzzCyW8xAkXBbmZ/8yZu5/u6j2EuB+O6j2K9Kb7cwpytE6011tTVEVx4TiVfEtB2EIXZQvStfJObKHZIfz/P+tzyfq2fAfSNKMc8VvO+Zxr/nNnyZwU3fld9//a74l8YnPV8OvDVH+EWk9ecQR9BpIgg2UnEe4sBFSgJw6Bn42yNTGJnB3biz7/V9Qeeu/hfc2TXDtxlNz6NaRV2CaB3RGBWzZWWKClhP8fvgFTdL2p+Tfl/5d5e46WcU9DVqxM1I0yRBtG1U/F4kVxSDb0xORLaJf9PNwnhBhkdSPvjq/eTfB3pkCm+Lsck/OIZsMan0ojvZ8QSv2j2hu/uuvrYdNz8WSOMhkBwabqJhgrYUjSEQyHlg5JkxkulpzDHQH5uaHDq8t/qebZNizb5X+BAJnAftgq6CBiBDIN6WhhVVIFVSERkaV//QTlonl7n939/J2398hg8/U39vBSeCugTSCxX8fSUFRK0F50R8xfoEYz101tvc2ae8+OgUn36uWOI/WyY1M4P78BQ7do/5U7NLeuyHZuxf/+fX6nXtqir9k0i+DzSCBLRew4WKNsB20E6C147ZVGXlqSAKiGoG3qNryPoYOgUqM7jf/J7wRyb7288buv6lqQz/szzpedAFIEFognoCPQiiFxFbAXyRXA/gibnxKhfEXaL7zvKe11/FkbuPUvk7McfLcZfWUi7emxHWw66unbrA8E3DoUVDcWkMqYInaOLE940e2AOnN9WLrXz73Uf1nl96rX9zuOluuHfJHblvltozjfz9ZwXeAFPkdo3Ir+0bSN9QXaH7/lf7M1GU7rQpJNUzxgwmqCkJjSUljPHEsHFOWN1UV0nItVLWXngLlY/NIXdPYQ6tIdeMZbixFVHaSxHlZ1+77daRXP2dw7tGEv+ad+WRfYL7uKAdhKZAihgjqhVwkeqWgzBmSytGBDC9g3DFOMlDs+wfTPlphH9zaczBfRlsCPD/TuEdW8tczcx9dA6McHqiX54XVq0GZ9cI+hW1FoyiiWBEZbgfry+H68vpTb9ym/m3uwvpu2t9MvGqnFx336y+633TCDPfRIXcM40nM6RH38brD99QeEPv4duajaOfzp27J/xA6EvHMyRpp+blQys0qhB18AOfdCVlYwmda+CqCRIjx2aOajyTxR6XbL7Kj09dM76nUN1f9uNrfRtdHXWiQy5Zvna0SKnn+u9zZvBWT+PHgBBIEULQVHTLVWuGb4gIGBCXFUwIEO31vD07rVw7J93qKf1X//Z6XhQUmM3l5VwuJ6e74j2+apMLH/obKk91N0nCMaP6hmYVJw+1GbzZIDmw7cxruhRpdNRPIc175uZRcbde89rrbKmz1v3okZV3vH5X8FszM8mXpsA7ytO7smeskJeDg2kzWph5S8/ggOauf7t/VXoOOqfCh0+IX+3A3k5NaCWilSoeTtMNZe3zsLgM823hfF2c68n92Vvfekuhf/HU2DaJJnq85KqBcvdwIZBregvs7S0x1ttDMV8Gv7dHC2OHotzwIWT3G33iZXBPZgrRNpBsGVSCiFXlYt5GMs0oqCrigJxgAzE33WR0/EojtmVf6LruRXGihJHS6rrWuDNrv3Y757uq59tWn2gmPJ4YzhQTPv/kCt12B/95sah6Kj3jkO8FYzJHZFMlUsO1/U5e+qre7uSbXuKln/wTLQcE10yk3/unczw8NQVHj34TLOTIFJ7MYH/nnf/hRTuHeYmZ3BcnjT/1era1uebVvqnWUyrrkFRDyfdH0LCuvSJSO6+yuIbWYrSQV+/QNg2HB7o/lq/c91NDA4wM9zPUX6bQN2zI9Y+48vjupDBxIPWGD7b9kf2Y8g6R0lUGSsamLTQ9BmyC64B0ULWKCEIszrUzG9G/5TW6VQNWRfAUb7+nuyYLsme4YAiTMK2nGlcSF21aWhtqqgs62dhgX70J1Q5sKEmcUPdyVDbaxIttKYw3VMvLghcCw1Dc6ZH3LD4w4DkO39jLzrfcblj9a4pmw+zYJfbEE7zytt0M3H2U2qWB6XNWyNQRHIIXVDvfXzhUKniH7nLa+aiXxjH5Q6Ny4JYNztyTEC5DbxndfBwaq8piXbhQgVxeOTiGlErGzw8VDo/tLtnStoO2sOMmWxi5sm0GrsTltxspbAODD05wMc5GEC2Cq4O0wM2BCiJNVLuAB+op4mduSt2WQnQLkQ04BadCQfB25Uk9o7SdYAKPoTzBkCOnVnvVMdGMrWsknagtGlaFxrI1rQ3Xv7LKyGqFuBOjCzWk24VdIUwkiotSSr2w3hZKeaX/RVdgyh7xE2dU1MhIvyReovt25vlB4JenQWa+EYVMZ7Do3vT84rh2w5d7ff2OYMFI94KKyYlNA3a8cIDlYxWSutPGk1ZXFoRmW3R+xSlFaCdIf6nAjT/zS+SGr+n6hWGcNyRKzlNX8dS1EVdF4iVUN8BVEdqoWkARSVFNM1DQFCQREUFdqmiKGiOIVUgzDFHNrEUkSxAWPGTch8SJJKpIioiKikHFZKkfMeD7yKBQGobePcjYdT4oGkdJ1G06+ZvfU3niScUfUIp1CB301JWeHqHZUnZcN8SO23cQnf6fSCIkKAeuFK45gV44ybdzI/9h5mGSp7OSr28h0xkHHC26YrlIMbBt6MwiDtWoLZLvw9iQ3VcrC4+J1nJQaSh4ysvffQXlHSX+7BefwGvG5J/8L3D4DmPl+ahWUFMAcohuCq4JxCoISAAaIAiKgnYR7WYWQIKIEZU8glVFESJw0ZbSLqa/Mr8lBQOjeaTsK1ZR52DrXeAQLJo6I+pAPIfv44o50XxBVME2rej5CmbB4TXVpSnc+vZtDEmNL/xJl1YHvKbSV4ar7vDw2w9hUwNJhl1JV/Gy6n7AwwRbwPcNYMhWCuHcSmTq24zxGg3V2UeU/pxou406H9KUfFml3jHaajrGbtghO151nQ4djGmeWiUOHQ0nLH/sBEPNE+RvLCAyBsWroOewGC8veEVU9qi6BuKWgPYW8XUoKajdolAKLnHQRimgCKKxqjOgZqtKb7JNF5DxEqbHOHWS/c1zW65NRZyIopieIvg+mvOQfE6oR2JPNbDLEbYW01mFuSdgvSam2laNJNWBFw9wOFhl5bhw+ouOke0wsC2P1qp4oUEji1h0bUl1sw2NBH8UzPo3SnvfBzqTQWl9uUZzZV77x0816Lm+KMSK2iaCEuQ9BsqOwSsG2P0v7yTIhRKf+AvNV2OGRoXHTyqBGK6NhQlPKDwftHUC6Z4B30B+EoLnC0YUPw9mBNw62A3ENTNdYDKTUYcSIZIAfaKqkgGHfCVPoUaRsT6kx1fnttiXWrAWRUX8QOgrIJ6CyeHqkXKyjjat0kiwTRUF0liYOw9P1NV9YQ3p7RX62hskCx6lcbhyUOi2BNNVXNjG9CoaKmKVsCKcPClUu5hEVXZlK3pa8Z6JgUxPY37/T2nt7+PFgZVrd/Wm1tPUBGUj4oBUxFSclEsq429+s0j0mNi5+0TbqE9KPhQeehTasZJXpVhPyQcp/uQwWCOCE003kfhxkXQObIImbcRuIH5eCPYbMamItkQ0FTTVjFFFxoiISAkVX2TtuNJogjHISC8MlcBuaUMEKfaIDE+IFAoZBq3Hqott7OMVONZU1lNoWtSC8UCdMHsCTs0pJ5qw2RbeeIdy/a0iaddBIuALw7vA1YBmRG5AoWXBwsojIifPqJ6tk98M+eS9TY7I18mjPaOa8H33wbtfTZ/t5sZ7jb5ytKAuiJwp9It4BdCOk3DJSs92MANttL6IxAYNu5I2YeU4XFhUFhpQDsB3Qm8U0zMAjBYQ44uID+TBWYhXkO4pJF4SbFtEE8RWwSj4gyD57CnQRFTbCAF4vbB2Aup1GO9Fhoqo+Eg+h/QPI/kcNCJhvSs6V0XPVVXPNFVXY+hk9Bgv83qQcYflU4YzF2C5Cxca0JcTbtgvTBxQMZopTAoBLnGklczLFoYFo4pdNcw+rJzbhLm2eBPbzUdu26MLm3O017PgSZ61QqanMffdh37428277tyv/+3Fu+0LG5tanK+J7wdGci3FzyvgpLmC5HaV8IohojmVThdPE6GBLD2uulqDuSauHKBFg7gYSs2Q0i6H+lZQD4fdirU9EB9REZK60D0H3RWwbTRtIM6KaFvU5BCvBK4FXgnWzogpxSIT/eAHkB+Dah03uwkXNnEnNoULDdjsKh0HXhbRq2bPgdsqqXgC8yeEE+eFjRQWurAZwa4+2NUL2670jQQqkmT0IMh55Esi3RWlOCjYFWH+IceJZfjiqogEpC/eqbc067xztMThw9v484fWSWa+ilK8p6O7M/fh/q8Xs/154/zWwSsLE6WDB3sLftusrCQmtELZKEkLxBcJV5Sea0fJ9frqKg2Mi3BNZOWLqhsrsNLGnqmSiyx+ziOxDkOC6kok+f4IM9wvolkUB2RsSBDEE5E8Ih7YLhJvIt0liDYQG6I2RVwCmkA4B0UfQhE9V8UdX8TNNpD1rmgzyZiuL6jJAP4irOhFnE/ARrB4QTh5Di40YaGjOtcm14rwt/eR7htBBjylOIhITtTFmiXAxbD5pMNLlIVjjmPn4IsbQjtRbnmBz+HbewJZj6lVuWa5y6PfVePYbeDP8ncz3/7Xo7uD/ZT78lLqG0ILb/wRs+P1DxnzX36fkw90efScMNSj7K1DQUBU0HZLTKcjGnpUjzudO42er4s9V8N3Ko9WU809uanXtp20RPCNCKXHLLmeGjreLxIEgk2y3IcTUKsqqcgWDoCPc5kStLMCZgMKIxC1oL6ZJcwqDklEjM0q8ZqTLYas2fK3crrOZbUtUXBbYc76svDkaVjtohfa6pZCctWEE4GwOVeXW44tSBrk1Ewk0DOhFIYgTR02cbS6ytojMLcBJ2pC0lZe9yp4xU+8SHrKZ2k80XKffQzXseSfM8vKeRgLgSaJr9U/JnYrXPedfQxdkefTv1WnGUK9huR6IUjaSqdDvArhGcfynLARofWO2pFecvkSlbmO/nCtwV/05HVf2ZPY9zWIH4O9zU2duN1KunsEVYs4FVV1gIjJik44C6KIZ9SZPkyuD4J+GNgtfOpe9FSE9/IRGA2hlkBLRWtWibiYQvlKal5UwIGzWcbWdZSVBeHcnGojQauRaC1GK110Q3nT3gJXjg7wka510ROLmJW20clFZXwfUhoTxFMNY6HSUGZbQiGvvOUnrubQ68bwwxN0PrlBYw2xHiZJvoFIXVNMveGCOA4oeTW1jXNiTYldN/bJbZtNTt/jWG0oxqC7lltanbM0FmG9pswvZ8Hv9TcHXqfqOp993N4V+LwuLfLdGy0+lzcaOMVFFi+NBb+vzVAhQYt5NFcAnKBbqVvPg1wZ/AJq8iImUFURKU2qmz2v7rEFlRij5yPkQA+4BvSImH6ErqJNxdUVTTNKCtllSQx0VWsV4dR5qCfoahfqVm3ipJzz5Mf3G3d6xwD/7Xl7vHTi4KSsnl5keTkRT4VAIVpxOrAn84ErsdBKldfd3cMN/3yCqLKKXV5FugZxWWir6deu1H7dEm7YQbsRmkROoIAE/RB2SJstdr9sWG767rJ4AVS7sP5ESmVRObsqenYB9Uby7H3jdrntx0fMwSvFcx2SVp0f/6NTPNZyfN+T6+Rmm5iFKjq/CfOPpNr8XFdZb6g264r4Ivky9Iyg5QkojkDQi5hcBuzFCbWthOijD2naEawI6eNNXC0PY9uQTgKeICVgCMykYCYE02+QfFZHo600augTp1TXQtWFNmxEJPNNKW92+c2/XHK/khp+rt/n5h3D0r35X7/Ce+W7tnPzKwPCNrK8obRDZHNWsQ7yRnn5G8a5/h2voXPis7izx3CR4FJFlazIrF8bu7+uQqyg4olGDYfbnMe4SLzAN54gSewY2OfxvJf5aCCy0YK1ltBpKwevEV7366+U533XLkmfWBPWUzPWh/Ed3UN9DP3pBY40urxlqY630UErLXVrHdHH71etzoM3tgftuwGKw5Drz6jtFuirJmAMznikn75HdTXZYkuqoqL6pTU0AcaHILHqUnEoinFIXpERMJMG02swBcPDJ+HEOqzH6HJMPN+itxLq0b9c0R8EpCD0DhbQvKaSLv+VlPobXPedZQ6/zscEyLkFdHEdck659tYhXvrWHaTn7sfrxHiJgQjiGqRxxq4dz8VCtlImtos0QiQORalvZDQExaUW6bSIayF7D6TsucLoRlWwsbLnujLX/NCtQnQWPfkw0nLEW/Uip+K3G1lnxr0V/sAJP9qKKUSIPrZiaDtDfrII/eMixn0lDfK3xXwLzqG9u3Ff/IxyooKXN5KVW0UlQKUa4x5ZQyfH0KL3t33sYrIlb2WEpQy5fqFQgoU2rMW4aiR9ja7cu3eE75/aImK+IS0GIr1FxDiLrbWINztM3gI7rzda60C1CeM7DIde34OtriHVNUzqicSKcRk2WJvFqWqfi0Kmv4IyximSxErrSx1QTzVNIIrRrZmYJEIH+1WHyjA84rP/jRPkR1qiS6eh6nCJSpJAlPWue6U+zAy4d9xI8MdzfCgRfnulpUXPww5tg8KuIVHtQV0r20QBzTK3GSvqGcfNnlB5ZAkv8LJioftKd6M4I6rLXdyX5mFiUCgEqHMoGeXNaK9AACqWkSFMfwmtReTXW3o8EP3uXz9Oi0OZa8l7eDZjZpLN2AnEqcZN4/a9rKDXv8jgHHgDPgQRLC+A9dC2VXVgIqGxpqRW1AtE3XNyWVsWEqXEYYRdXENrs5akEkEnVFpdtBkhsUM8Q6kAZVEmb99Fz64cbuHLSttA16mNUKOQDyDvYfqzeg7Vh7NW0Z4D/T8WqpkbzGl+bAz1Rw7hGAJtXmIcPqIp0nMoy3M9/JimLcHarGioKagK1gkO1CY4+3ATZBzZuQsyxWXpfBAshqIiJSjk0OFeXGLxLfzyn6yydhv4h0az+7OaVebVoiQh+IJ4HhJaXJhw1S2G0TFIQgdRlHGRuoVEcbESbcCZM2itq048JAjoPGuFzGSMXT6VcuHLi3rsywvkTp/VdO1THZU467iQrkLHItZgBHwftLaBq6zi2kZtM3U2QZNQyCsMltAeH9QjVZCtviw9eazurErSl3eUJkqqxR2K7WJMfusWMzej/i7U+NhPf5LkvDUOEU2cqNWLgZ5KFjxnhhUYl95zyjk7KObqW+QrjalWRa3LEvAeDPbhBgvY3jwUA0afktZQK1jxsiUTiojVLJZxinZSbOiI2pBaB60Y3QSJBPEMpms4+YDT82vYTy9J/tiGns4Z/mqrr8I+K1CfAvPwwySRx6+1rKazm7ils+j6g05NDWdSnDictq0msZI4SDoxWu9Ax6IRSKIkbWi1wDqxpZyUrt3OtQK6fGNmuk7p781pOW9IzfgoYkpqbFORHIK3VcPwoO8g7uFPYB9eQJ3J+qJAxKiRi9H9RYbvstjFrXRxj56BclkY7M0aHsxX+lZFfaPlUejrQftyQs6XAxeLR8fH0KkXUhztNc8LE7RSFel8oaXSchClqM1odBoqUbr1rkoKYQaYrAkrx5TzS+h8i7RhCeqW//SnS1S2+pr1WSnkKFmv6v84yR80Yu5ZaVGeX8fOPQ7zn1U2jyvayuK1KBI2m5AmComC9TBdkFhwVZjfRM6toVdNav6KbfK7d1/BK35jq3o2nGdiMK/9+QJpbrKMuhaqF7tNLSIFyPWiZz9B8uCcutg4capyMeK2Wd+aquC+Uu7IlmuKBj27QfrgI8i+/UYG+8UEIJ5BECUvku8XGezDxLG6dqSHABmbQo8exQ63+cU7rnKv2DPsooUNZ9oLWWZXrKBhlkkONwUbZcDtJYo4pX5OOf0Fx4MPw/kqbqlNsRHp8Vuu4PcAOcpXbxb8urT3eNZVo6fXef9inXSliXd+DT19Hs6fgOOfcWzOKgWj1KpCuB7hJSkkYJziYmFuVXhsSRjYJvLau4s6mGds0Jff/KmXcgDQAubWkaIUhkdw/lgOF1dQ7WSuRx1S2gGRR/rRh5SuqgQKDsU5tRa1qerF+tXF5LZsFUnVKtYK6UNrqgtVJ9tGFSOI57nsHxUNkN5ePM+QRJb9L5lg59Gj2DdfZd50aEDeceu372kdeuUVUqvBiSVh85glWrVoAr4H1VVIQvBiJZ5zcv4RuPd+5b6TcLYNmzG6ERGECb/8aw/RmMr2XZ9T+v046BR4f9bgwo4cSRhxVyfx0uW6mDQFLxXiOviJ0G4rpRIytENEm1aSFrI5izw+K4KnfOdPvITJW3dJ7sSFuFU322ptveaBFX73JTvNDx/s0+t2X0Ey+LKDvohDbEMEhMJ+1Hi4ez9Fcr6DGtAsyEKd4C4qwgnGUzx/a3idLDWiNnNfLhHYbCO7yiLjfUKtuZXbUjRVaW+InJnHtRIGkpg/u/VK6gd7+eM7Dmn/jre/W3oPDnrrDz3K3JIhj2Ii6OkDMYaFM1DdVIoBrM4Lp+ZgtQOzTfR8Fbvapid2/Nkn1vjpaTC/ztdupX1G9ZCpaeS++9A3PZ8bDm3nrpGCqu+r+CZbfLUG82tIpJhiARnsR9IYWTuNnFsQ8fNObrpzQHe+6nmkS48zVm56aZ3o2CwHrt8u48VAbri6323bc1NRSzfdKBK1wIUGDNK3E/fZB0g/PYvzDS5RnJOtV5YgFITAKDkPxANrM0U5p5lCNFOWq1rRta74t4yjm5to5HAqiCBeCKuLaDMicD5ndvXKXXfs1ddc/fpdYXBFGuS7j8pgfpO5J4T1OuSBomRu6twpqLWFtSqcmYNaC6IYYptlfIZ60P4i7VKOj/52g8bTFai+ftfJVj/vO2707tpRtr9w+MZSd/Blb82lzc+RM3NibV6iMKS11OHxv4g4cQ68HmGkxxF2YLMOu/YaJl84jq09iVYWlILo6F687Y8Tnt7UH+wJXDQ5SFTcuc0IDk06YHqV8g7R0w9gHz6F9QxYzZp9bJYUNCJ4HkgKlQrUQhgfh/6h7BF0Vi6CSVbZ9EXcWkzyqSX8q3sEEmWzgxSM9o05JgfUe2yVOG94j3bVNwW/k7thLMfqZ+g2uozuEpm8UnniQdXuKHRqQs6prCwbabQc2yfRq79jhOKgw4WxujQVF6deddbGn/y43jzs8evAGy7pwtBnrZDjxzNtrjXsgVafFHNE4Y4bRsSwHeINIciDZ7BrKT4pF44ps2eVZAw6XcHEytgLJsjtKUt8+hFV8Ym6KXv2wi37MQtfIOrNIbkSkt81LBrVwUZIeTuuUSX842MkdcH4YLL4TxRVMUKrrsSJsLamLGxCPYH+FWHfOGwfgaGRLDJ2DlyGtSgO+9lNZGwb/p4ybGbNFKYIwwMZdQ9DejTF7bqrYILyOu58G9P1cPgcvFJl+WTKRhPKPUo3hB7jmHxpL9d/h5G+awcgSGC9DiuxIsLZdRUvJWnHTGwpwn0tK3nGraRiWIkS1eqFVLqf/b81ODQs2gyVNN2q8qVc+2qRKw4Lp/5KaaxaGhFSHoD+0RTXWhYbOsWKGCviW3RyQGX3IMSqpEWBXiBag6AfbaPJXz5EWs86rFyqqJeBqMbQbMCpC7DaULoWVsKsT2qbKrUWrG0IB3fB8LCQyylWM34tAuqj0cfWVO4cNObKEThbcc4ohQKUfbAW2b9DvMH+jrAWI7En4sCmlon9ovv2ovc/ke3e7gHk8NuvZNud+2DxcxodO484xTYdRgW7IWw+AbkcgVpm2WKuM18DR76uQg4d3ersh5NxQss6CtE5xd/VBeNUozjTdaqEVVXfV665BS58BtprSLkIEKO1ELoYz8cZB+pEfC9rZgtQeifyeAWLxl3MthuJP/Z54seqqnlBE9QhJKHSDZHlClTqSjWG1a6w2ETXQnUWaMeYiTJim9A8I4yuKBMj6EAflMrZfIGoqms54s/VtfR9uyRttQyd0PWPCttLKieqW1nZqiDDKSSCpOC6Trv1LIUuPgwEsPtlPYzeWcbOfwnaiZjUc9q1GBU8HzYXlLWa0EVJHKcB7s1YlntOoH7f1s+4Qn3XEFN9RbZ7kdp8jzGlvR7asRmjsS6jmuKBQ3IW0ZbiKRRKsZQGYmijxgGdjP2sLggPnoXdQ3Dd7SMUrr5GiFqSPnRC4gfOYB14oogKjbowtyA8fAEWmzDfzqp6lQhXjzCtlEJsCchgJYksdFKkGsFyVWi3oOgJPpDPiRgfEzcc0dmWBvt8lSTFtyKNJWSuigz4Itddr5IfE3FNkERUEtHuBlRXhPFeYbIfRm4WpL0sdBI0chA7EadqfGjNGY7dr5yu4E7Xya2F/Pe5kEf3gJl9rhYC6BawR13H6eUGN4z2kQzPxuT7HcX+rMIkThArojiVvGjPFUJxzlLZRGqzytDeLQjrKi6E1An1GDqRMFxWKWzfjfbeLO7xL1L7+KJqnKU/qnVYXlc2mspGImwkUO8K1Vht1+KFKcV6TMcif53zWajG+ppE2ZX3IGc0LudEB/NIxwobHRjuUfaOG4b7lWIB7Z5LCMuW8q1l8u1QxodSBvJCsw3tTSjFijZUnYqKQNSEsANiofcakWDY4ZZBbJqBgqcoIoEVXXhMOT2r1AWv0qXdTXni4iTBfd9Is/VFYK90eHC5JXePbEL0oGXitOXgHYaeK4S0BtrRrU5DUCOUJuDJ02gjVNm2C8qTWT/Cxa7P1UqWuRsYQYKDO5CFB0j+alFt17Beh42KUmlkKZlaCmuxstpB10PSzYggUmo5Xz5inf7qAxU9CTD1Qor1RfO93dC9WZSrS0aLpQBG8yITJaVjod5VxsvCWK8y1Af5U07i/oieq0qURpp44rjQhMWTwvB2SGPwfcV4wuo8bK4pO68QRp9vSOYt2kFFwfOQwFfSusrZL6DHnoSGwy22CZyyHBV5ksbfmxx79go5uoUjmxF/kazpD5VgV1QS1xuoWf2Co2cWekpCcadR8NCuJe1CLicMDkKUKBtnRU0A+ZxiY/CsYhOhN1AcQndxkegzp6mch8W2srimUotEN2OoxlBLha5V2qk4P4/ryclfW6/473fsHTrlt+o91x1Inx9GiWnVk+7QbvfxeosHalWu8VN5l0v1cNeqbcbIcAdGe1SSFNaqyEAeJgaRUj1mvFCiiU/iEubasLAO12wqpgwmgeoFpVaFgUFkYkyhDdJWVZtlNltrItVZaDeUU+eReox2LSw3MZsJf/RYhfbTAfqzYVlua0jy1FsP8KFmxAcrnrbOb5Jbq8HgGRgbV/Jns/4vm2ZU0xPBWWStjopRjBP6xyFvoFmBblcxPnL2hFL76Qcxii7XRC1QjYTZurLWzcb5ir7S68NYQaUvj3PovsS2P8RKe6i3gNffg7MeXg289XlMCVrbhUq+qH0FgyvmkVoItRipx7DSgp4c0hfAqTr0F2BosarnK9BMEIfQbUPagkI/VM4Ii/PK3Cbi+SJ989Bcsy5J2DphRwg7qut14eymkOKIU1ylSy5RHri/ws9sKUO/KRNUxzIrkVT46HyD9/sGv+iTtgxeQ5HqKiRWAINaR6uTpSV8H833IAsbSBqpjjfRoaFshrcbw3wTnIG1UAgjJY6yzGmiEBiY7IEcUChAf69hZCQwY+OBn+/r3TcwPur1jvSkPYO+NYGvLj5jJKnpxrlEW5V0oFlnNGpB2lFNt4pkjQjaobJUh/UmVDNXg/Ggpy44VKsxXDuiMlaGsAKrG6InTyjzFWSjjeQ9pVWFvLc1y2iE1CkporFVGgphBPUudraJqXX5XUDvzUhU+oxP5XkmsyIz4G4f423bSnxoTz/hYA7Pg6AVIr7L+qb7BmHn4SGGr97H0Hie/tySaR6fU19EkxVLY1mxAueXkZPryFoHbtwj9PR6FCbzmisVdWzMJ1hZh66l7/ZJgrFRSgND5PsmCIqJSuFWNDcJ9jwuraNOMPUjSm0ek6pqO8ELFYwn1jmTdi1Jy6IY6uecPPawEzsSkB8M6G5G1JaUeNNxroo2YuTmbbB7RBjqVW01UEZ9hm4bN1ES0zM+Qby26WY/s0R93dGswnotC0xrEXgi6lTjuRa9zYj7017u+vwC0aUDwt8UhWzVSLyjYO+a4Ec9+MDOMumgL/7ubWqufskE44dvlG2TZ3VwxEJpOyQt6CwJzQZ0Ew3nLctfsnL+tFJpIs1QKPUJd7zE0Xv1sBZe8/0Cpxz1WVhqYisreHv7xPk9OOeroygm53D+JEgf2E3UdhTbhPUT6HqESTzN5tTJJuIvdkN2sxqvJphO21B+QS+5iQLUG9jFlMrHEu4/pXxpCXb0C4UAd+12Zft1eQZf0kdxQgUj4PUoSYhrNYlsnuaqZeXLbc48qXzmftXFDmmslDYjHgxyfMen1lj9eqNszyq5+JTsL1Pg/XmLz032EIYpNw72mJ7vuB15wT8bZPyl10jOnpO0ukq6sYxdWcatNSWtp5rWEiRV+oegvyDYDlpro71FZfd2VKIYDb6safUMaa1Banw0Z3H1inGNphA2VJIGeJEIDvEHRby8iMaCMdCpYKIEnIhBRWJBIkW7CnHWQoOC1ysUdviinpIshtj5iMbplNlZ4VwFltuwvQ9esAc9cKPP4K1FMWIlWW+qbUTYpU3SShsbKUY8SmVhdDClL4WF08q5Bqbr+ExguPuT66zwNOn2b1ghF1Py0+D/TpvPHuxlZXsfdxdTicJjNRnpPoq2qmJAJE6hmyKSzULRZmt2QrBdSBtQb8GFDZidh74Ael2EP2yQnIesrWOSCOMFggr4nmqwBXsaIVhBDOJCRHJCa1Wl04V0K6kYcUmRBIxkB9NIXgyRg7Ukq4s3hOOfh8dmYa6RBY/Xj8KOIaRnmyBehDYiFZWsdSbNXho6vEZMOh/zuT9Qve9+dXMd8gttPv3XFe4826HJ00Tl39TDZ7aUYrpdKlGqrt5wWqmLnr3X0+X7RbtzidK0xsuL0VSxjayv1vfByyk9vcrYBLzgkDBYFhaqWWa4dl6wocGUAsT3sybrxCGxQphA2IU4Fkm7RmwDsXVIm+BaSKrQBXWKplvNaamiVr9y1J0AYlEpeJiC4AGNOajXVTdj1UYXPTgiOjos2jci5ApOBBExBqxmTR0XK/2RsPiAcPxvRGfX0PmuuFqKRtlhRDr9LJXxDZ+XNQPuNXkqax30XFVcvaVsNKy3vYksnofJ/cLgftHAc5iLQ7Ix2KZQX1HmF6HRyRqdDfDkBaRZVW66MtXBIMTFZF3cSXYumG7hgfT4IpICESItoAlpqnQTNM0swYVbMx8iX+nrdQ7EUyQwIjjSEJKKMLegenYDnW8aip6y2VROLGbaG1dkIFLyQ8aYIiRdp1EDrc1DbU05cww9V0crFixqWwnGOuYvadx5VuJ9oxay49+w/Pj9lMOUVxQ8oihB4wiDRVpr6MpxpbkGQQrNc8rykzB/Cs7MCitVoR5CI8yqbWmapcUKNSf+SiKBpxKMeyLq8As+Ug5EPCMYT1QDXCtSWwtxTYtrdlUrEa6dNU9LklmDyQmmx2BQTCCYsuD3KrahEp5VPfOo6skLGUNKnTKUzyYa0gTqTaGypFq9AJ15RKtK65zK4w+gTzwJFxZx64mwmeAiSBdb9K20+cSQ4ftPhk8/3PlNY1lf7f0i6B1j/Pxgnp/Z24sZytMueHjlnJhiAB5K0cue0thBYgQRJSeCU6XRBasQprDRhh0DIpP9KodfJpQOeBrXnMahJ0kHkrrTqKMkMSRdRzeEqJu1ZAcG0a0J5yDIWrGCAPJFCDxFAoEewe9x9PcKm6eULz0M8w04U4cdfVn6fbiUdfkkZM15xql4FvEF/Bw0Yly9i2vGaGixGxH5lQ7BZpcjzuNtD1RoPlNW9c1WyKXX0dvHeGWP4UfKOV7bn8NOlAk9MNbhT/QJoyXwTVbKDmOhFiqNSAgTpZNCK4YeD64cEdQpV+2AqJvBBgqRzZQmXhbvhF2hv6js2w3GR4NMz6yuwex6xnpTq+QM+JKdHyDZyCc9PUo7hDBE/Jzo5xeVvjw6XITePNKb1d0QyIZYNBsCXWrgal20a0k6ilcJKVa6nAst7/9cnf9+6X58Kyzk7wWNAC8f5Z2+8K6BAgeLBg4MEO0aEBN4EMVKmMBGB5oJ2rVo14o2E6UgePsH4AU7Ybg36+SoNyFKoZNCPcp+pluM6abnCVe/wKN/QCG1EAtpC9qbKmsb8MATWVe950HOh2IAffksA+AJFDzEeFDrin5hWbUR48o+brCAFAI8PzM2Sjnoy2XXObuJHqtAx5K3QjNO+cMk4ec+12btktTIcz4I85t2EPB9W90px4Dv6/DQSJ7fixI+r464GHCTc3TPbyILTVwlwoVWNLJ41Ujya6EGG12C4SLRRAlJFOnvhZG+rbk/B61YqHSFjRBW2jBaFl5+rbLt5hzeFT6mlNVjghLkiwYNlfVNWG7CbAsCX3QgDyUfhnqQyQEYKgvNSFiqK12HW2gj9ZiexBGkWYuV61hsI0Y3O1AP0U6CWQpJawm/IMJ7Pl3ltxcS2lPg/Trf+FGx/yBnm196DNFtuxkotvnS9jJ7fUibCX5XIbRC6uhYZS5R/byB6kSRH91dJuwvICO9SKBZ7SGysBIKoYV2qlqP0BsnxBwcVdk7gVxxMxSv8JCOI12B5ceUx86ij6zAchudbYpuL6oM5tCij5QDZLCI5AKh0lJtxyRLXUpP1OS85/QDCneWA15UCNiRN3gmsyYCIV0Nxd+M9f2fqfLeS9b6DR8P+w+qkIvXvhH8hyG5dZy9QcIHE8cB5zilwuOpx5cFjg0Oce5jZ7JDMe8Y5jcMvH1/P43t5Yx1tUI0MUhkIQF/PSTvCWbvIM0dvTBaFn/fkJrtu5Dh7cL6l9FzS6pP1tEnK6SNiKBpKQwWcf0eYWCwLkWKHqYcQNtiFzsUNlPC9YjvebCa9d3eOUi/n+eATTgcWW4ycJUYdncsv/pgnV++EYJ94L7e+Vf/lBTCUwFuFMrr/P2vFroN/DHQo2Bf3M9PlAN+YSDABoLtpngdpZA4xClNJ5zPwWJvnhfuGZSg5GvS51Pc0ScyWIa5FXSlra6ZEi91KG90WEZ4wCn7Ao8DeUNf3mADSH3QTUtxqcs9ScJPPhryhUvv5alB9LX99D9ep/oPvVn/GGKyXvEM/O8Fs7VovSQDKltHF7mbenlLYPhhPysohmI4j+Gzns9DfR5n/2KZzgv7uHukyAcm+9g1nKcTCH7qRKqh2k6Kpo5SPeLBtTbv+nyHL+2H/Fg/Vxs47Hu8EmWvEwpxyheqAT9yskLzKSe+yTTIJfdqn0pe/neQZ/IAXEznmN27KXy191w8F/fGPq749nE+/r170B85SPq2vaRv3oXeNUT31jL//tsm6Lno5596jd1QuHHr71/rf77Kvf8f+c1xPPUg4inwpsDb+r08ZQO9V47w3teM8fgrR3j0zmHuu2OYl3+Va8k0mNvAf8r1/8/d6OdgTV9vsy7d2NyWRV2qCLn8xH8LFPdUdzPF/wJftPJ/kEVdlstyWS7LZbksl+WyXJbLclkuy2W5LJflslyWy3JZ/hHk/wf+1VoL4Ku+LwAAAABJRU5ErkJggg==",
    "shout": "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",
    "cross": "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",
    "check": "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",
    "hourglass": "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",
    "info": "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",
    "bell": "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",
    "noentry": "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",
    "exclaim": "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",
    "scroll": "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",
    "trophy": "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",
    "ticket": "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",
    "triangle": "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",
    "flag": "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",
    "medal_first": "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",
    "refresh": "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",
    "party": "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",
    "unlock": "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",
    "clipboard": "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",
    "people": "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",
    "gamepad": "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",
    "chain": "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",
    "cap": "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",
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
    rank_emoji = custom_emoji_html("shout", msg_rank[1]) if msg_rank[1] == "🗣" else msg_rank[1]
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
        f"{rank_emoji} <b>{msg_rank[2]}</b> — {msgs} {messages_word(msgs)}",
        next_line,
        "",
        f"{custom_emoji_html('bag', '🛍')} <b>Покупок:</b> {buys}",
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
        spawn_task(delete_later(context.bot, [(MAIN_CHAT_ID, cur["message_id"])], 60))
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
CD_DEFAULTS = {"dice": 60, "duel": 60}


def cd_seconds(kind):
    """Кулдаун в секундах: кубик (dice) или дуэль (duel). Меняется командой владельца /кд."""
    value = data.get("cooldowns", {}).get(kind)
    return int(value) if value is not None else CD_DEFAULTS[kind]


def dice_cooldown():
    return timedelta(seconds=cd_seconds("dice"))


DICE_MSG_TTL = 1800  # сообщения кубика и дуэли удаляются через 30 минут
DICE_STREAK_NEED = 3   # сколько выигрышей подряд нужно для бонуса
DICE_STREAK_BONUS = 2  # бонус за следующий выигрыш
DICE_WEEK_PRIZE = 20   # приз первому по кубику за неделю


def dice_bet(user_id):
    return int(data.get("dice_bet", {}).get(str(user_id), DICE_STAKE))


def dice_panel_text(user_id):
    stake = dice_bet(user_id)
    balance = ds_balance(user_id)
    return (
        "🎲 <b>Кубик</b>\n\n"
        f"Ставка: <b>{stake} {coins_word(stake)}</b>\n"
        f"🪙 Баланс: <b>{balance} {coins_word(balance)}</b>\n\n"
        "Что выпадет:\n"
        f"▫️ 6 — выигрыш +{(DICE_MULT[6] - 1) * stake}\n"
        "▫️ 5 — ставка возвращается\n"
        "▫️ 1–4 — ставка теряется\n\n"
        "Выбери ставку и нажми «🎲 Бросить»."
    )


def dice_panel_markup(user_id):
    stake = dice_bet(user_id)
    bets = [InlineKeyboardButton(f"{b}{' 🎲' if b == stake else ''}", callback_data=f"dc:{user_id}:bet:{b}")
            for b in DICE_BETS]
    return InlineKeyboardMarkup([bets, [InlineKeyboardButton("🎲 Бросить", callback_data=f"dc:{user_id}:roll")]])


def dice_check(user, stake):
    """Возвращает текст ошибки или None, если бросок можно сделать."""
    last = parse_dt(data.setdefault("dice_last", {}).get(str(user.id)))
    if last and now_utc() - last < dice_cooldown():
        left = int((dice_cooldown() - (now_utc() - last)).total_seconds()) + 1
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


_BG_TASKS = set()


def spawn_task(coro):
    """Фоновая задача со ссылкой: иначе asyncio может удалить задачу раньше времени."""
    task = asyncio.create_task(coro)
    _BG_TASKS.add(task)
    task.add_done_callback(_BG_TASKS.discard)
    return task


def schedule_delete(bot, chat_id, message_id, delay):
    spawn_task(delete_later(bot, [(chat_id, message_id)], delay))


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
    # /кубик можно вызвать не чаще, чем раз в dice_cooldown(), как и бросок
    last = parse_dt(data.setdefault("dice_panel_last", {}).get(str(user.id)))
    if last and now_utc() - last < dice_cooldown():
        left = int((dice_cooldown() - (now_utc() - last)).total_seconds()) + 1
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


async def myid_command(update, context):
    """/myid в личке: показывает Telegram ID написавшего — чтобы сверить с OWNER_ID."""
    message, user = update.effective_message, update.effective_user
    if not message or not user:
        return
    owner_note = "✅ Это совпадает с OWNER_ID." if is_owner(user.id) else (
        f"⚠️ Не совпадает с OWNER_ID (сейчас: {OWNER_ID or 'не задан'}). Поменяй OWNER_ID в настройках хостинга.")
    await message.reply_text(f"Твой Telegram ID: <code>{user.id}</code>\n{owner_note}", parse_mode=ParseMode.HTML)


async def cooldown_command(update, context):
    """Владелец, в личке: /кд кубик 60 или /кд дуэль 90. Без аргументов показывает текущие значения."""
    message, user = update.effective_message, update.effective_user
    if not message or not user or not is_owner(user.id):
        return
    args = command_args(message)
    names = {"кубик": "dice", "дуэль": "duel"}
    if len(args) < 2:
        await message.reply_text(
            "⏱ Кулдауны:\n"
            f"🎲 кубик: {cd_seconds('dice')} сек.\n"
            f"⚔️ дуэль: {cd_seconds('duel')} сек.\n\n"
            "Изменить: <code>/кд кубик 60</code> или <code>/кд дуэль 90</code>",
            parse_mode=ParseMode.HTML)
        return
    kind = names.get(args[0].lower())
    if kind is None or not args[1].isdigit():
        await message.reply_text("Формат: <code>/кд кубик 60</code> или <code>/кд дуэль 90</code>",
                                 parse_mode=ParseMode.HTML)
        return
    seconds = max(0, min(int(args[1]), 3600))
    data.setdefault("cooldowns", {})[kind] = seconds
    save_data()
    label = "кубик" if kind == "dice" else "дуэль"
    await message.reply_text(f"✅ Кулдаун {label}: {seconds} сек.")


async def delete_command_later(update, context):
    """Команды в основном чате удаляются через 30 минут (вместе с ответами бота на них)."""
    msg = update.effective_message
    if not msg:
        return
    now = now_utc().timestamp()
    for old_id in [k for k, v in CMD_MSG_IDS.items() if now - v > 7200]:
        CMD_MSG_IDS.pop(old_id, None)
    CMD_MSG_IDS[msg.message_id] = now
    schedule_delete(context.bot, msg.chat.id, msg.message_id, 1800)


async def duel_command(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or is_hidden(user.id):
        return
    if not await is_main_member(context, user.id):
        return
    cd_last = data.setdefault("duel_cd", {}).get(str(user.id))
    if cd_last and now_utc() - parse_dt(cd_last) < timedelta(seconds=cd_seconds("duel")):
        left = cd_seconds("duel") - int((now_utc() - parse_dt(cd_last)).total_seconds())
        await message.reply_text(f"⏳ Новую дуэль можно начать через {max(left, 1)} сек.")
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
    spawn_task(duel_expire(context, duel_id))


def duel_roll_markup(duel_id):
    return InlineKeyboardMarkup([[InlineKeyboardButton("🎲 Бросить", callback_data=f"du:roll:{duel_id}")]])


def duel_rolls_status(duel):
    rolls = duel.get("rolls", {})
    lines = []
    for uid in (duel["challenger"], duel["target"]):
        if str(uid) in rolls:
            lines.append(f"🎲 {saved_user_link(uid)} — <b>{rolls[str(uid)]}</b>")
        else:
            lines.append(f"🎲 {saved_user_link(uid)} — ждем бросок")
    return "\n".join(lines) + "\n\nНажмите «🎲 Бросить», чтобы кинуть кубик."


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
    scores = (f"🎲 {saved_user_link(duel['challenger'])} — <b>{v_ch}</b>\n"
              f"🎲 {saved_user_link(duel['target'])} — <b>{v_tg}</b>\n")
    if v_ch == v_tg:
        for uid in (duel["challenger"], duel["target"]):
            coins[str(uid)] = ds_balance(uid) + bet
        status = scores + "Ничья — ставки возвращены."
    else:
        winner = duel["challenger"] if v_ch > v_tg else duel["target"]
        coins[str(winner)] = ds_balance(winner) + pot
        status = scores + "\n" + f"🏆 Победитель: {saved_user_link(winner)}, забирает <b>{pot} {coins_word(pot)}</b>"
        log_action(winner, "duel_win", winner, details=f"дуэль, банк {pot}")
    data["duels"].pop(duel_id, None)
    save_data()
    schedule_delete(context.bot, MAIN_CHAT_ID, duel["msg"], 1800)
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
        spawn_task(duel_roll_expire(context, duel_id))
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
MAFIA_DAY_PHRASES = [
    "Солнце всходит, подсушивая на тротуарах пролитую ночью кровь. Город просыпается и осторожно смотрит друг на друга.",
    "Первые лучи упали на крыши DestroyCraft. Кто-то не досчитался соседа, и никто не спешит признаваться.",
    "Утро пахнет дымом кузниц и свежими блоками. В чате тихо, слишком тихо для такого утра.",
    "На рассвете над островами DestroyCraft гуляет туман. Под ним кто-то спрятал нож и улыбку.",
    "Солнце встает над шахтами и фермами. Город просыпается, и каждый проверяет, на месте ли его друзья.",
    "Петухи пропели раньше обычного. Значит, ночь была не такой спокойной, как хотелось бы.",
]
MAFIA_NIGHT_PHRASES = [
    "Город засыпает. Где-то скрипит половица...",
    "Ночь опустилась на город. Кто-то уже не спит...",
    "Фонари гаснут. В тишине слышны чужие шаги...",
    "Луна скрылась за тучами. Город затих...",
]
MAFIA_ACTION_LINES = {
    "kill": "🤵🏻 Мафия выбрала жертву...",
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
    "mafia": ("🤵🏻 Мафия",
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
    return ("🤵🏻 Открыт набор в мафию. Жми кнопку «🙋 Играть».\n\n"
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
    spawn_task(mafia_lobby_watch(context, game))


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
                       "🔍 Кого проверяешь этой ночью?" if mode == "check" else "🤵🏻 В кого стреляешь этой ночью?",
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
    game.task = spawn_task(mafia_loop(context, game))


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
        f"🌙 <b>НОЧЬ {game.day}</b>\n\n{random.choice(MAFIA_NIGHT_PHRASES)}\n\n⏳ На выбор 1 минута",
        photo_key="night"))
    await mafia_mute_alive(context, game, True)
    prompts = {
        "mafia": ("🤵🏻 Выбери жертву этой ночью:", "kill"),
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
                InlineKeyboardButton("🤵🏻 Стрелять", callback_data=f"mf:mode:{game.id}:shoot"),
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
        f"<i>{random.choice(MAFIA_DAY_PHRASES)}</i>",
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
    return ("🗳 <b>ГОЛОСОВАНИЕ</b>\n\n"
            "🧐 Кого казнить?\n\n" + "\n".join(lines) +
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
    text = (f"⚖️ <b>КАЗНЬ</b>\n\n"
            f"<b>Вы действительно хотите казнить {name}?</b>\n\n"
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


async def mafia_notify_night(context, game, blocked, dead):
    """Пишет игрокам в личку, что с ними происходило этой ночью."""
    docs = data.setdefault("fake_docs", {})
    for actor, target in game.actions["check"].items():
        if actor in blocked or target not in game.players:
            continue
        checked = game.players[target]
        role = checked["role"]
        shown = role
        if MAFIA_SIDE[role] == "mafia" and int(docs.get(str(target), 0)) > 0:
            docs[str(target)] = int(docs[str(target)]) - 1
            save_data()
            shown = "mirny"
            await mafia_dm(context, target, "🧾 Комиссар проверил тебя, но твой фальшивый документ сработал.")
        else:
            await mafia_dm(context, target, "🕵️ Этой ночью тебя проверял комиссар.")
        if shown == "don":
            shown = "mirny"
        await mafia_dm(context, actor,
                       f"🕵️ <b>В ходе проверки оказалось:</b> {esc(checked['name'])} является — "
                       f"{MAFIA_ROLES[shown][0]}")
    healed_by = {}
    for doctor, healed in game.actions["heal"].items():
        if doctor in blocked or healed not in game.players:
            continue
        healed_by.setdefault(healed, []).append(doctor)
        if healed != doctor:
            await mafia_dm(context, healed, "💉 Этой ночью тебя лечил доктор.")
    guard_by = {}
    for actor, target in game.actions["guard"].items():
        if actor not in blocked and target in game.players:
            guard_by[target] = actor
    attacked = set()
    for kind in ("kill", "mkill", "shoot"):
        for actor, target in game.actions[kind].items():
            if actor not in blocked and target in game.players:
                attacked.add(target)
    for target in attacked:
        if target in dead:
            continue
        name = game.players[target].get("link", esc(game.players[target]["name"]))
        if target in healed_by:
            await mafia_dm(context, target, "🛡 Этой ночью на тебя напали, но тебя спасли.")
            for doctor in healed_by[target]:
                if doctor != target:
                    await mafia_dm(context, doctor, f"💉 Ты спас {name} от нападения.")
        elif target in guard_by:
            await mafia_dm(context, target, "🛡 Этой ночью на тебя напали, но тебя защитили.")
            guard = guard_by[target]
            if game.players[guard]["alive"] and guard != target:
                await mafia_dm(context, guard, f"🛡 Ты защитил {name} от нападения.")


async def mafia_loop(context, game):
    try:
        while True:
            await mafia_night(context, game)
            await mafia_track_afk(context, game, ROLE_KINDS)
            dead, blocked = mafia_resolve_night(game)
            await mafia_notify_night(context, game, blocked, dead)
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
                f"{custom_emoji_html('shout', '🗣')} Кто-то из жителей слышал крик {player.get('link', esc(player['name']))} "
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


FAKE_DOC_PRICE = 300


def mafia_shop_text(uid):
    docs = int(data.get("fake_docs", {}).get(str(uid), 0))
    return ("🕵️ <b>Магазин мафии</b>\n\n"
            f"🧾 Фальшивый документ — <b>{FAKE_DOC_PRICE} DS коинов</b>\n"
            "Если тебя проверит комиссар, он увидит мирного жителя.\n\n"
            f"У тебя: <b>{docs}</b> шт.")


def mafia_shop_markup():
    return InlineKeyboardMarkup([[InlineKeyboardButton("🧾 Купить документ", callback_data="mshop:buy")]])


async def mafia_shop_command(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot:
        return
    await message.reply_text(mafia_shop_text(user.id), parse_mode=ParseMode.HTML,
                             reply_markup=mafia_shop_markup(), **NO_PREVIEW)


async def mafia_shop_callback(update, context):
    query = update.callback_query
    user = query.from_user
    if ds_balance(user.id) < FAKE_DOC_PRICE:
        await query.answer(f"Нужно {FAKE_DOC_PRICE} DS коинов, у тебя {ds_balance(user.id)}", show_alert=True)
        return
    data.setdefault("ds_coins", {})[str(user.id)] = ds_balance(user.id) - FAKE_DOC_PRICE
    docs = data.setdefault("fake_docs", {})
    docs[str(user.id)] = int(docs.get(str(user.id), 0)) + 1
    save_data()
    await query.answer("✅ Документ куплен")
    try:
        await query.message.edit_text(mafia_shop_text(user.id), parse_mode=ParseMode.HTML,
                                      reply_markup=mafia_shop_markup(), **NO_PREVIEW)
    except TelegramError:
        pass


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
    games = data.get("mafia_games", {})
    lines = []
    for i, (u, v) in enumerate(ranking):
        played = max(int(games.get(str(u), 0)), v)
        percent = round(v * 100 / played) if played else 0
        place = medals[i] if i < 3 else f"{i + 1}."
        lines.append(f"{place} {saved_user_link(u)} — <b>{v}</b> побед из {played} игр ({percent}%)")
    await message.reply_text("🎭 <b>Топ мафии по выигрышам:</b>\n\n" + "\n".join(lines),
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
        only_messages & private & filters.Regex(r"(?i)^/(mafiashop|мафиямагазин)(?:@\w+)?(?:\s|$)"),
        mafia_shop_command), group=0)
    application.add_handler(CallbackQueryHandler(mafia_shop_callback, pattern=r"^mshop:buy$"), group=0)
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

    application.add_handler(MessageHandler(
        only_messages & filters.Chat(chat_id=MAIN_CHAT_ID) & filters.COMMAND,
        delete_command_later), group=-5)
    ROUTES["/викторина"] = quiz_command  # регистрируем здесь: функция объявлена ниже ROUTES
    ROUTES["/выдатькоины"] = grant_coins_command
    ROUTES["/шопс"] = shop_admin_command
    ROUTES["/скрыть"] = hide_command
    ROUTES["/пользователи"] = users_count_command
    ROUTES["/эмодзисоздать"] = emoji_set_create
    ROUTES["/кд"] = cooldown_command
    application.add_handler(MessageHandler(
        only_messages & private & filters.Regex(r"(?i)^/myid(?:@\w+)?(?:\s|$)"), myid_command), group=-3)
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
