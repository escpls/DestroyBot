"""Тесты логики бота. Запуск: python3 test_bot.py
Библиотека python-telegram-bot не нужна: вместо неё используются заглушки.
Для боевой проверки запустите те же тесты с установленной библиотекой (уберите блок заглушек)."""
import asyncio
import importlib.util
import os
import sys
import tempfile
import types
from datetime import timedelta

# ---------- заглушки telegram ----------
class _Dummy:
    def __init__(self, *args, **kwargs):
        self.args, self.kwargs = args, kwargs


def _module(name, **attrs):
    mod = types.ModuleType(name)
    mod.__getattr__ = lambda attr: _Dummy
    for key, value in attrs.items():
        setattr(mod, key, value)
    sys.modules[name] = mod
    return mod


class ParseMode:
    HTML = "HTML"


class ChatMemberStatus:
    MEMBER, ADMINISTRATOR, OWNER, RESTRICTED, BANNED = "member", "administrator", "creator", "restricted", "kicked"


class TelegramError(Exception):
    pass


class BadRequest(TelegramError):
    pass


class NetworkError(TelegramError):
    pass


class TimedOut(TelegramError):
    pass


class MessageEntity:
    def __init__(self, type, offset, length, url=None, user=None):
        self.type, self.offset, self.length, self.url, self.user = type, offset, length, url, user


class User:
    def __init__(self, id, first_name, is_bot=False):
        self.id, self.first_name, self.is_bot = id, first_name, is_bot


class ExtBot:
    """Записывает вызовы вместо похода в Telegram."""
    def __init__(self, token=None, **kwargs):
        self.calls = []
        self.fail_markup = None  # исключение, которое вернёт edit_message_reply_markup

    async def _record(self, name, *args, **kwargs):
        self.calls.append((name, args, kwargs))
        return types.SimpleNamespace(message_id=1)

    async def send_message(self, *args, **kwargs):
        return await self._record("send_message", *args, **kwargs)

    async def edit_message_text(self, *args, **kwargs):
        return await self._record("edit_message_text", *args, **kwargs)

    async def send_photo(self, *args, **kwargs):
        return await self._record("send_photo", *args, **kwargs)

    async def edit_message_caption(self, *args, **kwargs):
        return await self._record("edit_message_caption", *args, **kwargs)

    async def copy_message(self, *args, **kwargs):
        return await self._record("copy_message", *args, **kwargs)

    async def edit_message_text(self, *args, **kwargs):
        return await self._record("edit_message_text", *args, **kwargs)

    async def edit_message_caption(self, *args, **kwargs):
        return await self._record("edit_message_caption", *args, **kwargs)

    async def edit_message_media(self, *args, **kwargs):
        return await self._record("edit_message_media", *args, **kwargs)

    username = "destroy_test_bot"

    async def send_dice(self, *args, **kwargs):
        self.calls.append(("send_dice", args, kwargs))
        return types.SimpleNamespace(message_id=321, dice=types.SimpleNamespace(value=6))

    async def upload_sticker_file(self, *args, **kwargs):
        self.calls.append(("upload_sticker_file", args, kwargs))
        return types.SimpleNamespace(file_id=f"file_{len(self.calls)}")

    async def create_new_sticker_set(self, *args, **kwargs):
        self.calls.append(("create_new_sticker_set", args, kwargs))
        return True

    async def get_sticker_set(self, *args, **kwargs):
        self.calls.append(("get_sticker_set", args, kwargs))
        return types.SimpleNamespace(stickers=[
            types.SimpleNamespace(emoji="💜", custom_emoji_id="111111111111"),
            types.SimpleNamespace(emoji="💚", custom_emoji_id="333333333333"),
            types.SimpleNamespace(emoji="⬜", custom_emoji_id="222222222222"),
        ])

    async def delete_message(self, *args, **kwargs):
        return await self._record("delete_message", *args, **kwargs)

    async def edit_message_reply_markup(self, *args, **kwargs):
        return await self._record("edit_message_reply_markup", *args, **kwargs)

    async def ban_chat_member(self, *args, **kwargs):
        return await self._record("ban_chat_member", *args, **kwargs)

    async def unban_chat_member(self, *args, **kwargs):
        return await self._record("unban_chat_member", *args, **kwargs)

    async def get_chat_member(self, *args, **kwargs):
        return types.SimpleNamespace(status="left")

    async def edit_message_reply_markup(self, *args, **kwargs):
        if self.fail_markup is not None:
            raise self.fail_markup
        return await self._record("edit_message_reply_markup", *args, **kwargs)


_module("telegram", InputMediaPhoto=_Dummy, InputSticker=_Dummy, InputFile=_Dummy, ChatPermissions=_Dummy, InlineKeyboardButton=_Dummy, InlineKeyboardMarkup=_Dummy,
        MessageEntity=MessageEntity, Update=_Dummy, User=User)
class ChatType:
    PRIVATE, GROUP, SUPERGROUP, CHANNEL = "private", "group", "supergroup", "channel"


_module("telegram.constants", ChatMemberStatus=ChatMemberStatus, ChatType=ChatType, ParseMode=ParseMode)
_module("telegram.error", BadRequest=BadRequest, NetworkError=NetworkError, TelegramError=TelegramError,
        TimedOut=TimedOut)
class ContextTypes:
    DEFAULT_TYPE = None


class ChatMemberHandler:
    CHAT_MEMBER = "chat_member"

    def __init__(self, *args, **kwargs):
        pass


class _FilterAny:
    """Заглушка фильтров: поддерживает &, |, ~, вызов и любые атрибуты."""
    def __call__(self, *args, **kwargs):
        return _FilterAny()
    def __getattr__(self, name):
        return _FilterAny()
    def __and__(self, other):
        return _FilterAny()
    __or__ = __rand__ = __ror__ = __and__
    def __invert__(self):
        return _FilterAny()


_module("telegram.ext", ExtBot=ExtBot, Application=_Dummy, CallbackQueryHandler=_Dummy,
        ChatJoinRequestHandler=_Dummy, ChatMemberHandler=ChatMemberHandler, CommandHandler=_Dummy, ContextTypes=ContextTypes, MessageHandler=_Dummy,
        PersistenceInput=_Dummy, PicklePersistence=_Dummy, filters=_FilterAny())

# ---------- загрузка бота ----------
_tmp = tempfile.mkdtemp()
os.environ.update({
    "DATA_FILE": os.path.join(_tmp, "data.json"), "OWNER_ID": "1", "ADMIN_CHAT_ID": "-100200",
    "MAIN_CHAT_ID": "-100300", "BOT_TOKEN": "123:test",
})
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("bot", os.path.join(HERE, "bot.py"))
bot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bot)

# ---------- тесты ----------
passed = 0


def check(name, condition):
    global passed
    assert condition, name
    passed += 1
    print("ok —", name)


def chat_of(call):
    return call[1][0] if call[1] else call[2].get("chat_id")


def text_of(call):
    return call[1][1] if len(call[1]) > 1 else call[2].get("text")


class FakeContext:
    def __init__(self):
        self.bot = ExtBot()


def test_converter():
    plain, ents = bot.html_to_entities('🦊 Нарушитель: <a href="tg://user?id=5399052664">;g</a>')
    check("ссылка tg://user становится text_mention", ents[0].type == "text_mention"
          and ents[0].user.id == 5399052664 and plain.endswith(";g"))
    plain, ents = bot.html_to_entities('😀😀 <a href="tg://user?id=7">Ли</a>')
    check("смещения UTF-16 учитывают эмодзи", ents[0].offset == 5 and ents[0].length == 2)
    plain, ents = bot.html_to_entities("<b>Вася &amp; Co</b>")
    check("HTML-сущности экранирования раскрываются", plain == "Вася & Co" and ents[0].type == "bold")
    plain, ents = bot.html_to_entities('<a href="https://t.me/durov">Павел</a>')
    check("ссылка с username остаётся text_link", ents[0].type == "text_link" and ents[0].url.startswith("https"))


async def test_htmlbot_sends_entities():
    bot_obj = bot.HtmlBot(token="x")
    await bot_obj.send_message(-100, 'Ник: <code>Steve</code>', parse_mode="HTML")
    name, args, kwargs = bot_obj.calls[-1]
    check("send_message переводит HTML в текст", args[1] == "Ник: Steve" if len(args) > 1 else kwargs["text"] == "Ник: Steve")
    check("parse_mode убирается, появляются entities", "parse_mode" not in kwargs and kwargs.get("entities"))


async def test_application_card_gone():
    ctx = FakeContext()
    app = {"id": 5, "user_id": 42, "admin_message_id": 99, "status": "pending", "nickname": "a"}
    data = bot.data
    data["applications"]["5"] = app
    ctx.bot.fail_markup = BadRequest("Message to edit not found")
    refusal = await bot.application_refusal(ctx, 42)
    check("удалённая карточка: заявка отменяется, подача разрешена", refusal is None and app["status"] == "cancelled")

    app2 = {"id": 6, "user_id": 43, "admin_message_id": 100, "status": "pending", "nickname": "b"}
    data["applications"]["6"] = app2
    ctx.bot.fail_markup = BadRequest("Message is not modified")
    refusal = await bot.application_refusal(ctx, 43)
    check("живая карточка: пользователь получает сообщение без номера заявки",
          refusal and "№" not in refusal and app2["status"] == "pending")


async def test_stale_applications_job():
    ctx = FakeContext()
    old = bot.now_utc() - timedelta(days=8)
    app = {"id": 7, "user_id": 44, "admin_message_id": 101, "status": "pending", "nickname": "c",
           "created_at": old.isoformat(), "user_name": "X", "username": None, "photo_id": "p"}
    bot.data["applications"]["7"] = app
    await bot.stale_applications_job(ctx)
    check("заявка старше 7 дней закрывается", app["status"] == "cancelled")
    sent = [c for c in ctx.bot.calls if c[0] == "send_message" and c[1][0] == 44]
    check("пользователь получает уведомление о закрытии", len(sent) == 1)


async def test_expiry_notices():
    ctx = FakeContext()
    past = (bot.now_utc() - timedelta(minutes=5)).isoformat()
    bot.data["punishments"]["77"] = {"type": "mute", "duration": "7 дней", "until": past}
    bot.data["warnings"]["78"] = 2
    bot.data["warning_expires"]["78"] = past
    bot.cleanup_expired()
    check("истёкший мут и предупреждения попадают в очередь", len(bot.data["expiry_queue"]) == 2)
    await bot.send_expiry_notices(ctx)
    admin_msgs = [c for c in ctx.bot.calls if c[1][0] == -100200]
    check("админам уходят два уведомления", len(admin_msgs) == 2)
    check("очередь очищается после отправки", bot.data["expiry_queue"] == [])


async def test_background_loop():
    ctx = FakeContext()
    past = (bot.now_utc() - timedelta(minutes=5)).isoformat()
    bot.data["punishments"]["88"] = {"type": "mute", "duration": "1 день", "until": past}
    task = asyncio.create_task(bot.background_loop(ctx.bot))
    await asyncio.sleep(0.05)  # первая итерация выполняется сразу
    task.cancel()
    try:
        await task
    except asyncio.CancelledError:
        pass
    check("фоновый цикл чистит истёкший мут и уведомляет админов",
          any(c[1][0] == -100200 for c in ctx.bot.calls) and task.cancelled())


def test_template_helpers():
    check("слишком длинная подпись к фото отклоняется", bot.template_error("а" * 1100, with_photo=True) is not None)
    check("текст до 4096 символов без фото допустим", bot.template_error("а" * 2000, with_photo=False) is None)


async def test_template_flow():
    """Владелец: меню → текст → предпросмотр → сохранение."""
    ctx = FakeContext()
    ctx.user_data = {}
    bot.data["template_text"] = "Старый текст"
    bot.data["template_photo"] = None

    class Msg:
        def __init__(self, text_html=None, chat_id=1):
            self.text_html, self.chat = text_html, types.SimpleNamespace(id=chat_id)
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)
        async def edit_text(self, text, **kwargs):
            self.replies.append(text)

    class Query:
        def __init__(self, action, user_id=1):
            self.data, self.from_user = f"tpl:{action}", types.SimpleNamespace(id=user_id)
            self.message = Msg(chat_id=1)
        async def answer(self, *args, **kwargs):
            pass

    owner_update = lambda q: types.SimpleNamespace(callback_query=q)
    await bot.template_callback(owner_update(Query("text")), ctx)
    check("кнопка «Изменить текст» переводит в режим ввода", ctx.user_data.get("tpl_step") == "text")

    msg = Msg(text_html="<b>Новый</b> текст")
    await bot.owner_private_text(types.SimpleNamespace(effective_message=msg), ctx)
    check("текст попадает в черновик, а не в сохранённый шаблон",
          ctx.user_data["tpl_draft"]["text"] == "<b>Новый</b> текст" and bot.data["template_text"] == "Старый текст")

    await bot.template_callback(owner_update(Query("save")), ctx)
    check("после «Сохранить» шаблон обновлён и черновик очищен",
          bot.data["template_text"] == "<b>Новый</b> текст" and "tpl_draft" not in ctx.user_data)

    stranger = Query("save", user_id=999)
    await bot.template_callback(owner_update(stranger), ctx)
    check("чужой пользователь не может менять шаблон", bot.data["template_text"] == "<b>Новый</b> текст")


async def test_transfer_link():
    """Чужой человек вошёл по ссылке: ссылка отзывается, заявка отклоняется, подача закрыта на 7 дней."""
    ctx = FakeContext()
    revoked = []

    async def revoke(chat_id, invite_link):
        revoked.append(invite_link)

    async def decline():
        pass

    ctx.bot.revoke_chat_invite_link = revoke
    link = "https://t.me/+transfer_test"
    bot.data["applications"]["50"] = {
        "id": 50, "user_id": 4242, "status": "accepted", "invite_link": link,
        "admin_message_id": 500, "nickname": "owner",
    }
    request = types.SimpleNamespace(
        chat=types.SimpleNamespace(id=-100300),
        invite_link=types.SimpleNamespace(invite_link=link, name="application-50"),
        from_user=types.SimpleNamespace(id=9999, first_name="Чужой", full_name="Чужой", username=None),
        decline=decline,
    )
    update = types.SimpleNamespace(chat_join_request=request)
    await bot.join_request_handler(update, ctx)

    app = bot.data["applications"]["50"]
    check("ссылка отозвана", revoked == [link] and app["invite_revoked"] is True)
    check("заявка отклонена", app["status"] == "rejected")
    check("подача закрыта на 7 дней", bot.get_user_block(4242) is not None)


async def test_admin_log():
    ctx = FakeContext()
    bot.data["admins"] = [2]
    bot.data["admin_log"] = [
        {"at": bot.now_utc().isoformat(), "action": "reports_blocked", "actor_id": 2, "target_id": 3,
         "app_id": None, "details": None}
        for _ in range(25)
    ]
    text, page, total = bot.log_page(0)
    check("журнал делится на страницы по 10 записей", total == 3 and "Страница 1 из 3" in text)

    class Msg:
        chat = types.SimpleNamespace(id=-100200, type="supergroup")
        async def edit_text(self, text, **kwargs):
            self.text = text

    class Query:
        def __init__(self, action, user_id):
            self.data, self.from_user, self.message = f"log:{action}", types.SimpleNamespace(id=user_id), Msg()
        async def answer(self, *args, **kwargs):
            self.alert = kwargs.get("show_alert", False)

    upd = lambda q: types.SimpleNamespace(callback_query=q)

    q = Query("clear", 2)
    await bot.log_callback(upd(q), ctx)
    check("админ не может очистить журнал", len(bot.data["admin_log"]) == 25)

    q = Query("clearyes", 2)
    await bot.log_callback(upd(q), ctx)
    check("очистка админом не выполняется", len(bot.data["admin_log"]) == 25)

    q = Query("clearyes", 1)
    await bot.log_callback(upd(q), ctx)
    check("владелец очищает журнал, остаётся запись об очистке",
          len(bot.data["admin_log"]) == 1 and bot.data["admin_log"][0]["action"] == "log_cleared")

    class DmMsg:
        chat = types.SimpleNamespace(id=1, type="private")
        async def edit_text(self, text, **kwargs):
            self.text = text

    class DmQuery(Query):
        def __init__(self, action, user_id):
            super().__init__(action, user_id)
            self.message = DmMsg()

    bot.data["admin_log"] = [{"at": bot.now_utc().isoformat(), "action": "reports_blocked", "actor_id": 2,
                              "target_id": 3, "app_id": None, "details": None} for _ in range(25)]
    q = DmQuery("1", 1)
    await bot.log_callback(upd(q), ctx)
    check("владелец листает журнал в личке", hasattr(q.message, "text") and "Страница 2 из 3" in q.message.text)

    class AdminDmQuery(DmQuery):
        pass

    q = AdminDmQuery("1", 2)  # админ (не владелец) в личке с ботом
    await bot.log_callback(upd(q), ctx)
    check("админ не может открыть журнал в личке", not hasattr(q.message, "text"))

    q = Query("1", 2)  # админ в админ-чате
    await bot.log_callback(upd(q), ctx)
    check("админ листает журнал в админ-чате", hasattr(q.message, "text"))


async def test_start_notifies_owner():
    ctx = FakeContext()
    ctx.user_data = {}

    class Msg:
        async def reply_text(self, text, **kwargs):
            pass

    user = types.SimpleNamespace(id=555, first_name="Вася", full_name="Вася", username="vasya")
    upd = types.SimpleNamespace(
        effective_message=Msg(), effective_user=user,
        effective_chat=types.SimpleNamespace(id=555, type="private"),
    )
    await bot.start(upd, ctx)
    to_owner = [c for c in ctx.bot.calls if c[0] == "send_message" and chat_of(c) == 1]
    check("владелец получает сообщение о нажатии /start", len(to_owner) == 1 and "555" in text_of(to_owner[0]))

    ctx2 = FakeContext()
    ctx2.user_data = {}
    owner_user = types.SimpleNamespace(id=1, first_name="Владелец", full_name="Владелец", username=None)
    upd2 = types.SimpleNamespace(
        effective_message=Msg(), effective_user=owner_user,
        effective_chat=types.SimpleNamespace(id=1, type="private"),
    )
    await bot.start(upd2, ctx2)
    check("владельцу самому уведомление не отправляется",
          not [c for c in ctx2.bot.calls if c[0] == "send_message" and chat_of(c) == 1
               and "Нажали /start" in (text_of(c) or "")])


async def test_start_log():
    ctx = FakeContext()
    ctx.user_data = {}

    class Msg:
        async def reply_text(self, text, **kwargs):
            pass

    user = types.SimpleNamespace(id=777, first_name="Лена", full_name="Лена", username="lena")
    upd = types.SimpleNamespace(effective_message=Msg(), effective_user=user,
                                effective_chat=types.SimpleNamespace(id=777, type="private"))
    bot.data["start_log"] = []
    await bot.start(upd, ctx)
    check("нажатие /start попадает в журнал", len(bot.data["start_log"]) == 1
          and bot.data["start_log"][0]["user_id"] == 777)
    text, page, total = bot.start_log_page(0)
    check("журнал нажатий выводит ID и username", "777" in text and "@lena" in text and total == 1)


async def test_unverified_flow():
    """Вход без заявки: предупреждение, напоминание, исключение через 24 часа."""
    ctx = FakeContext()
    bot.data["applications"] = {}
    bot.data["unverified"] = {}
    old = types.SimpleNamespace(status="left")
    new = types.SimpleNamespace(status="member", tag=None)
    user = types.SimpleNamespace(id=8888, first_name="Гость", full_name="Гость", username="guest", is_bot=False)
    change = types.SimpleNamespace(
        chat=types.SimpleNamespace(id=-100300),
        old_chat_member=old,
        new_chat_member=types.SimpleNamespace(status="member", tag=None, user=user),
    )
    bot.JOIN_BATCH_DELAY = 0
    await bot.on_member_change(types.SimpleNamespace(chat_member=change), ctx)
    await asyncio.sleep(0.05)
    check("вход без заявки ставит срок", "8888" in bot.data["unverified"])
    check("в основной чат уходит предупреждение",
          any(c[0] == "send_message" and chat_of(c) == -100300 and "без заявки" in text_of(c)
              for c in ctx.bot.calls))

    # Заявка подана — срок не нужен, и человек не попадает под исключение
    bot.data["applications"]["60"] = {"id": 60, "user_id": 8888, "status": "pending"}
    bot.data["unverified"]["8888"]["deadline"] = (bot.now_utc() - timedelta(minutes=1)).isoformat()
    await bot.unverified_tick(ctx)
    check("пока заявка на рассмотрении, участника не исключают",
          not [c for c in ctx.bot.calls if c[0] == "ban_chat_member"])

    bot.data["applications"]["60"]["status"] = "rejected"
    await bot.unverified_tick(ctx)
    check("срок прошёл, заявки нет — участника исключают",
          [c for c in ctx.bot.calls if c[0] == "ban_chat_member"] and "8888" not in bot.data["unverified"])


async def test_foreign_join_request_approved():
    """Запрос по чужой ссылке: без заявки ждет админа, с одобренной заявкой проходит."""
    ctx = FakeContext()
    approved = []

    async def approve():
        approved.append(True)

    async def decline():
        pass

    request = types.SimpleNamespace(
        chat=types.SimpleNamespace(id=-100300),
        invite_link=types.SimpleNamespace(invite_link="https://t.me/+other", name="comments"),
        from_user=types.SimpleNamespace(id=7777, first_name="Коммент", full_name="Коммент", username=None),
        approve=approve, decline=decline,
    )
    bot.data["applications"] = {}
    await bot.join_request_handler(types.SimpleNamespace(chat_join_request=request), ctx)
    check("запрос без заявки не одобряется, ждет ручного решения", approved == [])

    bot.data["applications"]["70"] = {"id": 70, "user_id": 7777, "status": "accepted"}
    await bot.join_request_handler(types.SimpleNamespace(chat_join_request=request), ctx)
    check("вернувшийся с одобренной заявкой проходит тихо", approved == [True])


async def test_muted_user_join_detected():
    """Участник с мутом возвращается в чат: статус restricted, но вход должен распознаться."""
    ctx = FakeContext()
    bot.data["applications"] = {}
    bot.data["unverified"] = {}
    user = types.SimpleNamespace(id=5555, first_name="Мут", full_name="Мут", username=None, is_bot=False)
    change = types.SimpleNamespace(
        chat=types.SimpleNamespace(id=-100300),
        old_chat_member=types.SimpleNamespace(status="restricted", is_member=False),
        new_chat_member=types.SimpleNamespace(status="restricted", is_member=True, tag=None, user=user),
    )
    await bot.on_member_change(types.SimpleNamespace(chat_member=change), ctx)
    check("вход участника с мутом распознается", "5555" in bot.data["unverified"])


async def test_tag_exempts_player():
    """Игрок с тегом не получает срок, без тега — получает."""
    ctx = FakeContext()
    bot.data["applications"] = {}
    bot.data["unverified"] = {}

    def change_for(uid, tag, has_tag=True):
        user = types.SimpleNamespace(id=uid, first_name="Игрок", full_name="Игрок", username=None, is_bot=False)
        member = types.SimpleNamespace(status="member", user=user)
        if has_tag:
            member.tag = tag
        return types.SimpleNamespace(
            chat=types.SimpleNamespace(id=-100300),
            old_chat_member=types.SimpleNamespace(status="left"),
            new_chat_member=member,
        )

    await bot.on_member_change(types.SimpleNamespace(chat_member=change_for(9001, "Steve")), ctx)
    check("игрок с тегом не получает срок", "9001" not in bot.data["unverified"])
    await bot.on_member_change(types.SimpleNamespace(chat_member=change_for(9002, None)), ctx)
    check("человек без тега получает срок", "9002" in bot.data["unverified"])
    await bot.on_member_change(types.SimpleNamespace(chat_member=change_for(9003, None, has_tag=False)), ctx)
    check("без поддержки тегов никого не наказываем", "9003" not in bot.data["unverified"])


async def test_reset_application():
    ctx = FakeContext()
    bot.data["applications"] = {"80": {"id": 80, "user_id": 444444, "status": "accepted", "admin_message_id": None}}

    class Msg:
        def __init__(self, text):
            self.text, self.reply_to_message, self.sender_chat = text, None, None
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    owner = types.SimpleNamespace(id=1, full_name="Владелец", username=None)
    upd = types.SimpleNamespace(effective_message=Msg("/сбросзаявку 444444"), effective_user=owner,
                                effective_chat=types.SimpleNamespace(id=1, type="private"))
    await bot.reset_application_command(upd, ctx)
    check("владелец сбрасывает одобренную заявку", bot.data["applications"]["80"]["status"] == "reset")
    check("сброс записывается в журнал", any(e["action"] == "application_reset" for e in bot.data["admin_log"]))

    admin = types.SimpleNamespace(id=2, full_name="Админ", username=None)
    bot.data["admins"] = [2]
    bot.data["applications"]["81"] = {"id": 81, "user_id": 5555, "status": "accepted", "admin_message_id": None}
    upd2 = types.SimpleNamespace(effective_message=Msg("/сбросзаявку 5555"), effective_user=admin,
                                 effective_chat=types.SimpleNamespace(id=-100200, type="supergroup"))
    await bot.reset_application_command(upd2, ctx)
    check("админ не может сбросить заявку", bot.data["applications"]["81"]["status"] == "accepted")


async def test_member_without_app_can_apply():
    ctx = FakeContext()
    bot.data["applications"] = {}
    bot.data["punishments"] = {}
    bot.data["unverified"] = {"31313": {"name": "Игрок", "username": None, "deadline": "2099-01-01T00:00:00+00:00"}}

    class MemberCtx(FakeContext):
        pass

    async def in_chat(chat_id, user_id):
        return types.SimpleNamespace(status="member")

    ctx.bot.get_chat_member = in_chat
    refusal = await bot.application_refusal(ctx, 31313)
    check("участник без заявки, который уже в чате, может подать заявку", refusal is None)


async def test_quiz_flow():
    """Викторина: включение, первый верный ответ получает коин, попытка одна, закрытие по времени."""
    ctx = FakeContext()
    bot.data["quiz"] = {"enabled": False, "next_at": None, "used": [], "current": None, "round": 0}
    bot.data["ds_coins"] = {}

    class Msg:
        chat = types.SimpleNamespace(id=1, type="private")
        def __init__(self):
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    owner = types.SimpleNamespace(id=1, full_name="Владелец", username=None)
    upd = types.SimpleNamespace(effective_message=Msg(), effective_user=owner,
                                effective_chat=types.SimpleNamespace(id=1, type="private"))
    await bot.quiz_command(upd, ctx)
    cur = bot.data["quiz"]["current"]
    check("владелец включает викторину, раунд стартует", bot.data["quiz"]["enabled"] and cur is not None)
    check("вопрос уходит в основной чат", any(c[0] == "send_message" and chat_of(c) == -100300 for c in ctx.bot.calls))

    class Query:
        def __init__(self, data_str, user_id, chat_id=-100300):
            self.data = data_str
            self.from_user = types.SimpleNamespace(id=user_id, full_name=f"Игрок{user_id}", username=None)
            self.message = types.SimpleNamespace(chat=types.SimpleNamespace(id=chat_id, type="supergroup"))
            self.popups = []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)

    rid, correct = cur["round"], cur["correct"]
    wrong = (correct + 1) % 4
    q_wrong = Query(f"qz:{rid}:{wrong}", 555)
    await bot.quiz_callback(types.SimpleNamespace(callback_query=q_wrong), ctx)
    check("неверный ответ показывает «Неверно», попытка использована",
          "Неверно" in (q_wrong.popups[-1] or "") and "555" in bot.data["quiz"]["current"]["attempted"])
    check("владелец получает сообщение о неверном нажатии",
          any(c[0] == "send_message" and chat_of(c) == 1 and "неверно" in text_of(c) for c in ctx.bot.calls))

    q_again = Query(f"qz:{rid}:{correct}", 555)
    await bot.quiz_callback(types.SimpleNamespace(callback_query=q_again), ctx)
    check("вторая попытка на тот же вопрос запрещена", "использован" in (q_again.popups[-1] or ""))
    check("после неверной попытки раунд ещё открыт", bot.data["quiz"]["current"] is not None)

    q_win = Query(f"qz:{rid}:{correct}", 666)
    await bot.quiz_callback(types.SimpleNamespace(callback_query=q_win), ctx)
    check("первый верный ответ дает 20 DS коинов", bot.ds_balance(666) == 20)
    check("после первого победителя раунд ещё открыт", bot.data["quiz"]["current"] is not None)

    q_second = Query(f"qz:{rid}:{correct}", 777)
    await bot.quiz_callback(types.SimpleNamespace(callback_query=q_second), ctx)
    q_third = Query(f"qz:{rid}:{correct}", 888)
    await bot.quiz_callback(types.SimpleNamespace(callback_query=q_third), ctx)
    check("три первых верных ответа получают по 1 DS коину",
          bot.ds_balance(666) == 20 and bot.ds_balance(777) == 20 and bot.ds_balance(888) == 20)
    check("после третьего места раунд закрывается", bot.data["quiz"]["current"] is None)

    q_late = Query(f"qz:{rid}:{correct}", 999)
    await bot.quiz_callback(types.SimpleNamespace(callback_query=q_late), ctx)
    check("после закрытия кнопки показывают «Вопрос уже закрыт»", "закрыт" in (q_late.popups[-1] or ""))
    check("четвёртый участник коин не получает", bot.ds_balance(999) == 0)

    await bot.quiz_start_round(ctx)
    bot.data["quiz"]["current"]["deadline"] = (bot.now_utc() - timedelta(minutes=1)).isoformat()
    await bot.quiz_tick(ctx)
    check("по истечении 5 минут раунд закрывается без ответа в чат", bot.data["quiz"]["current"] is None)

    await bot.balance_command(types.SimpleNamespace(effective_message=Msg(), effective_user=types.SimpleNamespace(id=666)), ctx)
    check("баланс показывает накопленные коины", bot.ds_balance(666) == 20)


async def test_coins_commands():
    ctx = FakeContext()
    bot.data["ds_coins"] = {"100001": 5, "200002": 9, "300003": 0}
    bot.data["users"] = {}

    class Msg:
        def __init__(self, text, reply_to=None):
            self.text, self.reply_to_message, self.sender_chat = text, reply_to, None
            self.chat = types.SimpleNamespace(id=1, type="private")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    owner = types.SimpleNamespace(id=1, full_name="Владелец", username=None)
    upd = lambda m, u: types.SimpleNamespace(effective_message=m, effective_user=u,
                                             effective_chat=types.SimpleNamespace(id=1, type="private"))
    await bot.grant_coins_command(upd(Msg("/выдатькоины 100001 10"), owner), ctx)
    check("владелец выдаёт коины по ID", bot.ds_balance(100001) == 15)

    await bot.grant_coins_command(upd(Msg("/выдатькоины 100001 -50"), owner), ctx)
    check("списание не уводит баланс в минус", bot.ds_balance(100001) == 0)

    stranger = types.SimpleNamespace(id=555, full_name="Игрок", username=None)
    await bot.grant_coins_command(upd(Msg("/выдатькоины 200002 100"), stranger), ctx)
    check("обычный участник выдать коины не может", bot.ds_balance(200002) == 9)

    top_msg = Msg("/топкоинов")
    await bot.coins_top_command(upd(top_msg, stranger), ctx)
    text = top_msg.replies[-1]
    check("в топе только ненулевые балансы", "id=200002" in text and "id=100001" not in text and "id=300003" not in text)


async def test_admin_coins_and_balance():
    ctx = FakeContext()
    bot.data["ds_coins"] = {"100001": 4}
    bot.data["admins"] = [2]

    class Msg:
        def __init__(self, text, chat_id, chat_type):
            self.text, self.reply_to_message, self.sender_chat = text, None, None
            self.chat = types.SimpleNamespace(id=chat_id, type=chat_type)
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    admin = types.SimpleNamespace(id=2, full_name="Админ", username=None)
    grant = Msg("/выдатькоины 100001 3", -100200, "supergroup")
    await bot.grant_coins_command(types.SimpleNamespace(effective_message=grant, effective_user=admin,
                                                        effective_chat=grant.chat), ctx)
    check("админ выдаёт коины в админ-чате", bot.ds_balance(100001) == 7)

    look = Msg("/баланс 100001", -100200, "supergroup")
    await bot.balance_command(types.SimpleNamespace(effective_message=look, effective_user=admin,
                                                    effective_chat=look.chat), ctx)
    check("админ смотрит баланс участника в админ-чате", "7" in look.replies[-1] and "100001" not in look.replies[-1] or "7" in look.replies[-1])

    player = types.SimpleNamespace(id=100001, full_name="Игрок", username=None)
    own = Msg("/баланс 200002", -100300, "supergroup")
    await bot.balance_command(types.SimpleNamespace(effective_message=own, effective_user=player,
                                                    effective_chat=own.chat), ctx)
    check("участник видит только свой баланс", "7" in own.replies[-1])


async def test_shop_flow():
    ctx = FakeContext()
    bot.data["shop"] = {"next_id": 1, "items": []}
    bot.data["ds_coins"] = {"123456": 10}
    bot.data["purchases"] = []

    class Msg:
        def __init__(self, text):
            self.text, self.caption, self.reply_to_message, self.sender_chat = text, None, None, None
            self.chat = types.SimpleNamespace(id=1, type="private")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    owner = types.SimpleNamespace(id=1, full_name="Владелец", username=None)
    add = Msg("/шопс добавить Скин | 7 | красивый")
    await bot.shop_admin_command(types.SimpleNamespace(effective_message=add, effective_user=owner,
                                                       effective_chat=add.chat), ctx)
    check("владелец добавляет товар с ценой", bot.shop_active_items()
          and bot.shop_active_items()[0]["price"] == 7)

    buyer = types.SimpleNamespace(id=123456, full_name="Покупатель", username=None)

    class Query:
        def __init__(self, data_str, user):
            self.data, self.from_user, self.popups = data_str, user, []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)

    q = Query("shop:buy:1", buyer)
    await bot.shop_buy_callback(types.SimpleNamespace(callback_query=q), ctx)
    check("покупка списывает коины", bot.ds_balance(123456) == 3)
    check("покупка попадает в историю", len(bot.data["purchases"]) == 1)

    poor = types.SimpleNamespace(id=999999, full_name="Бедный", username=None)
    q2 = Query("shop:buy:1", poor)
    await bot.shop_buy_callback(types.SimpleNamespace(callback_query=q2), ctx)
    check("без нужной суммы покупка не проходит", bot.ds_balance(999999) == 0
          and "Недостаточно" in (q2.popups[-1] or ""))


async def test_profile():
    ctx = FakeContext()
    ctx.user_data = {}
    bot.data["ds_coins"] = {"123456": 12}
    bot.data["purchases"] = [{"user_id": 123456, "item_name": "Скин", "price": 7, "at": bot.now_utc().isoformat()}]
    bot.data["admin_log"] = [{"at": bot.now_utc().isoformat(), "action": "quiz_win", "actor_id": 123456,
                              "target_id": 123456, "app_id": None, "details": None}]
    bot.data["applications"] = {"90": {"id": 90, "user_id": 123456, "status": "accepted",
                                       "created_at": bot.now_utc().isoformat()}}
    bot.data["warnings"] = {"123456": 1}
    bot.data["profiles"] = {}
    bot.data["profile_msgs"] = {}
    text = bot.build_profile(123456)
    check("профиль показывает баланс, покупки, листья и лайки",
          "12 DS коинов" in text and "Покупок: 1" in text and "Поймано листьев" in text and "лайков" in text)
    check("в профиле нет заявок и предупреждений", "заявк" not in text.lower() and "предупрежд" not in text.lower())

    async def delete_message(chat_id, message_id):
        ctx.bot.calls.append(("delete_message", (chat_id, message_id), {}))
    ctx.bot.delete_message = delete_message

    class Msg:
        def __init__(self, text=None, photo=None, chat_id=-100300):
            self.text, self.caption, self.photo = text, None, photo
            self.reply_to_message, self.sender_chat = None, None
            self.chat = types.SimpleNamespace(id=chat_id, type="supergroup")
            self.replies = []
            self.deleted = False
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)
        async def delete(self):
            self.deleted = True

    class Query:
        def __init__(self, data_str, user_id):
            self.data = data_str
            self.from_user = types.SimpleNamespace(id=user_id, full_name="Игрок", username=None)
            self.message = types.SimpleNamespace(chat=types.SimpleNamespace(id=-100300, type="supergroup"))
            self.popups = []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)

    player = types.SimpleNamespace(id=123456, full_name="Игрок", username=None)
    m = Msg("/мустат")
    await bot.my_profile_command(types.SimpleNamespace(effective_message=m, effective_user=player,
                                                       effective_chat=m.chat), ctx)
    check("/мустат показывает профиль с кнопками",
          any(c[0] == "send_message" and "Баланс" in text_of(c) for c in ctx.bot.calls))

    q = Query("pf:status:123456", 123456)
    await bot.profile_callback(types.SimpleNamespace(callback_query=q), ctx)
    check("кнопка «Статус» ждёт текст", ctx.user_data.get("pf_step") == "status")

    stranger = Query("pf:status:123456", 999)
    await bot.profile_callback(types.SimpleNamespace(callback_query=stranger), ctx)
    check("чужой профиль через кнопки не меняется", "Это не твой профиль" in (stranger.popups[-1] or ""))

    status_msg = Msg("играю в скай")
    await bot.profile_input(types.SimpleNamespace(effective_message=status_msg, effective_user=player,
                                                  effective_chat=status_msg.chat), ctx)
    check("статус сохраняется в профиле", bot.get_profile(123456)["status"] == "играю в скай")
    check("сообщение с текстом удаляется", status_msg.deleted)
    check("сообщение «Добавлено» не пишется в чат", not any(c[0] == "send_message" and text_of(c) == "✅ Добавлено" for c in ctx.bot.calls))
    check("шаг ввода закрыт", "pf_step" not in ctx.user_data)

    q2 = Query("pf:photo:123456", 123456)
    await bot.profile_callback(types.SimpleNamespace(callback_query=q2), ctx)
    photo_msg = Msg(photo=[types.SimpleNamespace(file_id="small"), types.SimpleNamespace(file_id="big")])
    await bot.profile_input(types.SimpleNamespace(effective_message=photo_msg, effective_user=player,
                                                  effective_chat=photo_msg.chat), ctx)
    check("картинка сохраняется в профиле", bot.get_profile(123456)["photo"] == "big")
    check("сообщение с фото удаляется", photo_msg.deleted)

    stranger_msg = Msg("чужой текст")
    await bot.profile_input(types.SimpleNamespace(effective_message=stranger_msg, effective_user=types.SimpleNamespace(id=999, full_name="X", username=None),
                                                  effective_chat=stranger_msg.chat), ctx)
    check("без нажатия кнопки сообщения не трогаются", not stranger_msg.deleted)

    stat_msg = Msg("/стат 123456")
    await bot.profile_command(types.SimpleNamespace(effective_message=stat_msg, effective_user=types.SimpleNamespace(id=999, full_name="X", username=None),
                                                    effective_chat=stat_msg.chat), ctx)
    check("/стат доступен обычному участнику", any(c[0] == "send_message" and "Баланс" in text_of(c) for c in ctx.bot.calls))


async def test_likes():
    ctx = FakeContext()
    bot.data["likes"] = {}
    bot.data["profiles"] = {}

    class Q:
        def __init__(self, data_str, user_id):
            self.data = data_str
            self.from_user = types.SimpleNamespace(id=user_id, full_name="Х", username=None)
            self.message = types.SimpleNamespace(photo=None, edit_text=self._edit, edit_caption=self._edit)
            self.popups, self.edited = [], []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)
        async def _edit(self, *args, **kwargs):
            self.edited.append(kwargs)

    q = Q("lk:123456", 999)
    await bot.like_callback(types.SimpleNamespace(callback_query=q), ctx)
    check("лайк ставится", bot.like_count(123456) == 1 and "поставлен" in (q.popups[-1] or ""))

    q_again = Q("lk:123456", 999)
    await bot.like_callback(types.SimpleNamespace(callback_query=q_again), ctx)
    check("повторное нажатие снимает лайк", bot.like_count(123456) == 0)

    q_self = Q("lk:123456", 123456)
    await bot.like_callback(types.SimpleNamespace(callback_query=q_self), ctx)
    check("свой профиль лайкнуть нельзя", bot.like_count(123456) == 0 and "нельзя" in (q_self.popups[-1] or ""))

    await bot.like_callback(types.SimpleNamespace(callback_query=Q("lk:123456", 999)), ctx)
    await bot.like_callback(types.SimpleNamespace(callback_query=Q("lk:123456", 888)), ctx)
    check("лайки считаются по разным людям", bot.like_count(123456) == 2)
    check("в профиле виден счётчик лайков", "2 лайков" in bot.build_profile(123456))


async def test_purchases_and_shop_menu():
    ctx = FakeContext()
    ctx.user_data = {}
    bot.data["purchases"] = [
        {"user_id": 777001, "item_name": "Скин", "price": 5, "at": bot.now_utc().isoformat()},
        {"user_id": 777001, "item_name": "Плащ", "price": 9, "at": bot.now_utc().isoformat()},
    ]
    bot.data["purchase_seq"] = 0
    bot.ensure_purchase_pids()
    pid = bot.data["purchases"][0]["pid"]

    class Q:
        def __init__(self, data_str, user_id, chat_type="private"):
            self.data = data_str
            self.from_user = types.SimpleNamespace(id=user_id, full_name="Х", username=None)
            self.message = types.SimpleNamespace(chat=types.SimpleNamespace(id=user_id, type=chat_type),
                                                 edit_text=self._edit, delete=self._noop)
            self.popups = []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)
        async def _edit(self, *a, **k):
            pass
        async def _noop(self, *a, **k):
            pass

    hide = Q(f"pu:hide:777001:{pid}:0", 777001)
    await bot.purchases_callback(types.SimpleNamespace(callback_query=hide), ctx)
    check("покупку можно скрыть", bot.data["purchases"][0].get("hidden") is True)
    visible = sum(1 for p in bot.data["purchases"] if int(p.get("user_id", 0)) == 777001 and not p.get("hidden"))
    check("скрытая покупка не считается в профиле", f"Покупок: {visible}" in bot.build_profile(777001))
    check("склонение: 1 коин, 2 коина, 5 коинов", bot.coins_word(1) == "DS коин" and bot.coins_word(2) == "DS коина" and bot.coins_word(5) == "DS коинов")

    stranger = Q(f"pu:hide:777001:{pid}:0", 999)
    await bot.purchases_callback(types.SimpleNamespace(callback_query=stranger), ctx)
    check("чужие покупки не меняются", bot.data["purchases"][0].get("hidden") is True)

    delete = Q(f"pu:del:777001:{pid}:0", 777001)
    await bot.purchases_callback(types.SimpleNamespace(callback_query=delete), ctx)
    check("покупку можно удалить", len(bot.data["purchases"]) == 1)

    owner = Q("sh:add", 1)
    await bot.shop_admin_callback(types.SimpleNamespace(callback_query=owner), ctx)
    check("кнопка «Добавить товар» ждёт ввод", ctx.user_data.get("shop_step") == {"action": "add"})

    class Msg:
        def __init__(self, text):
            self.text, self.photo, self.caption = text, None, None
            self.chat = types.SimpleNamespace(id=1, type="private")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    m = Msg("Шлем | 12 | крутой")
    await bot.owner_private_text(types.SimpleNamespace(effective_message=m, effective_user=types.SimpleNamespace(id=1),
                                                       effective_chat=m.chat), ctx)
    check("товар добавляется через кнопки", any(i["name"] == "Шлем" and i["price"] == 12 for i in bot.shop_state()["items"]))
    check("шаг ввода закрывается после добавления", "shop_step" not in ctx.user_data)


async def test_message_reward():
    ctx = FakeContext()
    bot.data["msg_counts"] = {"424242": 99}
    bot.data["ds_coins"] = {"424242": 2}
    bot.data["admin_log"] = []

    class Msg:
        text, caption = "привет", None
    user = types.SimpleNamespace(id=424242, full_name="Счётчик", username=None, is_bot=False)
    await bot.count_message(types.SimpleNamespace(effective_user=user, effective_message=Msg()), ctx)
    check("на 100 сообщении начисляется +100 коинов", bot.ds_balance(424242) == 102)
    check("в чат уходит отметка о награде",
          any(c[0] == "send_message" and chat_of(c) == -100300 and "100" in text_of(c) and "+100" in text_of(c)
              for c in ctx.bot.calls))
    cmd = types.SimpleNamespace(text="/мустат", caption=None)
    await bot.count_message(types.SimpleNamespace(effective_user=user, effective_message=cmd), ctx)
    check("команды не считаются", bot.message_count(424242) == 100)


async def test_chests():
    ctx = FakeContext()
    bot.data["chests"] = {"current": None, "round": 0}
    bot.data["ds_coins"] = {}
    bot.data["admin_log"] = []
    bot.data["hidden_users"] = []

    class Msg:
        def __init__(self, text):
            self.text, self.reply_to_message, self.sender_chat = text, None, None
            self.chat = types.SimpleNamespace(id=1, type="private")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    owner = types.SimpleNamespace(id=1, full_name="Владелец", username=None)
    start = Msg("/сундучки")
    await bot.chest_command(types.SimpleNamespace(effective_message=start, effective_user=owner,
                                                  effective_chat=start.chat), ctx)
    cur = bot.data["chests"]["current"]
    check("владелец запускает игру командой, без объявления в чат", cur is not None and len(cur["prizes"]) == 2)

    class Q:
        def __init__(self, data_str, user_id):
            self.data = data_str
            self.from_user = types.SimpleNamespace(id=user_id, full_name="Х", username=None)
            self.message = types.SimpleNamespace(chat=types.SimpleNamespace(id=-100300, type="supergroup"),
                                                 edit_text=None)
            self.popups = []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)

    rid, prize = cur["round"], cur["prizes"][0]
    miss = [i for i in range(3) if i not in cur["prizes"]][0]
    q1 = Q(f"ch:{rid}:{miss}", 501)
    await bot.chest_callback(types.SimpleNamespace(callback_query=q1), ctx)
    check("промах пишет «Мимо»", "Мимо" in (q1.popups[-1] or ""))
    q1b = Q(f"ch:{rid}:{prize}", 501)
    await bot.chest_callback(types.SimpleNamespace(callback_query=q1b), ctx)
    check("вторая попытка того же игрока запрещена", "использована" in (q1b.popups[-1] or ""))

    old_prize = set(bot.data["chests"]["current"]["prizes"])
    q2 = Q(f"ch:{rid}:{min(old_prize)}", 502)
    await bot.chest_callback(types.SimpleNamespace(callback_query=q2), ctx)
    check("попадание пишет окно с +5 DS коинов", "+5 DS" in (q2.popups[-1] or ""))
    check("попадание начисляет 5 коинов", bot.ds_balance(502) == 5)
    check("после попадания выигрышный сундучок меняется",
          set(bot.data["chests"]["current"]["prizes"]) != old_prize)

    for uid in (503, 504, 505, 506):
        cur2 = bot.data["chests"]["current"]
        if cur2 is None:
            break
        await bot.chest_callback(types.SimpleNamespace(callback_query=Q(f"ch:{rid}:{cur2['prizes'][0]}", uid)), ctx)
    check("после 5 мест игра закрывается", bot.data["chests"]["current"] is None)
    check("всего 5 мест", sum(bot.ds_balance(u) for u in (502, 503, 504, 505, 506)) == 25)


async def test_emoji_set():
    ctx = FakeContext()
    bot.data["emoji"] = {}

    class Msg:
        def __init__(self):
            self.text, self.reply_to_message, self.sender_chat = "/эмодзинабор", None, None
            self.chat = types.SimpleNamespace(id=1, type="private")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)

    owner = types.SimpleNamespace(id=1, full_name="Владелец", username=None)
    real_get = ctx.bot.get_sticker_set

    calls = {"n": 0}

    async def no_set_once(*a, **k):
        calls["n"] += 1
        if calls["n"] == 1:
            raise bot.TelegramError("Stickerset not found")
        return await real_get(*a, **k)
    ctx.bot.get_sticker_set = no_set_once
    m = Msg()
    await bot.emoji_set_command(types.SimpleNamespace(effective_message=m, effective_user=owner,
                                                      effective_chat=m.chat), ctx)
    check("набор эмодзи создается с двумя эмодзи", any(c[0] == "create_new_sticker_set" for c in ctx.bot.calls))
    check("ID эмодзи сохраняются в базу", bot.data["emoji"]["ids"] == {"purple": "111111111111", "lime": "333333333333", "empty": "222222222222"})
    bot.data["emoji"] = {}
    ctx.bot.get_sticker_set = real_get
    m2 = Msg()
    await bot.emoji_set_command(types.SimpleNamespace(effective_message=m2, effective_user=owner,
                                                      effective_chat=m2.chat), ctx)
    check("если набор с таким именем уже есть, берутся его ID", bot.data["emoji"]["ids"]["purple"] == "111111111111"
          and "уже был" in m2.replies[-1])
    check("ответ владельцу содержит ID", "111111111111" in m.replies[-1])
    check("файлы эмодзи вшиты в код", len(bot.EMOJI_PURPLE_TGS) > 100 and len(bot.EMOJI_LIME_TGS) > 100 and len(bot.EMOJI_EMPTY_TGS) > 100)


async def test_dice():
    ctx = FakeContext()
    bot.data["ds_coins"] = {"808080": 3}
    bot.data["dice_last"] = {}
    bot.data["hidden_users"] = []

    class Msg:
        def __init__(self, value):
            self.dice = types.SimpleNamespace(value=value, emoji="🎲")
            self.message_id = 77
            self.reply_to_message, self.sender_chat = None, None
            self.chat = types.SimpleNamespace(id=-100300, type="supergroup")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)
            return types.SimpleNamespace(message_id=5)

    player = types.SimpleNamespace(id=808080, full_name="Игрок", username=None, is_bot=False)
    m6 = Msg(6)
    await bot.dice_handler(types.SimpleNamespace(effective_message=m6, effective_user=player,
                                                 effective_chat=m6.chat), ctx)
    check("выпало 6: +4 коина, ставка списана", bot.ds_balance(808080) == 6)
    m2 = Msg(2)
    await bot.dice_handler(types.SimpleNamespace(effective_message=m2, effective_user=player,
                                                 effective_chat=m2.chat), ctx)
    check("повторный бросок сразу после первого ждет паузу", bot.ds_balance(808080) == 6 and "Подожди" in m2.replies[-1])


async def test_dice_panel():
    ctx = FakeContext()
    ctx.user_data = {}
    bot.data["ds_coins"] = {"909090": 10}
    bot.data["dice_last"] = {}
    bot.data["dice_bet"] = {}
    bot.data["hidden_users"] = []

    class Q:
        def __init__(self, data_str, user_id):
            self.data = data_str
            self.from_user = types.SimpleNamespace(id=user_id, full_name="Игрок", username=None)
            self.message = types.SimpleNamespace(chat=types.SimpleNamespace(id=-100300, type="supergroup"),
                                                 edit_text=self._noop, photo=None)
            self.popups = []
        async def answer(self, text=None, show_alert=False, **kwargs):
            self.popups.append(text)
        async def _noop(self, *a, **k):
            pass

    player = 909090
    await bot.dice_callback(types.SimpleNamespace(callback_query=Q(f"dc:{player}:bet:5", player)), ctx)
    check("ставка выбирается кнопкой и запоминается", bot.dice_bet(player) == 5)
    check("в панели виден баланс игрока", "🪙 Баланс:" in bot.dice_panel_text(player))
    await bot.dice_callback(types.SimpleNamespace(callback_query=Q(f"dc:{player}:roll", player)), ctx)
    check("«Бросить» бросает кубик через бота", any(c[0] == "send_dice" for c in ctx.bot.calls))
    check("выигрыш при ставке 5 и шестерке: чистый плюс 15 — баланс 25", bot.ds_balance(player) == 25)
    stranger = Q(f"dc:{player}:roll", 111)
    await bot.dice_callback(types.SimpleNamespace(callback_query=stranger), ctx)
    check("чужая панель не работает", "Это не твоя панель" in (stranger.popups[-1] or ""))


async def test_dice_command_cooldown():
    ctx = FakeContext()
    bot.data["dice_panel_last"] = {}
    bot.data["hidden_users"] = []

    class Msg:
        def __init__(self):
            self.text, self.reply_to_message, self.sender_chat, self.message_id = "/кубик", None, None, 55
            self.chat = types.SimpleNamespace(id=-100300, type="supergroup")
            self.replies = []
        async def reply_text(self, text, **kwargs):
            self.replies.append(text)
            return types.SimpleNamespace(message_id=56)

    player = types.SimpleNamespace(id=424242, full_name="Игрок", username=None, is_bot=False)
    m1 = Msg()
    await bot.dice_command(types.SimpleNamespace(effective_message=m1, effective_user=player, effective_chat=m1.chat), ctx)
    check("первый /кубик открывает панель", any(c[0] == "send_message" and "Кубик" in text_of(c) for c in ctx.bot.calls))
    m2 = Msg()
    await bot.dice_command(types.SimpleNamespace(effective_message=m2, effective_user=player, effective_chat=m2.chat), ctx)
    check("повторный /кубик сразу после первого ждет паузу", "Подожди" in m2.replies[-1])


async def test_dice_streak():
    bot.data["ds_coins"] = {"515151": 0}
    bot.data["dice_streak"] = {}
    bot.data["dice_stats"] = {}
    bot.data["dice_week"] = {"key": bot.dice_week_key(), "profit": {}}
    bot.data["dice_last"] = {}
    user = types.SimpleNamespace(id=515151, full_name="Серия", username=None)
    for _ in range(3):
        bot.dice_settle(user, 1, 6)
    check("три выигрыша подряд дают по +3 и серию 3", bot.ds_balance(515151) == 9 and bot.data["dice_streak"]["515151"] == 3)
    bot.dice_settle(user, 1, 6)
    check("четвертый выигрыш получает бонус серии +2", bot.ds_balance(515151) == 9 + 3 + 2)
    bot.dice_settle(user, 1, 2)
    check("проигрыш сбрасывает серию", bot.data["dice_streak"]["515151"] == 0)
    check("статистика ведется", bot.data["dice_stats"]["515151"]["rolls"] == 5 and bot.data["dice_stats"]["515151"]["best"] == 4)


def test_mafia_logic():
    g = bot.MafiaGame(-100300)
    names = {1: "a", 2: "b", 3: "c", 4: "d", 5: "e"}
    roles = ["mafia", "doctor", "commissar", "mirny", "mirny"]
    for (uid, name), role in zip(names.items(), roles):
        g.players[uid] = {"name": name, "role": role, "alive": True}
    check("мафия не побеждает, пока мирных больше", bot.mafia_check_win(g) is None)
    g.actions["kill"] = {1: 4}
    g.actions["heal"] = {2: 4}
    dead, _ = bot.mafia_resolve_night(g)
    check("доктор спасает от ночного убийства", dead == [] and g.players[4]["alive"])
    g.actions["kill"] = {1: 4}
    g.actions["heal"] = {}
    dead, _ = bot.mafia_resolve_night(g)
    check("без лечения жертва погибает", dead == [4] and not g.players[4]["alive"])
    g.players[3]["alive"] = False
    g.players[5]["alive"] = False
    check("мафия побеждает, когда мафии не меньше мирных", bot.mafia_check_win(g) == "mafia")
    g.players[1]["alive"] = False
    check("мирные побеждают, когда мафии нет", bot.mafia_check_win(g) == "town")


def test_register_handlers():
    """Регистрация всех обработчиков не должна падать (ловит ошибки порядка и имён)."""
    class FakeApp:
        def __init__(self):
            self.handlers = []
        def add_handler(self, handler, group=0):
            self.handlers.append(handler)
        def add_error_handler(self, handler):
            self.handlers.append(handler)
    fake = FakeApp()
    bot.register_all_handlers(fake)
    print("обработчиков:", len(fake.handlers)); check("все обработчики регистрируются без ошибок", len(fake.handlers) >= 15)


def main():
    test_converter()
    test_template_helpers()
    asyncio.run(test_htmlbot_sends_entities())
    asyncio.run(test_application_card_gone())
    asyncio.run(test_stale_applications_job())
    asyncio.run(test_expiry_notices())
    asyncio.run(test_background_loop())
    asyncio.run(test_template_flow())
    asyncio.run(test_transfer_link())
    asyncio.run(test_admin_log())
    asyncio.run(test_start_notifies_owner())
    asyncio.run(test_start_log())
    asyncio.run(test_unverified_flow())
    asyncio.run(test_foreign_join_request_approved())
    asyncio.run(test_muted_user_join_detected())
    asyncio.run(test_tag_exempts_player())
    asyncio.run(test_reset_application())
    asyncio.run(test_quiz_flow())
    asyncio.run(test_coins_commands())
    asyncio.run(test_admin_coins_and_balance())
    asyncio.run(test_shop_flow())
    asyncio.run(test_profile())
    asyncio.run(test_likes())
    asyncio.run(test_purchases_and_shop_menu())
    asyncio.run(test_message_reward())
    asyncio.run(test_member_without_app_can_apply())
    asyncio.run(test_chests())
    asyncio.run(test_emoji_set())
    asyncio.run(test_dice())
    asyncio.run(test_dice_panel())
    asyncio.run(test_dice_command_cooldown())
    asyncio.run(test_dice_streak())
    test_mafia_logic()
    test_register_handlers()
    print(f"\nПройдено тестов: {passed}")


if __name__ == "__main__":
    main()
