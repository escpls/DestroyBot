FROM python:3.11-slim

WORKDIR /app

# pypi.org иногда отвечает медленно с нод — увеличиваем таймаут и число повторов pip
ENV PIP_DEFAULT_TIMEOUT=120 PIP_RETRIES=10

COPY requirements.txt .
# Очищаем BOM и невидимые символы из requirements.txt
RUN sed -i 's/^\xEF\xBB\xBF//' requirements.txt 2>/dev/null || true && \
    sed -i 's/^\xFF\xFE//' requirements.txt 2>/dev/null || true && \
    sed -i 's/^\xFE\xFF//' requirements.txt 2>/dev/null || true && \
    tr -d '\r\0' < requirements.txt > requirements.txt.tmp && mv requirements.txt.tmp requirements.txt 2>/dev/null || true
# Проверяем, что requirements.txt скопирован
RUN cat requirements.txt && echo '--- Requirements.txt содержимое выше ---'
# Устанавливаем зависимости из requirements.txt
# Пропускаем aiogram если он есть - установим правильную версию отдельно
RUN set -e && \
    pip_install_retry() { \
        pkg="$1"; attempt=1; \
        while [ "$attempt" -le 3 ]; do \
            if pip install --no-cache-dir "$pkg"; then return 0; fi; \
            echo "WARNING: pip install failed for $pkg (attempt $attempt/3), retry in 10s..."; \
            attempt=$((attempt + 1)); \
            [ "$attempt" -le 3 ] && sleep 10; \
        done; \
        return 1; \
    } && \
    echo 'Начинаем установку зависимостей из requirements.txt...' && \
    if [ ! -f requirements.txt ] || [ ! -s requirements.txt ]; then \
        echo 'WARNING: requirements.txt пуст или не существует'; \
    else \
        while IFS= read -r line || [ -n "$line" ]; do \
            [ -z "$line" ] && continue; \
            # Очищаем BOM и невидимые символы, обрезаем пробелы \
            line=$(echo "$line" | sed 's/^\xEF\xBB\xBF//' | sed 's/^\xFF\xFE//' | sed 's/^\xFE\xFF//' | tr -d '\r\0' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//'); \
            [ -z "$line" ] && continue; \
            case "$line" in \
              \#*) continue ;; \
            esac; \
            echo "=== Устанавливаем: $line ===" && \
            if echo "$line" | grep -qiE '^(sqlite3|json|os|sys|time|datetime|re|random|math|logging|asyncio|collections|itertools|functools|operator|pathlib|urllib|http|socket|ssl|hashlib|base64|uuid|threading|multiprocessing|queue|concurrent|subprocess|shutil|tempfile|pickle|copy|weakref|gc|ctypes|struct|array|binascii|codecs|encodings|locale|gettext|argparse|configparser|csv|io|textwrap|string|unicodedata|readline|rlcompleter)$'; then \
                echo "ℹ️  Пропускаем встроенный модуль Python: $line (не требует установки)"; \
                continue; \
            fi && \
            if echo "$line" | grep -qiE '(python-dotenv|tgcrypto).*=='; then \
                if ! pip_install_retry "$line"; then \
                    echo "WARNING: Не удалось установить $line (возможно несуществующая версия или сеть)"; \
                    # Пробуем установить без версии \
                    pkg_name=$(echo "$line" | sed 's/[<>=!].*//' | xargs); \
                    echo "Пробуем установить $pkg_name без версии..."; \
                    pip_install_retry "$pkg_name" || echo "WARNING: Не удалось установить $pkg_name даже без версии"; \
                else \
                    echo "✅ Успешно установлен: $line"; \
                fi; \
            else \
                if ! pip_install_retry "$line"; then \
                    echo "ERROR: Не удалось установить $line (проверьте сеть до pypi.org)" && exit 1; \
                else \
                    echo "✅ Успешно установлен: $line"; \
                fi; \
            fi; \
        done < requirements.txt; \
    fi && \
    echo 'Установка завершена' && \
    echo '=== Проверка установленных пакетов ===' && \
    (pip list 2>/dev/null | grep -E '(aiogram|dotenv|telegram|requests|supabase)' || echo 'WARNING: Некоторые модули не найдены') && \
    echo '=== Проверка python-dotenv ===' && \
    (pip show python-dotenv >/dev/null 2>&1 && echo '✅ python-dotenv установлен' || echo '❌ python-dotenv НЕ установлен')

# Проверяем, что aiogram 3.x установлен правильно
RUN python -c 'from aiogram.client.default import DefaultBotProperties; print("✅ aiogram 3.x установлен правильно")' 2>/dev/null || echo '⚠️ Проверка aiogram 3.x не прошла, но это может быть нормально'
RUN pip cache purge || true
# Проверяем, что python-telegram-bot установлен (используется в коде)
RUN python -c 'import telegram' 2>/dev/null || (echo 'ERROR: python-telegram-bot используется в коде, но не установлен. Добавьте его в requirements.txt!' && exit 1)

# Очищаем pip кеш
RUN pip cache purge || true

# Копируем код приложения
COPY . .

# Директория для постоянных данных: БД, файлы состояния, логи.
# Монтируется как Docker volume — данные сохраняются при перезапуске.
# В коде бота используйте: import os; DATA_DIR = os.getenv('DATA_DIR', '/app/data')
ENV DATA_DIR=/app/data
RUN mkdir -p /app/data && chmod 777 /app/data
RUN chown -R $(id -u):$(id -g) /app/data 2>/dev/null || chown -R 1000:1000 /app/data || true


# Определяем точку входа
CMD ["python", "bot.py"]
