#!/usr/bin/env bash
# Забирає базу news.db з гілки "data" (якщо вона вже є).
set -u
REMOTE="${REMOTE:-https://x-access-token:${GITHUB_TOKEN:-}@github.com/${GITHUB_REPOSITORY:-}.git}"
mkdir -p data
if git ls-remote --exit-code --heads "$REMOTE" data >/dev/null 2>&1; then
  tmp="$(mktemp -d)"
  git clone -q --depth 1 --branch data "$REMOTE" "$tmp" && cp "$tmp/news.db" data/news.db && echo "База відновлена."
else
  echo "Бази ще немає, почнемо з нуля."
fi
exit 0
