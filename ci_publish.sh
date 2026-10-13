#!/usr/bin/env bash
# Кладе news.db у гілку "data", а сторінку у гілку "pages" (як index.html).
# Кожна гілка має один-єдиний коміт, щоб репозиторій не розростався.
set -eu
REMOTE="${REMOTE:-https://x-access-token:${GITHUB_TOKEN:-}@github.com/${GITHUB_REPOSITORY:-}.git}"

push_branch() {
  branch="$1"; shift
  dir="$(mktemp -d)"
  for pair in "$@"; do cp "${pair%%:*}" "$dir/${pair##*:}"; done
  touch "$dir/.nojekyll"
  ( cd "$dir"
    git init -q -b "$branch"
    git config user.name "news-bot"
    git config user.email "news-bot@users.noreply.github.com"
    git add -A
    git commit -q -m "update $(date -u +%Y-%m-%dT%H:%MZ)"
    git push -q -f "$REMOTE" "$branch" )
}

push_branch data  data/news.db:news.db
push_branch pages data/news.html:index.html
echo "Опубліковано."
