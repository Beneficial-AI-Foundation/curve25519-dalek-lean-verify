#!/usr/bin/env bash
tmp_dir=$(mktemp -d)
mkdir "$tmp_dir"/logs
cp "$1" "$tmp_dir"/logs
uv run inspect view bundle --log-dir "$tmp_dir"/logs --output-dir "$tmp_dir"/logs_www
echo "Upload the full path $tmp_dir/logs_www"
