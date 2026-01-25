#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lakefile_src="$root/lakefile.toml"
out_dir="$root/artifacts/leanobserve-profile"
out_json="$out_dir/trace-profiler.json"
targets=()
rehash=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      out_json="$2"
      shift 2
      ;;
    --rehash)
      rehash=true
      shift
      ;;
    --)
      shift
      targets+=("$@")
      break
      ;;
    *)
      targets+=("$1")
      shift
      ;;
  esac
done

if rg -n "moreLeanArgs|weakLeanArgs" "$lakefile_src" >/dev/null; then
  echo "lakefile.toml already defines more/weakLeanArgs; update scripts/trace-profiler.sh to merge." >&2
  exit 1
fi

mkdir -p "$out_dir"
tmp_lakefile="$out_dir/lakefile.trace.toml"

cp "$lakefile_src" "$tmp_lakefile"
cat >> "$tmp_lakefile" <<EOF

weakLeanArgs = [
  "-Dtrace.profiler=true",
  "-Dtrace.profiler.useHeartbeats=true",
  "-Dtrace.profiler.threshold=200",
  "-Dtrace.profiler.output=$out_json",
  "-j1"
]
EOF

rm -f "$out_json"
if [[ ${#targets[@]} -eq 0 ]]; then
  echo "usage: scripts/trace-profiler.sh [--out path] [--rehash] -- <target>" >&2
  echo "note: pass a single module target to avoid concurrent writes to the JSON output." >&2
  exit 1
fi

lake_args=(--old)
if [[ "$rehash" == "true" ]]; then
  lake_args+=(--rehash)
fi

lake --file "$tmp_lakefile" build "${lake_args[@]}" "${targets[@]}"
echo "wrote $out_json"
