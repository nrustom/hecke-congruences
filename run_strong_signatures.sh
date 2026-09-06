#!/usr/bin/env bash
# Build the Nim/libpari scanner if necessary, then replace this shell with it.
set -euo pipefail
repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
build_dir="$repo_dir/nim/.strong-signatures-build"
binary="$build_dir/strong_signatures"

if ! command -v nim >/dev/null 2>&1; then
    echo 'nim is not on PATH; activate your Nim installation first.' >&2
    exit 1
fi
pari_options=()
if [[ -n "${PARI_PREFIX:-}" ]]; then
    pari_options+=("-d:pari_prefix=$PARI_PREFIX")
elif [[ -f "${HOME}/.conda/envs/sage/include/pari/pari.h" ]]; then
    pari_options+=("-d:pari_prefix=${HOME}/.conda/envs/sage")
fi
mkdir -p "$build_dir"
build_configuration="$(command -v nim) ${pari_options[*]}"
if [[ ! -x "$binary" || "$repo_dir/nim/strong_signatures.nim" -nt "$binary" ||
      "$repo_dir/nim/pari_kernel.nim" -nt "$binary" ||
      ! -f "$build_dir/configuration" ||
      "$(<"$build_dir/configuration")" != "$build_configuration" ]]; then
    nim c -d:release "${pari_options[@]}" \
        --nimcache:"$build_dir/cache" --out:"$binary" \
        "$repo_dir/nim/strong_signatures.nim"
    printf '%s\n' "$build_configuration" > "$build_dir/configuration"
fi
cd "$repo_dir"
exec "$binary" "$@"
