#!/usr/bin/env bash
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
build="$project_root/nim/.verify-hecke-relations-build"
mkdir -p "$build"
# Set NATIVE_CPU=0 for a binary intended for another CPU.
cpu_flags=()
if [[ "${NATIVE_CPU:-1}" == 1 ]]; then cpu_flags+=(--passC:-march=native); fi
if [[ -n "${FLINT_LIBRARY:-}" ]]; then cpu_flags+=("-d:flint_library=$FLINT_LIBRARY"); fi
nim c -d:release --passC:-O3 "${cpu_flags[@]}" \
  --nimcache:"$build/cache" --out:"$build/verify_hecke_relations" \
  "$project_root/nim/verify_hecke_relations.nim"
echo "Built $build/verify_hecke_relations"
