#!/usr/bin/env bash
# Build the native finite-relation verifier; this script does not run a verification.
# The output is local to the repository and may use the current CPU instruction set.
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
nim c -d:release --passC:-O3 "${cpu_flags[@]}" \
  --nimcache:"$build/producer-cache" --out:"$build/produce_verification_data" \
  "$project_root/nim/produce_verification_data.nim"
echo "Built $build/produce_verification_data"
