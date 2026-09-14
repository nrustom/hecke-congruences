#!/usr/bin/env bash
# Manage the modulo-49 and modulo-343 source stages with recursive construction.
# Source completion does not by itself certify the displayed classification relations.
# Ascending full-source computations, both signs, with shared recursive maps.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work="$project_root/source_data/p7_mod49_recursive"
build="$project_root/nim/.p7-recursive-source-build"
unit=hecke-p7-mod49-recursive-sources.service
workers="${2:-4}"
# The Conda zlib can report Z_BUF_ERROR at EOF on valid 8192-byte gzip
# checkpoints. Preload Fedora's system zlib, retaining Conda's FLINT path.
# This changes neither the producer binary nor the checkpoint encoding/tags.
zlib_library="${SYSTEM_ZLIB:-/usr/lib64/libz.so.1}"
case "${1:-}" in
  start|resume)
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    [[ -r "$zlib_library" ]] || { echo 'Set SYSTEM_ZLIB to the system libz.so.1.' >&2; exit 2; }
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Source computation already running.'; exit 1
    fi
    # Freeze the producer for this scan; resume never replaces it.
    if [[ ! -x "$build/compute_source_data" ]]; then
      [[ -x "$project_root/nim/compute_source_data" ]] || {
        echo 'Build nim/compute_source_data first.' >&2; exit 1;
      }
      mkdir -p "$build"
      cp "$project_root/nim/compute_source_data" "$build/compute_source_data"
    fi
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=16G --property=MemoryMax=20G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      --setenv="LD_PRELOAD=$zlib_library" \
      /bin/bash "$project_root/run_p7_mod49_recursive_source_data.sh" run "$workers"
    ;;
  run)
    mkdir -p "$work"
    # Run one source-production stage with its fixed modulus, degree range and selected Hecke operators.
    # The shared module cache permits reuse of lower-degree recursive sources.
    run_stage() {
      local name="$1" exponent="$2"
      printf '%s\n' "$name" > "$work/current_stage.txt"
      /usr/bin/python3 "$project_root/python/run_source_data.py" \
        --executable "$build/compute_source_data" \
        --output "$work/$name" --prime 7 --exponent "$exponent" \
        --hecke 3,29 --degree-modulus 2 --residues 0 --workers "$workers" \
        --module-cache-dir "$work/.module_cache/m${exponent}_T3_T29"
    }
    run_stage G_mod49 2
    run_stage Q_selectors_mod343 3
    printf '%s\n' completed > "$work/current_stage.txt"
    ;;
  status)
    if [[ -f "$work/current_stage.txt" ]]; then
      stage=$(<"$work/current_stage.txt")
      printf 'stage: %s\n' "$stage"
      for name in G_mod49 Q_selectors_mod343; do
        if [[ -f "$work/$name/status.json" ]]; then
          jq --arg stage "$name" '{stage:$stage,state,prime,exponent,workers,
            completed_count,total_degrees,active_degrees,failed,archive_bytes}' \
            "$work/$name/status.json"
        fi
      done
    fi
    systemctl --user show "$unit" --property=ActiveState --property=SubState --property=MainPID
    ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {start [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
