#!/usr/bin/env bash
# Queue the two prime-7 source stages, including the maps needed for recursive verification.
# The predecessor gate checks source coverage, not the later terminal identities.
# Fresh source archives with recursive transfer maps. Old archives stay intact.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work="$project_root/source_data/p7_mod49_transfer_maps"
build="$project_root/nim/.p7-transfer-source-build"
unit=hecke-p7-mod49-transfer-sources.service
predecessor=hecke-p5-mod625-sources.service
workers="${2:-4}"
case "${1:-}" in
  queue|start|resume)
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Already queued or running.'; exit 1
    fi
    mkdir -p "$work" "$build"
    if [[ ! -x "$build/compute_source_data" ]]; then
      cp "$project_root/nim/compute_source_data" "$build/compute_source_data"
      cp "$project_root/python/run_source_data.py" "$build/run_source_data.py"
    fi
    # All launch modes retain the success gate, including after a restart.
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=16G --property=MemoryMax=20G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      --setenv=LD_PRELOAD=/usr/lib64/libz.so.1 \
      /bin/bash "$project_root/run_p7_mod49_transfer_source_data.sh" run "$workers"
    ;;
  run)
    previous_status="$project_root/source_data/p5_mod625_recursive/status.json"
    printf '%s\n' waiting_for_mod125_sources > "$work/current_stage.txt"
    echo 'Waiting for successful completion of modulo-625 source scan.'
    while true; do
      if [[ -f "$previous_status" ]] && jq -e '
        .state == "completed" and .prime == 5 and .exponent == 4
        and .total_degrees == 1625 and .completed_count == .total_degrees
        and (.failed | length) == 0 and (.active_degrees | length) == 0
        ' "$previous_status" >/dev/null &&
          ! systemctl --user is-active --quiet "$predecessor"; then
        break
      fi
      sleep 30
    done
    # Run one source-production stage with its fixed modulus, degree range and selected Hecke operators.
    # The shared module cache permits reuse of lower-degree recursive sources.
    run_stage() {
      local name="$1" exponent="$2"
      printf '%s\n' "$name" > "$work/current_stage.txt"
      /usr/bin/python3 "$build/run_source_data.py" \
        --executable "$build/compute_source_data" --output "$work/$name" \
        --prime 7 --exponent "$exponent" --hecke 3,29 \
        --degree-modulus 2 --residues 0 --workers "$workers" \
        --module-cache-dir "$work/.module_cache/m${exponent}_T3_T29"
    }
    run_stage G_mod49 2
    run_stage Q_selectors_mod343 3
    printf '%s\n' completed > "$work/current_stage.txt"
    ;;
  status)
    if [[ -f "$work/current_stage.txt" ]]; then
      printf 'stage: %s\n' "$(<"$work/current_stage.txt")"
    fi
    for name in G_mod49 Q_selectors_mod343; do
      if [[ -f "$work/$name/status.json" ]]; then
        jq --arg stage "$name" '{stage:$stage,state,workers,completed_count,
          total_degrees,active_degrees,failed,archive_bytes}' "$work/$name/status.json"
      fi
    done
    systemctl --user show "$unit" --property=ActiveState --property=SubState --property=MainPID
    ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {queue [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
