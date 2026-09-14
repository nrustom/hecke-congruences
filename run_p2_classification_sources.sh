#!/usr/bin/env bash
# Manage the unsplit direct Manin sources for the dyadic classification tests.
# These stages produce source data, not verification of the terminal relations.
# Full unsplit sources: ascending lower degrees, then induction degrees.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work="$project_root/source_data/p2_classification_sources"
unit=hecke-p2-classification-sources.service
workers="${2:-4}"
case "${1:-}" in
  start|resume)
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Source computation already running.'; exit 1
    fi
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=16G --property=MemoryMax=20G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      /bin/bash "$project_root/run_p2_classification_sources.sh" run "$workers"
    ;;
  run)
    mkdir -p "$work"
    # Run one source-production stage with its fixed modulus, degree range and selected Hecke operators.
    # The shared module cache permits reuse of lower-degree recursive sources.
    run_stage() {
      local name="$1" exponent="$2" hecke="$3" residue_modulus="$4"
      local residues="$5" minimum="$6" bound="$7"
      printf '%s\n' "$name" > "$work/current_stage.txt"
      /usr/bin/python3 "$project_root/python/run_source_data.py" \
        --executable "$project_root/nim/.source-scan-build/compute_source_data" \
        --output "$work/$name" --prime 2 --exponent "$exponent" \
        --hecke "$hecke" --degree-modulus "$residue_modulus" --residues "$residues" \
        --minimum-degree "$minimum" --degree-bound "$bound" --workers "$workers" \
        --module-cache-dir "$work/.module_cache/m${exponent}_T${hecke}"
    }
    run_stage hard_T3_lower 12 3 16 2,4,10,12 0 4096
    run_stage easy_T3_lower 10 3 16 0,6,8,14 0 1024
    run_stage T5_lower 9 5 2 0 0 512
    run_stage hard_T3_induction 12 3 16 2,4,10,12 4096 10240
    run_stage easy_T3_induction 10 3 16 0,6,8,14 1024 2560
    run_stage T5_induction 9 5 2 0 512 1280
    printf '%s\n' completed > "$work/current_stage.txt"
    ;;
  status)
    if [[ -f "$work/current_stage.txt" ]]; then
      stage=$(<"$work/current_stage.txt")
      printf 'stage: %s\n' "$stage"
      if [[ -f "$work/$stage/status.json" ]]; then
        jq '{state,prime,exponent,hecke_indices,workers,completed_count,total_degrees,active_degrees,failed,archive_bytes}' "$work/$stage/status.json"
      fi
    fi
    systemctl --user show "$unit" --property=ActiveState --property=SubState --property=MainPID
    ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {start [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
