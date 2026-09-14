#!/usr/bin/env bash
# Manage production of recorded intermediate elements for the modulo-125 relations.
# The mathematical tests are in the native verifier; status only reports process progress.
# Compact auxiliary-element packets, not source recomputation.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
unit=hecke-mod125-witnesses.service
output="$project_root/verification_data/mod125_compact"
case "${1:-}" in
  start|resume)
    workers="${2:-2}"
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Witness producer is already running.'; exit 1
    fi
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=16G --property=MemoryMax=20G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      --setenv=OPENBLAS_NUM_THREADS=1 --setenv=OMP_NUM_THREADS=1 \
      "$project_root/nim/.verify-hecke-relations-build/produce_verification_data" \
      --project-root "$project_root" --output "$output" --workers "$workers" \
      --supplementary-source-directory "$project_root/source_data/p5_mod625_lower_minus" \
      --supplementary-witness-directory "$project_root/verification_data/mod125_lower_minus/packets"
    ;;
  status)
    service_state=$(systemctl --user show "$unit" -p ActiveState --value 2>/dev/null || true)
    service_pid=$(systemctl --user show "$unit" -p MainPID --value 2>/dev/null || true)
    jq --arg service_state "$service_state" --arg service_pid "$service_pid" \
      '{state,observed_state:(if .state == "running" and
        ($service_state != "active" or $service_pid == "0" or $service_pid == "")
        then "not_running" else .state end),service_state:$service_state,
        service_pid:$service_pid,workers,completed_count,total_cases,checkpoint_hits,active_degrees,active,
        failed,packet_count,packet_bytes,elapsed_seconds,heartbeat_at,eta_note}' \
      "$output/status.json"
    ;;
  stop)
    systemctl --user stop "$unit"
    ;;
  *) echo "usage: bash $0 {start [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
