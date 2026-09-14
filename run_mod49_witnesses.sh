#!/usr/bin/env bash
# Manage compact intermediate-element files for the modulo-49 relation presentations.
# Completed predecessor coverage is required before the queued arithmetic starts.
# Never launch arithmetic before successful completion of the mod125 producer.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
unit=hecke-mod49-witnesses.service
output="$project_root/verification_data/mod49_compact"
case "${1:-}" in
  queue|start|resume)
    workers="${2:-4}"
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Already queued or running.'; exit 1
    fi
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=16G --property=MemoryMax=20G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      --setenv=OPENBLAS_NUM_THREADS=1 --setenv=OMP_NUM_THREADS=1 \
      /usr/bin/python3 "$project_root/python/queue_mod49_witnesses.py" --workers "$workers"
    ;;
  status)
    [[ ! -f "$output/status.json" ]] || jq . "$output/status.json"
    for stage in G_mod49 Q_selectors_mod343; do
      if [[ -f "$output/$stage/status.json" ]]; then
        jq --arg stage "$stage" '{stage:$stage,state,workers,completed_count,total_cases,
          checkpoint_hits,active,failed,packet_bytes,heartbeat_at}' "$output/$stage/status.json"
      fi
    done
    systemctl --user show "$unit" -p ActiveState -p MainPID
    ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {queue [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
