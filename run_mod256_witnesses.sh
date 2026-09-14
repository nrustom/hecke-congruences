#!/usr/bin/env bash
# Manage the queued production of intermediate elements for the modulo-256 relations.
# The Python queue checks its predecessor before starting native verification.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
unit=hecke-mod256-witnesses.service
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
      /usr/bin/python3 "$project_root/python/queue_mod256_witnesses.py" --workers "$workers"
    ;;
  status) jq . "$project_root/verification_data/mod256_compact/status.json" ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {queue [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
