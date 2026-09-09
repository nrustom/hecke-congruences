#!/usr/bin/env bash
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
unit=hecke-p3-ideal-source.service
build="$project_root/nim/.p3-ideal-build"
work="$project_root/source_data/p3_ideal_9_T2_mod2187"
case "${1:-}" in
  start|resume)
    workers="${2:-4}"
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    systemctl --user show-environment >/dev/null
    if systemctl --user is-active --quiet "$unit"; then
      echo 'The source computation is already running.'; exit 1
    fi
    mkdir -p "$build" "$work"
    nim c -d:release --passC:-O3 --passC:-march=native \
      --out:"$build/compute_p3_ideal_source_data" \
      "$project_root/nim/compute_p3_ideal_source_data.nim"
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=20G --property=MemoryMax=24G \
      /usr/bin/python3 "$project_root/python/run_p3_ideal_source_data.py" "$workers"
    echo "Monitor: $0 status"
    ;;
  status)
    systemctl --user show "$unit" --property=ActiveState --property=SubState --property=MainPID || true
    if [[ -f "$work/status.json" ]]; then cat "$work/status.json"; fi
    ;;
  stop)
    systemctl --user stop "$unit"
    echo 'Stopped the service and its worker cgroup. Completed archives are retained.'
    ;;
  *) echo "usage: $0 {start [1..4]|resume [1..4]|status|stop}"; exit 2 ;;
esac
