#!/usr/bin/env bash
# Source data only: T2,T19 modulo 625, with recursive transfer maps.
# Verification uses t_n=n^(125q)T_n and r=(d+50q) mod 100.
# Store untwisted actions, as required by the loader (it applies the twist once).
# Ascending sources from degree zero, per the revised launch request.
# Source completion does not assert that classification identities pass.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work="$project_root/source_data/p5_mod625_recursive"
build="$project_root/nim/.p5-mod625-source-build"
unit=hecke-p5-mod625-sources.service
workers="${2:-4}"
case "${1:-}" in
  start|resume)
    [[ "$workers" =~ ^[1-4]$ ]] || { echo 'workers must be 1..4'; exit 2; }
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Source computation already running.'; exit 1
    fi
    if [[ ! -x "$build/compute_source_data" ]]; then
      mkdir -p "$build"
      cp "$project_root/nim/compute_source_data" "$build/compute_source_data"
    fi
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=MemoryHigh=16G --property=MemoryMax=20G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      --setenv=LD_PRELOAD=/usr/lib64/libz.so.1 \
      /usr/bin/python3 "$project_root/python/run_source_data.py" \
      --executable "$build/compute_source_data" \
      --output "$work" --prime 5 --exponent 4 \
      --hecke 2,19 --degree-modulus 2 --residues 0 \
      --minimum-degree 0 --degree-bound 3250 --orientations 0,1,2,3 \
      --orientation-threshold 750 --lower-orientations 0 \
      --workers "$workers" --module-cache-dir "$work/.module_cache"
    ;;
  status)
    if [[ -f "$work/status.json" ]]; then
      jq '{state,working_modulus,orientations,workers,completed_count,total_degrees,
        orientation_threshold,lower_orientations,
        active_degrees,failed,archive_bytes,heartbeat_at}' "$work/status.json"
    fi
    systemctl --user show "$unit" --property=ActiveState --property=SubState --property=MainPID
    ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {start [workers]|resume [workers]|status|stop}"; exit 2 ;;
esac
