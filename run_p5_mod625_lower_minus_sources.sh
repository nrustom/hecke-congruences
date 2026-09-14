#!/usr/bin/env bash
# Produce the missing lower-degree minus sources at working precision 625.
# They supplement, rather than replace, the sources already used by verification.
# Supplementary archives only: never overwrite sources used by verification.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work="$project_root/source_data/p5_mod625_lower_minus"
unit=hecke-p5-mod625-lower-minus.service
case "${1:-}" in
  start|resume)
    if systemctl --user is-active --quiet "$unit"; then
      echo 'Lower-minus computation already running.'; exit 1
    fi
    systemd-run --user --collect --unit="${unit%.service}" \
      --property="WorkingDirectory=$project_root" \
      --property=KillMode=control-group --property=TimeoutStopSec=30 \
      --property=Nice=10 --property=MemoryHigh=2G --property=MemoryMax=3G \
      --setenv=LD_LIBRARY_PATH=/home/nrustom/.conda/envs/sage/lib \
      --setenv=LD_PRELOAD=/usr/lib64/libz.so.1 \
      --setenv=OPENBLAS_NUM_THREADS=1 --setenv=OMP_NUM_THREADS=1 \
      /usr/bin/python3 "$project_root/python/run_source_data.py" \
      --executable "$project_root/nim/.p5-mod625-source-build/compute_source_data" \
      --output "$work" --prime 5 --exponent 4 --hecke 2,19 \
      --degree-modulus 2 --residues 0 --minimum-degree 0 --degree-bound 752 \
      --orientations 1,3 --workers 1 --module-cache-dir "$work/.module_cache"
    ;;
  status)
    jq '{state,completed_count,total_degrees,active_degrees,failed,archive_bytes,heartbeat_at}' "$work/status.json"
    ;;
  stop) systemctl --user stop "$unit" ;;
  *) echo "usage: bash $0 {start|resume|status|stop}"; exit 2 ;;
esac
