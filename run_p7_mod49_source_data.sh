#!/usr/bin/env bash
# Compatibility runner for full direct source archives at working precision 49 and 343.
# This older format is distinct from the compact archives with recursive transfer maps.

set -uo pipefail

project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
compute_source_data="$project_root/nim/compute_source_data"
archive_builder="$project_root/python/build_source_data_archive.py"
work_root="$project_root/source_data/.p7_mod49_nim_work"
pid_file="$work_root/supervisor.pid"
workers_file="$work_root/workers"
supervisor_log="$work_root/supervisor.log"
complete_marker="$work_root/workflow.complete"
failure_marker="$work_root/workflow.failed"
service_unit="hecke-p7-mod49-source.service"

flint_library_directory="/home/nrustom/.conda/envs/sage/lib"
export LD_LIBRARY_PATH="$flint_library_directory:${LD_LIBRARY_PATH:-}"


# Test whether a numeric process identifier is currently visible; this does not identify its computation.
is_live_pid() {
    local pid="$1"
    [[ "$pid" =~ ^[0-9]+$ ]] && kill -0 "$pid" 2>/dev/null
}


# Count existing per-degree archives without asserting their mathematical validity.
count_bundles() {
    local directory="$1"

    if [[ ! -d "$directory" ]]; then
        echo 0
        return
    fi

    find "$directory" -type f -name replay_bundle.npz | wc -l
}


# Count recorded source-production failures in this workflow directory.
count_failures() {
    if [[ ! -d "$work_root" ]]; then
        echo 0
        return
    fi

    find "$work_root" -type f -name compute.failed | wc -l
}


# Produce one full direct source archive or reuse its completed file.
# Publish a new archive only after successful completion; failed partial output is removed.
run_degree() {
    local exponent="$1"
    local degree="$2"
    local modulus
    local stage_root

    if [[ "$exponent" == 3 ]]; then
        modulus=343
        stage_root="$work_root/mod343"
    elif [[ "$exponent" == 2 ]]; then
        modulus=49
        stage_root="$work_root/mod49"
    else
        echo "unsupported exponent: $exponent" >&2
        return 2
    fi

    local degree_root="$stage_root/degree_$degree"
    local output="$degree_root/replay_bundle.npz"
    local partial="$degree_root/replay_bundle.partial.$BASHPID.npz"
    local degree_log="$degree_root/compute.log"
    local degree_failure="$degree_root/compute.failed"

    mkdir -p "$degree_root"

    if [[ -s "$output" ]]; then
        echo "reusing modulus $modulus degree $degree"
        return 0
    fi

    rm -f "$degree_root"/replay_bundle.partial.*.npz "$degree_failure"
    echo "starting modulus $modulus degree $degree"

    # This compatibility runner feeds the legacy full-replay archive builder.
    if "$compute_source_data" \
        --direct \
        --prime 7 \
        --exponent "$exponent" \
        --degree "$degree" \
        --hecke 3,29 \
        --output "$partial" \
        >"$degree_log" 2>&1
    then
        mv -f "$partial" "$output"
        echo "completed modulus $modulus degree $degree"
        return 0
    else
        local return_code=$?
        printf 'exit code %s\n' "$return_code" >"$degree_failure"
        rm -f "$partial"
        echo "failed modulus $modulus degree $degree; see $degree_log" >&2
        tail -20 "$degree_log" >&2 || true
        return "$return_code"
    fi
}

export -f run_degree
export project_root compute_source_data archive_builder work_root
export LD_LIBRARY_PATH


# Schedule the inclusive even-degree interval with the configured worker limit.
run_range() {
    local exponent="$1"
    local first_degree="$2"
    local last_degree="$3"

    seq "$first_degree" 2 "$last_degree" |
        xargs -r -P "$workflow_workers" -n 1 \
            bash -c 'run_degree "$1" "$2"' _ "$exponent"
}


# Combine per-degree sources into a consolidated archive and publish it after the builder succeeds.
build_archive() {
    local exponent="$1"
    local maximum_degree="$2"
    local input_root="$3"
    local final_output="$4"
    local partial_output="${final_output%.npz}.partial.npz"

    rm -f "$partial_output"

    python3 "$archive_builder" \
        --input-root "$input_root" \
        --output "$partial_output" \
        --prime 7 \
        --exponent "$exponent" \
        --minimum-degree 0 \
        --maximum-degree "$maximum_degree" \
        --degree-step 2 || return $?

    mv -f "$partial_output" "$final_output"
}


# Run both fixed-precision source ranges and then consolidate their completed archives.
run_workflow() {
    # At each precision, compute the exact induction range first.
    run_range 3 392 2448 || return $?
    run_range 3 0 390 || return $?

    run_range 2 56 348 || return $?
    run_range 2 0 54 || return $?

    echo "consolidating the modulus-343 archive"
    build_archive \
        3 \
        2448 \
        "$work_root/mod343" \
        "$project_root/source_data/p7_krw49_Q_selectors_all_degrees_mod343.npz" \
        || return $?

    echo "consolidating the modulus-49 archive"
    build_archive \
        2 \
        348 \
        "$work_root/mod49" \
        "$project_root/source_data/p7_krw49_G_all_degrees_mod49.npz" \
        || return $?
}


# Launch the workflow as a user service after checking the worker count and duplicate-service guard.
start_workflow() {
    local requested_workers="${1:-4}"

    if [[ ! "$requested_workers" =~ ^[1-9][0-9]*$ ]]; then
        echo "workers must be a positive integer" >&2
        return 2
    fi

    mkdir -p "$work_root"

    if systemctl --user is-active --quiet "$service_unit"; then
        echo "the workflow service is already running" >&2
        return 1
    fi

    if [[ ! -x "$compute_source_data" ]]; then
        echo "missing executable: $compute_source_data" >&2
        return 1
    fi

    rm -f "$complete_marker" "$failure_marker"
    printf '%s\n' "$requested_workers" >"$workers_file"
    : >"$supervisor_log"

    systemd-run \
        --user \
        --unit="${service_unit%.service}" \
        --collect \
        --property="WorkingDirectory=$project_root" \
        "$project_root/run_p7_mod49_source_data.sh" \
        _run "$requested_workers" >/dev/null || return $?

    sleep 1

    local supervisor_pid
    supervisor_pid=$(systemctl --user show \
        --property=MainPID \
        --value \
        "$service_unit")
    printf '%s\n' "$supervisor_pid" >"$pid_file"

    echo "started with pid $supervisor_pid and $requested_workers workers"
    echo "status: $0 status"
}


# Report service state, existing source counts and recent log output without starting arithmetic.
show_status() {
    local pid=""
    local state="not_started"
    local modulus_343_count
    local modulus_49_count
    local failure_count

    [[ -f "$pid_file" ]] && pid=$(<"$pid_file")

    if systemctl --user is-active --quiet "$service_unit"; then
        state="running"
    elif [[ -f "$complete_marker" ]]; then
        state="completed"
    elif [[ -f "$failure_marker" ]]; then
        state="failed"
    elif [[ -d "$work_root" ]]; then
        state="stopped_or_incomplete"
    fi

    modulus_343_count=$(count_bundles "$work_root/mod343")
    modulus_49_count=$(count_bundles "$work_root/mod49")
    failure_count=$(count_failures)

    echo "state: $state"
    [[ -n "$pid" ]] && echo "supervisor pid: $pid"
    [[ -f "$workers_file" ]] && echo "workers: $(<"$workers_file")"
    echo "modulus 343: $modulus_343_count / 1225 degrees"
    echo "modulus 49:  $modulus_49_count / 175 degrees"
    echo "failed degrees: $failure_count"

    if [[ "$state" == running ]]; then
        echo "active computations:"
        systemctl --user status "$service_unit" \
            --no-pager --lines=0 2>/dev/null |
            sed -n '/CGroup:/,$p' || true
    fi

    if [[ -f "$supervisor_log" ]]; then
        echo "recent log:"
        tail -12 "$supervisor_log"
    fi
}


# Stop the workflow service while retaining completed degree files for reuse.
stop_workflow() {
    if ! systemctl --user is-active --quiet "$service_unit"; then
        echo "the workflow service is not running"
        return 0
    fi

    systemctl --user stop "$service_unit"
    echo "stopped the workflow service; completed degree files are reusable"
}


# Execute the service workflow and record its completion or failure marker.
internal_run() {
    workflow_workers="$1"
    export workflow_workers

    if run_workflow; then
        date --iso-8601=seconds >"$complete_marker"
        echo "workflow completed"
        return 0
    fi

    local return_code=$?
    date --iso-8601=seconds >"$failure_marker"
    echo "workflow failed with exit code $return_code" >&2
    return "$return_code"
}


case "${1:-}" in
    start)
        start_workflow "${2:-4}"
        ;;
    status)
        show_status
        ;;
    stop)
        stop_workflow
        ;;
    _run)
        internal_run "${2:-4}" >>"$supervisor_log" 2>&1
        ;;
    *)
        echo "usage: $0 {start [workers]|status|stop}" >&2
        exit 2
        ;;
esac
