#!/usr/bin/env bash
# Run inside a synced persvati pbuild lane.  Stdout is the benchmark raw log;
# load/CPU/frequency telemetry goes to the path supplied as argument 1.
set -euo pipefail

telemetry=${1:?usage: capture-session.sh TELEMETRY.csv}
samples_prove=${DREGG_STABILITY_PROVE_SAMPLES:-30}
samples_verify=${DREGG_STABILITY_VERIFY_SAMPLES:-100}
warmups=${DREGG_STABILITY_WARMUPS:-8}
cpus=${DREGG_STABILITY_CPUSET:-22-23}
rayon_threads=${DREGG_STABILITY_RAYON_THREADS:-2}
binary=target/release/direct_logic_dregg_workloads_benchmark

test -x "$binary"
printf 'utc,load1,load5,load15,runnable,total_tasks,cpu_user,cpu_nice,cpu_system,cpu_idle,cpu_iowait,cpu_irq,cpu_softirq,cpu_steal,cpu_freq_khz\n' > "$telemetry"

monitor() {
  while :; do
    read -r load1 load5 load15 runnable _ < /proc/loadavg
    read -r _ cpu_user cpu_nice cpu_system cpu_idle cpu_iowait cpu_irq cpu_softirq cpu_steal _ < /proc/stat
    cpu_freq=na
    if [[ "$cpus" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      cpu_freq=""
      for cpu in $(seq "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}"); do
        path="/sys/devices/system/cpu/cpu${cpu}/cpufreq/scaling_cur_freq"
        value=na
        test ! -r "$path" || value=$(<"$path")
        cpu_freq="${cpu_freq}${cpu}:${value}:"
      done
      cpu_freq=${cpu_freq%:}
    fi
    printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
      "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" "$load1" "$load5" "$load15" \
      "${runnable%/*}" "${runnable#*/}" "$cpu_user" "$cpu_nice" "$cpu_system" \
      "$cpu_idle" "$cpu_iowait" "$cpu_irq" "$cpu_softirq" "$cpu_steal" "$cpu_freq" \
      >> "$telemetry"
    sleep 1
  done
}

monitor &
monitor_pid=$!
trap 'kill "$monitor_pid" 2>/dev/null || true; wait "$monitor_pid" 2>/dev/null || true' EXIT

taskset --cpu-list "$cpus" env \
  RAYON_NUM_THREADS="$rayon_threads" \
  DREGG_DLOGIC_PROVE_SAMPLES="$samples_prove" \
  DREGG_DLOGIC_VERIFY_SAMPLES="$samples_verify" \
  DREGG_DLOGIC_WARMUPS="$warmups" \
  "$binary"
