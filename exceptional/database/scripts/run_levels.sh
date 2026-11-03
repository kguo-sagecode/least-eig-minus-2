#!/bin/bash
# Grow the levels n = START..END-1 -> n+1, and after each step save the exceptional graphs
# on n vertices to the database.  Usage: run_levels.sh WORKDIR DBDIR START END NWORKERS
# The environment comes from the caller: nauty (labelg) and Python 3 with NumPy and SciPy on the
# PATH. Optional: PYTHON, the Python to use (default python3); grow.py reads LABELG and SORTMEM.
# WORKDIR/levels/log.txt gets one line per step: the numbers of graphs in and out; time, the
# seconds of the growth and of the merging (without extract.py); step_mem_MiB, the largest memory
# of the job during the step (with extract.py), sampled every second; job_peak_MiB, the job's
# high-water mark so far (cgroup memory.peak); maxrss_proc_kB, the largest resident set of a
# single process of the growth (GNU time %M; it is not a total). Here "the job" is the nearest
# memory cgroup (v2) from ours upwards with a memory limit, or ours if
# none has one; NA where there is no such cgroup, or no GNU time.
set -euo pipefail
W=$1; DB=$2; START=$3; END=$4; NW=$5
HERE=$(cd "$(dirname "$0")" && pwd)
PYTHON=${PYTHON:-python3}

CG=/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup 2>/dev/null || true)
d=$CG
while [ "$d" != /sys/fs/cgroup ] && [ "$(cat "$d/memory.max" 2>/dev/null || echo max)" = max ]; do
  d=${d%/*}
done
[ "$d" = /sys/fs/cgroup ] || CG=$d
[ -r "$CG/memory.current" ] || CG=
watch_mem() {   # sample memory.current every second; on SIGTERM, print the largest (MiB)
  local peak=0 cur
  trap 'echo $((peak >> 20)); exit 0' TERM
  while kill -0 $$ 2>/dev/null; do    # stop if this script has gone
    cur=$(cat "$CG/memory.current"); [ "$cur" -le "$peak" ] || peak=$cur
    sleep 1
  done
}
if /usr/bin/time -f %M -o /dev/null true 2>/dev/null; then
  timed() { /usr/bin/time -f %M -o "$@"; }
else
  timed() { echo NA > "$1"; shift; "$@"; }
fi

mkdir -p "$W/levels"
if [ ! -f "$W/levels/n01.g6" ]; then echo '@' > "$W/levels/n01.g6"; fi
for ((n=START; n<END; n++)); do
  a=$(printf %02d $n); b=$(printf %02d $((n+1)))
  t0=$(date +%s.%N)
  if [ -n "$CG" ]; then watch_mem > "$W/step$a.mem" & WATCH=$!; else echo NA > "$W/step$a.mem"; fi
  ok=0
  for attempt in 1 2 3; do
    rm -rf "$W/step$a"; mkdir -p "$W/step$a"
    if timed "$W/step$a.rss" "$PYTHON" "$HERE/grow.py" "$W/levels/n$a.g6" "$W/step$a" "$NW"; then
      if [ "$(cat "$W/step$a"/info.* | wc -l)" = "$(wc -l < "$W/levels/n$a.g6")" ]; then ok=1; break; fi
    fi
    echo "step $n attempt $attempt failed, retrying" | tee -a "$W/levels/log.txt"
  done
  [ $ok = 1 ] || { echo "step $n FAILED" | tee -a "$W/levels/log.txt"; exit 1; }
  LC_ALL=C sort -u -m -S 1G -T "$W/step$a" "$W/step$a"/children.* > "$W/levels/n$b.g6.tmp"
  mv -f "$W/levels/n$b.g6.tmp" "$W/levels/n$b.g6"
  cat "$W/step$a"/info.* | LC_ALL=C sort -S 4G -T "$W/step$a" > "$W/levels/info$a.txt"
  rm -rf "$W/step$a"
  t1=$(date +%s.%N)
  el=$(awk -v t0="$t0" -v t1="$t1" 'BEGIN { printf "%.3f", t1 - t0 }')
  "$PYTHON" "$HERE/extract.py" $n "$W/levels/info$a.txt" "$DB" "$el"
  if [ -n "$CG" ]; then kill $WATCH 2>/dev/null || true; wait $WATCH || true; fi
  mem=$(cat "$W/step$a.mem" 2>/dev/null || true)
  if [ -r "$CG/memory.peak" ]; then pk=$(( $(cat "$CG/memory.peak") >> 20 )); else pk=NA; fi
  echo "n=$n -> $((n+1)): in=$(wc -l < "$W/levels/n$a.g6") out=$(wc -l < "$W/levels/n$b.g6") time=$el step_mem_MiB=${mem:-NA} job_peak_MiB=$pk maxrss_proc_kB=$(cat "$W/step$a.rss") $(date +%T)" | tee -a "$W/levels/log.txt"
done
