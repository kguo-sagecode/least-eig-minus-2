#!/usr/bin/env bash
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$script_dir"
mkdir -p .sage .tmp .cache data
export DOT_SAGE="$script_dir/.sage"
export TMPDIR="$script_dir/.tmp"
export XDG_CACHE_HOME="$script_dir/.cache"
export MPLCONFIGDIR="$script_dir/.cache/matplotlib"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONUNBUFFERED=1
export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
sage_bin="${SAGE_BIN:-sage}"
for script in c*.sage remark311_ldl.sage verify_certificates.sage; do
    script_start=$SECONDS
    "$sage_bin" "$script" 2>&1 | tee "${script%.sage}.log"
    printf 'elapsed_seconds: %s\n' "$((SECONDS-script_start))" | tee -a "${script%.sage}.log"
done
