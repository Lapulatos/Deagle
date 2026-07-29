#!/usr/bin/env bash

set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_dir=$(cd -- "$script_dir/.." && pwd)
jobs=${JOBS:-1}
output_dir=${1:-"$repo_dir/svcomp_stuff"}

mkdir -p "$output_dir"

make -C "$repo_dir/src" clean
make -C "$repo_dir/src" -j"$jobs" \
  CP_EXTRA_CXXFLAGS=-DDEAGLE_PURE_SPIN_WAIT
cp "$repo_dir/src/cbmc/deagle_exe" "$output_dir/deagle_pure_spin_exe"

make -C "$repo_dir/src" clean
make -C "$repo_dir/src" -j"$jobs"
cp "$repo_dir/src/cbmc/deagle_exe" "$output_dir/deagle_core_exe"

"${CXX:-g++}" -std=c++17 -O2 \
  "$script_dir/deagle-native-dispatch.cpp" \
  -o "$output_dir/deagle_exe"

printf 'Built native Deagle pair:\n'
printf '  dispatcher: %s\n' "$output_dir/deagle_exe"
printf '  baseline: %s\n' "$output_dir/deagle_core_exe"
printf '  pure spin: %s\n' "$output_dir/deagle_pure_spin_exe"
