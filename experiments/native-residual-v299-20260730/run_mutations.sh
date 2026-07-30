#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "usage: $0 DEAGLE_EXE BASE_SOURCE OUTPUT_DIR" >&2
  exit 2
fi

deagle_exe=$1
base_source=$2
output_dir=$3
mkdir -p "$output_dir"

make_variant() {
  local name=$1
  local old=$2
  local replacement=$3
  local source="$output_dir/$name.c"
  cp "$base_source" "$source"
  OLD="$old" REPLACEMENT="$replacement" perl -0pi -e \
    's/\Q$ENV{OLD}\E/$ENV{REPLACEMENT}/ or die "mutation did not match\n"' \
    "$source"
}

make_variant initial-mismatch \
  'pthread_create(&t1, 0, thread1, 0);' \
  'i_BA = 1; pthread_create(&t1, 0, thread1, 0);'
make_variant duplicate-bound \
  'i_BA < Bn && i_BA < An' \
  'i_BA < Bn && i_BA < Bn'
make_variant duplicate-array \
  'B[i_BA] == A[i_BA]' \
  'B[i_BA] == B[i_BA]'
make_variant disequality-word \
  'B[i_BA] == A[i_BA]' \
  'B[i_BA] != A[i_BA]'
make_variant step-two \
  'i_BA++;' \
  'i_BA += 2;'
make_variant worker-array-write \
  'i_AB++;' \
  'A[i_AB] = 0; i_AB++;'
make_variant worker-atomic \
  'while (i_AB < An && i_AB < Bn) {' \
  '__VERIFIER_atomic_begin(); while (i_AB < An && i_AB < Bn) {'
make_variant missing-join \
  'pthread_join(t2, 0);' \
  '(void)t2;'
make_variant index-address-escape \
  'pthread_create(&t1, 0, thread1, 0);' \
  'int *escaped_index = &i_AB; (void)escaped_index; pthread_create(&t1, 0, thread1, 0);'
make_variant index-type-mismatch \
  'int i_AB, i_BA, An, Bn;' \
  'unsigned int i_AB; int i_BA, An, Bn;'
make_variant extra-index-write \
  'pthread_join(t2, 0);' \
  'pthread_join(t2, 0); i_AB = 0;'
make_variant property-flip \
  'assume_abort_if_not(i_AB != i_BA);' \
  'assume_abort_if_not(i_AB == i_BA);'

printf 'variant\tadmission\n' > "$output_dir/summary.tsv"
for source in "$output_dir"/*.c; do
  name=$(basename "$source" .c)
  log="$output_dir/$name.log"
  timeout 3 stdbuf -oL "$deagle_exe" "$source" --32 \
    --refined-pointer-analysis --native-jces --deagle-nondet-bulk-init \
    > "$log" 2>&1 || true
  marker=$(grep 'NATIVE_SYMMETRIC_ARRAY_SCAN' "$log" | tail -1 || true)
  printf '%s\t%s\n' "$name" "${marker:-missing}" >> "$output_dir/summary.tsv"
done
