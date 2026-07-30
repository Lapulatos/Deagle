#!/bin/sh
set -eu

deagle_exe=$1
source_root=$2
output_dir=$3
mkdir -p "$output_dir"

subst="$source_root/chl-name-comparator-subst.wvr.c"
symm="$source_root/chl-name-comparator-symm.wvr.c"
trans="$source_root/chl-name-comparator-trans.wvr.c"

make_variant()
{
  name=$1
  base=$2
  old=$3
  new=$4
  cp "$base" "$output_dir/$name.c"
  OLD=$old NEW=$new perl -0pi -e '
    BEGIN { $old=$ENV{"OLD"}; $new=$ENV{"NEW"}; }
    s/\Q$old\E/$new/ or die "mutation did not match\n";
  ' "$output_dir/$name.c"
}

make_variant abort-name "$subst" \
  'extern void abort(void);' \
  'extern void stop_now(void);'
OLD='abort();' NEW='stop_now();' perl -0pi -e '
  BEGIN { $old=$ENV{"OLD"}; $new=$ENV{"NEW"}; }
  s/\Q$old\E/$new/g or die "mutation did not match\n";
' "$output_dir/abort-name.c"

make_variant custom-returning-abort "$subst" \
  'extern void abort(void);' \
  'void abort(void) {}'
make_variant positive-result-two "$subst" \
  'result_4 = ( current_6 == name_1 ) ? 1 : result_4;' \
  'result_4 = ( current_6 == name_1 ) ? 2 : result_4;'
make_variant positive-break-zero "$subst" \
  'break_7  = ( current_6 == name_1 ) ? 1 : break_7;' \
  'break_7  = ( current_6 == name_1 ) ? 0 : break_7;'
make_variant step-two "$subst" \
  'i_5++;' \
  'i_5 += 2;'
make_variant exit-assume-after-result "$subst" \
  'assume_abort_if_not( !( ( i_5 < 3 ) && !break_7 ) );
  result_4 = ( !break_7 ) ? minus(name_1, name_2) : result_4;' \
  'result_4 = ( !break_7 ) ? minus(name_1, name_2) : result_4;
  assume_abort_if_not( !( ( i_5 < 3 ) && !break_7 ) );'
make_variant step-before-negative-selector "$subst" \
  'result_4 = ( !break_7 && ( current_6 == name_2 ) ) ? ( 0 - 1 ) : result_4;' \
  'i_5++;
    result_4 = ( !break_7 && ( current_6 == name_2 ) ) ? ( 0 - 1 ) : result_4;'
OLD='i_5++;
  }' NEW='}' perl -0pi -e '
  BEGIN { $old=$ENV{"OLD"}; $new=$ENV{"NEW"}; }
  s/\Q$old\E/$new/ or die "mutation did not match\n";
' "$output_dir/step-before-negative-selector.c"
make_variant bound-four "$subst" \
  '( i_5 < 3 )' \
  '( i_5 < 4 )'
make_variant reversed-subtraction "$subst" \
  'minus(name_1, name_2)' \
  'minus(name_2, name_1)'
make_variant extra-result-write "$subst" \
  'i_5 = 0;' \
  'i_5 = 0; result_4 = 7;'
make_variant extra-array-write "$subst" \
  'current_6 = nondet_0[i_5];' \
  'nondet_0[0] = 1; current_6 = nondet_0[i_5];'
make_variant missing-third-join "$subst" \
  'pthread_join(t3, 0);' \
  '(void)t3;'
make_variant broken-triangle "$trans" \
  'minus(name_2, name_3)' \
  'minus(name_1, name_2)'
make_variant property-flip "$symm" \
  '== ( 0 -' \
  '!= ( 0 -'

printf 'variant\ttransitivity\tantisymmetry\n' > "$output_dir/summary.tsv"
for source in "$output_dir"/*.c; do
  name=$(basename "$source" .c)
  log="$output_dir/$name.log"
  timeout 3 stdbuf -oL "$deagle_exe" "$source" --32 \
    --refined-pointer-analysis --deagle-nondet-bulk-init \
    > "$log" 2>&1 || true
  transitivity=$(grep 'NATIVE_RELATIONAL_TRANSITIVITY applied=1' \
    "$log" | tail -1 || true)
  antisymmetry=$(grep 'NATIVE_RELATIONAL_COMPARATOR applied=1' \
    "$log" | tail -1 || true)
  printf '%s\t%s\t%s\n' "$name" \
    "${transitivity:-rejected}" "${antisymmetry:-rejected}" \
    >> "$output_dir/summary.tsv"
done
