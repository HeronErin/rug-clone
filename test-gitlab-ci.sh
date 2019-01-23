#!/bin/bash

# Copyright © 2016–2018 University of Malta

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved. This file is offered as-is,
# without any warranty.

function check_error {
    code="$?"
    if [ "$code" == "0" ]; then
        return
    fi
    printf '\nCompilation exited abnormally with code %s at %s\n' \
        "$code" "$(date)"
    exit "$code"
}

TOOLCHAIN="$1"

function print_eval_check {
    printf '$'
    printf ' %q' "$@"
    printf '\n'
    eval $(printf '%q ' "$@") 2>&1
    check_error
}

if [ "$TOOLCHAIN" != "1.18.0" ]; then
    all_targets="--all-targets"
else
    all_targets=""
fi
print_eval_check \
    cargo "+$TOOLCHAIN" \
    check $all_targets \
    --features serde \
    -p gmp-mpfr-sys -p rug

# Check with all feature combinations.
# integer,rational = rational
# integer,rand = rand
# float,complex = complex
for features in \
    '' gmp-mpfr-sys{,/mpfr,/mpc} \
    integer{,\,float,\,complex}{,\,serde} \
    rational{,\,float,\,complex}{,\,rand}{,\,serde} \
    float{,\,rand}{,\,serde} \
    complex{,\,rand}{,\,serde} \
    rand{,\,serde} \
    serde
do
    if [ "$TOOLCHAIN" != "1.18.0" ]; then
        all_targets="--all-targets"
    else
        all_targets=""
    fi
    if [[ "$features" =~ ^(()|serde)$ ]]; then
        gmp=""
    else
        gmp="-p gmp-mpfr-sys"
    fi
    print_eval_check \
        cargo "+$TOOLCHAIN"
        check $all_targets \
        --no-default-features --features "$features" \
        $gmp -p rug
done

rm -r target

# Test with default features and serde
for build in "" --release; do
    print_eval_check \
        cargo "+$TOOLCHAIN" \
        test $build \
        --features serde \
        -p gmp-mpfr-sys -p rug
    rm -r target
done
