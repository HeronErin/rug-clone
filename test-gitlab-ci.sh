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

function print_eval_check {
    printf '$'
    printf ' %q' "$@"
    printf '\n'
    eval $(printf '%q ' "$@") 2>&1
    check_error
}

print_eval_check \
    rustup install "$TOOLCHAIN"

# Check with all feature combinations.
# integer,rational = rational
# integer,rand = rand
# float,complex = complex
for features in \
    '' gmp-mpfr-sys{,/mpfr,/mpc} \
    integer{,\ float,\ complex}{,\ serde} \
    rational{,\ float,\ complex}{,\ rand}{,\ serde} \
    float{,\ rand}{,\ serde} \
    complex{,\ rand}{,\ serde} \
    rand{,\ serde} \
    serde
do
    if [[ "$TOOLCHAIN" == 1.18.0* ]]; then
        all_targets="--all-targets"
    else
        all_targets=""
    fi
    if [[ "$features" =~ ^(()|serde)$ ]]; then
        gmp=""
    else
        gmp="-p gmp-mpfr-sys"
    fi
    features="fail-on-warnings${features:+ $features}"
    print_eval_check \
        cargo "+$TOOLCHAIN" \
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
        --features "fail-on-warnings serde" \
        -p gmp-mpfr-sys -p rug
done

# For beta, check rustfmt and clippy too
if [[ "$TOOLCHAIN" == beta* ]]; then
    print_eval_check \
        rustup component add rustfmt --toolchain "$TOOLCHAIN"
    print_eval_check \
        cargo "+$TOOLCHAIN" \
        fmt -- --check
    print_eval_check \
        rustup component add clippy --toolchain "$TOOLCHAIN"
    print_eval_check \
        cargo "+$TOOLCHAIN" \
        clippy --release --all-targets \
        --features="fail-on-warnings serde"
fi
