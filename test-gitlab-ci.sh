#!/bin/bash

# Copyright © 2016–2019 University of Malta

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved. This file is offered as-is,
# without any warranty.

function print_eval_check {
    printf '$'
    for word in "$@"; do
        if [[ "$word" != *\ * ]]; then
            printf ' %q' "$word"
        elif [[ "$word" =~ ^[\ /0-9A-Z_a-z-]*$ ]]; then
            printf ' "%s"' "$word"
        else
            printf ' %q' "$word"
        fi
    done
    printf '\n'
    eval $(printf '%q ' "$@")
    code="$?"
    if [ "$code" == "0" ]; then
        return
    fi
    printf '\nCommand exited abnormally with code %s\n' "$code"
    exit "$code"
}

print_eval_check \
    rustup install "$TOOLCHAIN"
# For beta, install rustfmt and clippy too
if [[ "$TOOLCHAIN" == beta* ]]; then
    print_eval_check \
        rustup component add --toolchain "$TOOLCHAIN" rustfmt clippy
fi

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
        all_targets=""
    else
        all_targets="--all-targets"
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
        cargo "+$TOOLCHAIN" \
        fmt -- --check
    print_eval_check \
        cargo "+$TOOLCHAIN" \
        clippy --all-targets \
        --features "fail-on-warnings serde"
fi
