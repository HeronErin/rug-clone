#!/bin/bash

# Copyright © 2016–2018 University of Malta

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved. This file is offered as-is,
# without any warranty.

if [[ $(uname) == MINGW* ]]; then
    work_dir="$(cmd /c cd)"
    cache_dir="$work_dir\\cache"
else
    work_dir="$PWD"
    cache_dir="$work_dir/cache"
fi

printf '%s*- mode: compilation; default-directory: "%s" -*-\n' - "$work_dir"
printf 'Compilation started at %s\n\n' "$(date)"

function check_error {
    code="$?"
    if [ "$code" == "0" ]; then
        return
    fi
    printf '\nCompilation exited abnormally with code %s at %s\n' \
        "$code" "$(date)"
    exit "$code"
}

for word in "$@"; do
    arr=(X${word}X)
    count=${#arr[*]}
    if [ $count != 1 ]; then
        printf 'Expected single parameter, got "%s"\n' "$word"
        (exit 2)
        check_error
    fi
done

export GMP_MPFR_SYS_CACHE="$cache_dir"

if [ -e cache ]; then
    rm -r cache
fi
if [ -e target ]; then
    rm -r target
fi

suffix=""
if [[ "$1" == "-"* ]]; then
    suffix="$1"
    shift
fi

if [ $# == 0 ]; then
    toolchains=(beta stable nightly 1.18.0)
else
    toolchains=("$@")
fi

function print_eval_check {
    printf '$'
    printf ' %q' "$@"
    printf '\n'
    eval $(printf '%q ' "$@") 2>&1
    check_error
}

function tc {
    if [ "$1" != "" ]; then
        echo +$1$suffix
    fi
}

# Cache all C libraries.
print_eval_check \
    cargo $(tc "${toolchains[0]}") \
    check \
    --no-default-features --features gmp-mpfr-sys/mpc,gmp-mpfr-sys/ctest \
    -p gmp-mpfr-sys -p rug

# For all toolchains, check with default features and serde.
for toolchain in "${toolchains[@]}"; do
    if [ "$toolchain" != "1.18.0" ]; then
        all_targets="--all-targets"
    else
        all_targets=""
    fi
    print_eval_check \
        cargo $(tc "$toolchain") \
        check $all_targets \
        --features serde \
        -p gmp-mpfr-sys -p rug
done

# For first toolchain, check with all feature combinations.
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
    if [ "${toolchains[0]}" != "1.18.0" ]; then
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
        cargo $(tc "${toolchains[0]}") \
        check $all_targets \
        --no-default-features --features "$features" \
        $gmp -p rug
done

rm -r target

# For all toolchains (including first), test with default features and serde
for toolchain in "${toolchains[@]}"; do
    for build in "" --release; do
        print_eval_check \
            cargo $(tc "$toolchain") \
            test $build \
            --features serde \
            -p gmp-mpfr-sys -p rug
        rm -r target
    done
done

# copy C libraries to targets before clearing cache
for toolchain in "${toolchains[@]}"; do
    print_eval_check cargo $(tc "$toolchain") check -p gmp-mpfr-sys
    print_eval_check cargo $(tc "$toolchain") check --release -p gmp-mpfr-sys
done

rm -r cache

printf '\nCompilation finished at %s\n' "$(date)"
