#!/bin/bash

# Copyright © 2016–2018 University of Malta

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License and a copy of the GNU General Public License along with this
# program. If not, see <http://www.gnu.org/licenses/>.

set -e

for word in "$@"; do
    arr=(X${word}X)
    count=${#arr[*]}
    if [ $count != 1 ]; then
        printf 'Expected single parameter, got "%s"\n' "$word"
        exit 1
    fi
done

if [[ $(uname) == MINGW* ]]; then
    export GMP_MPFR_SYS_CACHE="$(cmd /c cd)\\cache"
else
    export GMP_MPFR_SYS_CACHE="$(pwd)/cache"
fi

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
    toolchains=(stable beta nightly 1.18.0)
else
    toolchains=("$@")
fi

function print_eval {
    printf '$'
    printf ' %q' "$@"
    printf '\n'
    eval $(printf '%q ' "$@")
}

function tc {
    if [ "$1" != "" ]; then
        echo +$1$suffix
    fi
}

# Cache all C libraries.
print_eval \
    cargo $(tc "${toolchains[0]}") \
    check \
    --no-default-features --features gmp-mpfr-sys/mpc,gmp-mpfr-sys/ctest \
    -p gmp-mpfr-sys -p rug

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
    if [[ "$features" =~ ^(()|serde)$ ]]; then
        gmp=""
    else
        gmp="-p gmp-mpfr-sys"
    fi
    print_eval \
        cargo $(tc "${toolchains[0]}") \
        check --all-targets \
        --no-default-features --features "$features" \
        $gmp -p rug
done

rm -r target

# For all toolchains (including first), test with default features and serde
for toolchain in "${toolchains[@]}"; do
    for build in "" --release; do
        print_eval \
            cargo $(tc "$toolchain") \
            test $build \
            --features serde \
            -p gmp-mpfr-sys -p rug
        rm -r target
    done
done

# copy C libraries to targets before clearing cache
for toolchain in "${toolchains[@]}"; do
    print_eval cargo $(tc "$toolchain") check -p gmp-mpfr-sys
    print_eval cargo $(tc "$toolchain") check --release -p gmp-mpfr-sys
done

if [ -e cache ]; then
    rm -r cache
fi
