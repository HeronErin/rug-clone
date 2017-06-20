#!/bin/bash

set -e

if [[ $(uname) == MINGW* ]]; then
	export GMP_MPFR_SYS_CACHE="$(cmd /c cd)\\cache"
else
	export GMP_MPFR_SYS_CACHE="$(pwd)/cache"
fi

if [ -e cache ]; then
	rm -r cache
fi

suffix=""
if [[ "$1" == "-"* ]]; then
	suffix="$1"
	shift
fi

if [ $# == 0 ]; then
	toolchains=(stable beta nightly 1.17.0 1.16.0 1.15.1)
else
	toolchains=("$@")
fi

function print_eval {
	printf '$'
	printf ' %q' "$@"
	printf '\n'
	eval $(printf '%q ' "$@")
}

# For first toolchain and suffix, test without rational, float,
# complex too. The default feature is complex, so no need to test it
# here. First test the feature mpc so that we cache all C libraries.
for features in gmp-mpfr-sys/mpc "" gmp-mpfr-sys/mpfr rational float; do
	if [ -e target ]; then
		rm -r target
	fi
	for build in --release ""; do
		print_eval cargo +${toolchains[0]}"$suffix" test $build \
			   --no-default-features --features "$features" \
			   -p gmp-mpfr-sys -p rug
		rm -r target
	done
done

for toolchain in "${toolchains[@]}"; do
	if [ -e target ]; then
		rm -r target
	fi
	for build in "" --release; do
		print_eval cargo +$toolchain"$suffix" test $build \
			   -p gmp-mpfr-sys -p rug
		rm -r target
	done
done

# copy C libraries to some targets before clearing cache
cargo +stable"$suffix" check -p gmp-mpfr-sys
cargo +stable"$suffix" check --release -p gmp-mpfr-sys
cargo +nightly"$suffix" check -p gmp-mpfr-sys
cargo +nightly"$suffix" check --release -p gmp-mpfr-sys

rm -r cache
