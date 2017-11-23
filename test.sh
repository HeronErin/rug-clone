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
	toolchains=(stable beta nightly 1.22.1 1.21.0 1.20.0 1.19.0 1.18.0 1.17.0)
else
	toolchains=("$@")
fi

function print_eval {
	printf '$'
	printf ' %q' "$@"
	printf '\n'
	eval $(printf '%q ' "$@")
}

# For first toolchain and suffix, check without rational, float,
# complex too. First check the feature mpc to cache all C libraries.
for features in gmp-mpfr-sys/mpc "" gmp-mpfr-sys gmp-mpfr-sys/mpfr integer rational float complex rand; do
	if [ -e target ]; then
		rm -r target
	fi
	if [ "$features" == "" ]; then
		gmp=""
	else
		gmp="-p gmp-mpfr-sys"
	fi
	for build in --release ""; do
		print_eval cargo +${toolchains[0]}"$suffix" check $build \
			   --no-default-features --features "$features" \
			   $gmp -p rug
		rm -r target
	done
done

# Check with default features and without serde.
for build in --release ""; do
	print_eval cargo +${toolchains[0]}"$suffix" check $build \
		   -p gmp-mpfr-sys -p rug
	rm -r target
done

# For all toolchains (including first), test with default features and serde
for toolchain in "${toolchains[@]}"; do
	if [ -e target ]; then
		rm -r target
	fi
	for build in "" --release; do
		print_eval cargo +$toolchain"$suffix" test $build \
			   --features serde -p gmp-mpfr-sys -p rug
		rm -r target
	done
done

# copy C libraries to some targets before clearing cache
cargo +stable"$suffix" check -p gmp-mpfr-sys
cargo +stable"$suffix" check --release -p gmp-mpfr-sys
cargo +nightly"$suffix" check -p gmp-mpfr-sys
cargo +nightly"$suffix" check --release -p gmp-mpfr-sys

rm -r cache
