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

# Cache all C libraries.
print_eval cargo +${toolchains[0]}"$suffix" check --no-default-features \
	   --features gmp-mpfr-sys/mpc,gmp-mpfr-sys/ctest \
	   -p gmp-mpfr-sys -p rug
rm -r target

# integer,rational = rational
# integer,rand = rand
# float,complex = complex
for features in '' gmp-mpfr-sys{,/mpfr,/mpc} \
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
	print_eval cargo +${toolchains[0]}"$suffix" check \
		   --no-default-features --features "$features" \
		   $gmp -p rug
	rm -r target
done

# For all toolchains (including first), test with default features and serde
for toolchain in "${toolchains[@]}"; do
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
