#!/bin/bash

set -e

if [ -e target/doc ]; then
	rm -r target/doc
fi
export GMP_MPFR_SYS_CDOC=$PWD/target/doc
# use nightly to support cargo:rerun-if-env-changed
cargo +nightly doc -p gmp-mpfr-sys -p rug
# clear variable so that next gen.sh run reruns doc generation
unset GMP_MPFR_SYS_CDOC
cargo +nightly check -p gmp-mpfr-sys
rustdoc +nightly doc-src/index.md --markdown-no-toc --output target/doc \
	--markdown-css normalize.css \
	--markdown-css rustdoc.css \
	--markdown-css main.css \
	--html-before-content doc-src/before-content.html \
	--html-after-content doc-src/after-content.html
if [ -e public ]; then
	rm -r public
fi
mv target/doc public
for l in gmp mpfr mpc; do
	L=$(echo $l | tr '[a-z]' '[A-Z]')
	for f in public/$l/*.html; do
		sed -i.rm~ \
		    's/..\/dir\/index.html\|dir.html#Top/..\/index.html/g' "$f"
		sed -i.rm~ -e '/<body/r doc-src/before-content-c.html' "$f"
		sed -n -i.rm~ -e '/<\/body>/r doc-src/after-content.html' \
		    -e 1x -e '2,${x;p}' -e '${x;p}' "$f"
		sed -i.rm~ 's,\(class="crate\)\(">'$L'</a>\),\1 current\2,' "$f"
		if [ $(basename $f) != index.html ]; then
			sed -i.rm~ 's,\(class="location">\)\(</p\),\1<a href="index.html">'$L'</a>\2,' "$f"
		fi
	done
done
find public -name \*.html -o -name \*.js | while read f; do
	sed -i.rm~ 's/doc.rust-lang.org\/nightly/doc.rust-lang.org/g' "$f"
done
find public -name \*.rm~ -delete
