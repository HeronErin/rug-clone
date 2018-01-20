#!/bin/sh

shopt -s globstar

# first extract docs

FIND='/```rust$/,/```$/'
UNCOMMENT='s, *//[/!],       ,'
BLOCK='s/    ```rust$/\{/;s/    ```/\}/'
UNCRATE='/extern crate/d'
UNRUG='s/rug:://'
UNMAIN='s,fn main(),/* fn main() */,'
UNHASH='s/# //'
SCRIPT="$FIND"'{'"$UNCOMMENT;$BLOCK;$UNCRATE;$UNRUG;$UNMAIN;$UNHASH;p;"'}'
for f in src/**/*.rs; do
	sed -n -e "$SCRIPT" < "$f" > "$f.tmp_doc"
	echo '// AUTOEXTRACTED DOCTESTS BELOW' >> "$f"
	echo '#[test] fn check_doctests() {' >> "$f"
	cat "$f.tmp_doc" >> "$f"
	echo '}' >> "$f"
	rm "$f.tmp_doc"
done

# generate coverage.report

cargo tarpaulin -v --features serde >& coverage_all.report
sed -i -e 's/ - /: /' coverage_all.report
echo '-*- mode: compilation -*-' > coverage.report
echo >> coverage.report
grep 'hits: 0' coverage_all.report >> coverage.report
cat coverage_all.report >> coverage.report
rm coverage_all.report

# remove extracted docs

for f in src/**/*.rs; do
	sed -i -e '/AUTOEXTRACTED DOCTESTS BELOW/,$d' "$f"
done
