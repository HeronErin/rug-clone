#!/bin/sh

shopt -s globstar
SUFFIX=.original

# first extract docs
EXTRACT_SCRIPT='
p                       # print original, as sed is called quiet
/```rust$/,/```$/{      # work between ```rust and ```
    s, *//[/!],       ,     # uncomment lines
    s, *$,,                 # remove trailing spaces
    s,^\( *\)# ,\1/* # */ , # comment hiding hash
    s,    ```rust$,{,       # replace ```rust with {
    s,extern crate.*,// &,  # comment lines containing extern crate
    s, rug::, /*& */ ,      # comment rug::
    s, ::rug, /*& */ ,      # comment ::rug
    s,fn main(),/* & */,    # comment fn main()
    s,    ```,},            # replace ``` with }
    H                       # append to hold
}
${                      # at the end of the file
    x                       # move the hold to pattern space
    /./{                    # if hold was not empty
        s/^.//                  # remove leading newline
        i\
// AUTOEXTRACTED DOCTESTS BELOW
        i\
#[test]
        i\
fn check_doctests() {
        p                       # print the hold (wrapped by fn)
        i\
}
    }
}'
sed -i$SUFFIX -n -e "$EXTRACT_SCRIPT" src/**/*.rs

# generate coverage.report
FILTER_SCRIPT='
1i\
-*- mode: compilation; default-directory: "'"$PWD"'"-*-\

s/ - /: /               # make lines friendly with emacs compilation mode
/hits: 0/p              # print zero coverage-lines immediately
H                       # hold everything
${x;p}                  # at the end of the file, print the hold
'
cargo tarpaulin -v --features serde --ignore-tests |&
    sed -n -e "$FILTER_SCRIPT" > coverage.report

# restore original sources
for f in src/**/*.rs$SUFFIX; do
    mv "$f" "${f%$SUFFIX}"
done
