#!/bin/sh

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
shopt -s globstar

SUFFIX=.original

if [ -e target ]; then
    mv target coverage_save_target
fi

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
s/ - /: /               # make lines friendly with emacs compilation mode
/hits: 0/p              # print zero coverage-lines immediately
H                       # hold everything
${x;p}                  # at the end of the file, print the hold
'
(
    printf '%s*- mode: compilation; default-directory: "%s" -*-\n' - "$PWD"
    printf 'Compilation started at %s\n\n' "$(date)"
    cargo tarpaulin -v --features serde --ignore-tests |&
        sed -n -e "$FILTER_SCRIPT"
    printf '\nCompilation finished at %s\n' "$(date)\n"
) > coverage.report

# restore original sources
for f in src/**/*.rs$SUFFIX; do
    mv "$f" "${f%$SUFFIX}"
done

if [ -e target ]; then
    rm -r target
fi
if [ -e coverage_save_target ]; then
    mv coverage_save_target target
fi
