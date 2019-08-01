#!/bin/bash

# Copyright © 2016–2019 University of Malta

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved. This file is offered as-is,
# without any warranty.

set -e
shopt -s globstar

SUFFIX=.original

if [ -e target ]; then
    mv target coverage_save_target
fi

## first extract docs
etc/extract-doc-tests.sh

## generate coverage.report

# This filter script is for tarpaulin 0.6.2:

# FILTER_SCRIPT='
# s/ - /: /               # make lines friendly with emacs compilation mode
# /hits: 0/p              # print zero-coverage lines immediately
# H                       # hold everything
# ${x;p}                  # at the end of the file, print the hold
# '

# This filter script is for tarpaulin 0.6.3:

FILTER_SCRIPT='
# modify uncovered lines list
/Uncovered Lines/,/Tested\/Total Lines:/{
    # make lines friendly with emacs compilation mode
    s/^\(.*\): \(..*\)/\1:\2: Uncovered/
    # if the line contains a comma split it, repeating prefix and suffix
    s/\(^\)\(.*\):\([^,]*\), \(.*: Uncovered\)$/\1\2:\3: Uncovered\n\2:\4/
: repeat
    # like above, but work on last line only
    s/\(.*\n\)\(.*\):\([^,]*\), \(.*: Uncovered\)$/\1\2:\3: Uncovered\n\2:\4/
    # if a line was split, repeat
    t repeat
}
p                       # print the line(s) as sed is invoked with -e
'

(
    printf '%s*- mode: compilation; default-directory: "%s" -*-\n' - "$PWD"
    printf 'Compilation started at %s\n\n' "$(date)"
    cargo tarpaulin -v --features serde --ignore-tests |&
        sed -n -e "$FILTER_SCRIPT"
    printf '\nCompilation finished at %s\n' "$(date)"
) > coverage.report

# restore original sources
etc/extract-doc-tests.sh restore

if [ -e target ]; then
    rm -r target
fi
if [ -e coverage_save_target ]; then
    mv coverage_save_target target
fi
