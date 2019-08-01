#!/bin/bash

# Copyright © 2016–2019 University of Malta

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved. This file is offered as-is,
# without any warranty.

set -e
shopt -s globstar

if [ -e target ]; then
    mv target coverage_save_target
fi

## first extract docs
etc/extract-doc-tests.sh

## generate coverage.report

(
    printf '%s*- mode: compilation; default-directory: "%s" -*-\n' - "$PWD"
    printf 'Compilation started at %s\n\n' "$(date)"
    etc/invoke-tarpaulin.sh
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
