#!/bin/bash

function usage {
    echo
    echo "this script must be called from the root directory of the coq dev"
    echo "it uses patchmake.sh which uses sponge (debian package: moreutils)."
    echo
}

for i in $*; do
    case $i in
	"-h")
	    usage; exit 0 ;;
	*)
	;;
    esac
done



${COQBIN}coq_makefile -f _CoqProject -o Makefile

# Getting the directory containing the current script, where we should
# also find patchmake.sh.
resourcedir=${0%/*}

$resourcedir/patchmake.sh Makefile
