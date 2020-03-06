#!/bin/bash

set -u
set -e

# This is a simple bash script to allow you to run a binary compiled
# for the simple_system environment using Spike.
#

error() {
    echo >&2 "$@"
    exit 1
}

usage () {
    echo >&2 "Usage:  spike-simple-system [-h] [-v] [-n] [--] [options] <elf>"
    echo >&2
    echo >&2 "  Where <elf> is the path to an ELF binary that was"
    echo >&2 "  compiled for the simple_system environment. Any arguments "
    echo >&2 "  in <options> will be passed to Spike after those to set up "
    echo >&2 "  the environment for simple_system tests."
    echo >&2
    echo >&2 "  If the -v argument is passed, the Spike command will be "
    echo >&2 "  echoed to stderr before it runs. If the -n argument is passed "
    echo >&2 "  (which implies -v), we don't actually run the command."
    echo >&2
    echo >&2 "  This will write the Spike instruction log to stderr."

    exit $1
}

declare -a opts
opts=()

verbose=0
dryrun=0

at_start=1

# We can be rather lazy when building our command line here, and don't
# need to distinguish between [options] and <elf>, since they end up
# appended to the Spike command line in the same order.
while [ $# != 0 ]; do
    if [ $at_start = 1 ]; then
        case "$1" in
            --help|-h)
                usage 0
                ;;

            --verbose|-v)
                verbose=1
                ;;

            --dry-run|-n)
                dryrun=1
                verbose=1
                ;;

            --)
                at_start=0
                ;;

            *)
                at_start=0
                opts=("$1")
                ;;
        esac
    else
        opts+=("$1")
    fi
    shift
done

# If opts is empty, that's definitely an error (since the <elf>
# parameter was compulsory). Moan here.
if [ ${#opts[*]} = 0 ]; then
    usage 1
fi

# Time to figure out how to call the Spike binary. If the user has set
# SPIKE_PATH, we should obey that. Otherwise, we'll just assume that
# they've got their PATH set up sensibly.
if [ x"$SPIKE_PATH" = x ]; then
    spike='spike'
else
    spike="$SPIKE_PATH/spike"
fi

# Here are the Spike options you need to run in a simple_system world.
declare -a ss_opts
ss_opts=(--isa=rv32imc
         --log-commits
         -l
         -m0x10000:0x30000,0x100000:0x100000)

cmd=("$spike" "${ss_opts[@]}" "${opts[@]}")

if [ $verbose = 1 ]; then
    # Echo the command that we're going to run in the same style as
    # 'set -x' would.
    echo >&2 + "${cmd[@]}"
fi

if [ $dryrun = 1 ]; then
    exit 0
fi

exec "${cmd[@]}"
