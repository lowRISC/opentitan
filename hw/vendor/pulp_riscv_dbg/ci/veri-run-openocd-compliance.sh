#!/usr/bin/env bash

set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if [ -z "${RISCV}" ]
then
    echo "RISCV is empty"
    exit 1
fi


veri_out=$(mktemp)
openocd_out=openocd.log

make -C "${ROOT}"/tb veri-run |& tee "${veri_out}"&
# record veri pid/pgid to kill it if it survives this script
veri_pid=$!
veri_pgid=$(ps -o pgid= ${veri_pid} | grep -o [0-9]*)

# block until we get "Listening on port" so that we are safe to connect openocd
coproc grep -m 1 "Listening on port"
tail -f -n0 "${veri_out}" --pid "$COPROC_PID" >&"${COPROC[1]}"

echo "Starting openocd"
"${RISCV}"/bin/openocd -f "${ROOT}"/tb/dm_compliance_test.cfg |& tee "${openocd_out}"

if grep -q "ALL TESTS PASSED" "${openocd_out}"; then
    exit 0
fi
exit 1

