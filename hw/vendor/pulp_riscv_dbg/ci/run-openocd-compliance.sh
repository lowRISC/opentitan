#!/usr/bin/env bash

set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if [ -z "${RISCV}" ]
then
    echo "RISCV is empty"
    exit 1
fi

function cleanup {
  echo "cleaning up processes and tmp files"
  sleep 2
  echo "vsim pid is:${vsim_pid} pgid:${vsim_pgid}"
  if ps -p "${vsim_pid}" > /dev/null
  then
      echo "vsim pid exists, killing it"
      kill -- -"${vsim_pgid}"
  fi
  rm "${vsim_out}"
}

trap cleanup EXIT

vsim_out=$(mktemp)
openocd_out=openocd.log

make -C "${ROOT}"/tb/dm vsim-run &> "${vsim_out}"&
# record vsim pid/pgid to kill it if it survives this script
vsim_pid=$!
vsim_pgid=$(ps -o pgid= ${vsim_pid} | grep -o [0-9]*)

# block until we get "Listening on port" so that we are safe to connect openocd
coproc grep -m 1 "Listening on port"
tail -f -n0 "${vsim_out}" --pid "$COPROC_PID" >&"${COPROC[1]}"

echo "Starting openocd"
"${RISCV}"/bin/openocd -f "${ROOT}"/tb/dm/dm_compliance_test.cfg |& tee "${openocd_out}"


if grep -q "ALL TESTS PASSED" "${openocd_out}"; then
    exit 0
fi
exit 1

