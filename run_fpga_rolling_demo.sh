#!/bin/sh

if [[ ! -v OT_FPGA_UART ]]; then
  echo "\$OT_FPGA_UART must be set to FPGA UART"
  exit 1
fi

export RISCV_TARGET=opentitan
export RISCV_DEVICE=rv32imc
export OT_TARGET=fpga
export OT_FPGA_UART_BAUD=115200

while :
do
  echo "Running Coremark..."
  ./run_earlgrey_bin.py --bin_file ./build-bin/sw/device/fpga/benchmarks/coremark/coremark.bin --fpga_uart $OT_FPGA_UART --baud_rate $OT_FPGA_UART_BAUD --log --log_level DEBUG

  echo "Running RISC-V Compliance Suite..."
  ./riscv-compliance-logo.sh
  pushd ./sw/vendor/riscv_compliance > /dev/null
  make --quiet RISCV_ISA=rv32i
  popd > /dev/null

  echo "Running Embench Suite..."
  ./embench-logo.sh
  pushd ./sw/vendor/embench-iot > /dev/null
  ./run_benchmark.sh
  popd > /dev/null
done

