all: help

.PHONY: help
help:
	@echo "This is a short hand for running popular tasks."
	@echo "Please check the documentation on how to get started"
	@echo "or how to set-up the different environments."

# Use a parallel run (make -j N) for a faster build
build-all: build-riscv-compliance build-simple-system build-arty \
      build-csr-test


# RISC-V compliance
.PHONY: build-riscv-compliance
build-riscv-compliance:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_riscv_compliance


# Simple system
# Use the following targets:
# - "build-simple-system"
# - "run-simple-system"
.PHONY: build-simple-system
build-simple-system:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_simple_system

simple-system-program = examples/sw/simple_system/hello_test/hello_test.vmem
sw-simple-hello: $(simple-system-program)

.PHONY: $(simple-system-program)
$(simple-system-program):
	cd examples/sw/simple_system/hello_test && $(MAKE)

Vibex_simple_system = \
      build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system
$(Vibex_simple_system):
	@echo "$@ not found"
	@echo "Run \"make build-simple-system\" to create the dependency"
	@false

run-simple-system: sw-simple-hello | $(Vibex_simple_system)
	build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system \
		--raminit=$(simple-system-program)


# Arty A7 100T
# Use the following targets:
# - "build-arty"
# - "program-arty"
arty-sw-program = examples/sw/led/led.vmem
sw-led: $(arty-sw-program)

.PHONY: $(arty-sw-program)
$(arty-sw-program):
	cd examples/sw/led && $(MAKE)

build-arty: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7_100

.PHONY: program-arty
program-arty:
	fusesoc --cores-root=. pgm lowrisc:ibex:top_artya7_100


# Lint check
.PHONY: lint-core-tracing
lint-core-tracing:
	fusesoc --cores-root . run --target=lint lowrisc:ibex:ibex_core_tracing


# CS Registers testbench
# Use the following targets:
# - "build-csr-test"
# - "run-csr-test"
.PHONY: build-csr-test
build-csr-test:
	fusesoc --cores-root=. run --target=sim --setup --build \
	      --tool=verilator lowrisc:ibex:tb_cs_registers
Vtb_cs_registers = \
      build/lowrisc_ibex_tb_cs_registers_0/sim-verilator/Vtb_cs_registers
$(Vtb_cs_registers):
	@echo "$@ not found"
	@echo "Run \"make build-csr-test\" to create the dependency"
	@false

.PHONY: run-csr-test
run-csr-test: | $(Vtb_cs_registers)
	fusesoc --cores-root=. run --target=sim --run \
	      --tool=verilator lowrisc:ibex:tb_cs_registers
