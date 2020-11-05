IBEX_CONFIG ?= small

FUSESOC_CONFIG_OPTS = $(shell ./util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)

all: help

.PHONY: help
help:
	@echo "This is a short hand for running popular tasks."
	@echo "Please check the documentation on how to get started"
	@echo "or how to set-up the different environments."

# Use a parallel run (make -j N) for a faster build
build-all: build-riscv-compliance build-simple-system build-arty-100 \
      build-csr-test


# RISC-V compliance
.PHONY: build-riscv-compliance
build-riscv-compliance:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_riscv_compliance \
		$(FUSESOC_CONFIG_OPTS)


# Simple system
# Use the following targets:
# - "build-simple-system"
# - "run-simple-system"
.PHONY: build-simple-system
build-simple-system:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_simple_system \
		$(FUSESOC_CONFIG_OPTS)

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


# Arty A7 FPGA example
# Use the following targets (depending on your hardware):
# - "build-arty-35"
# - "build-arty-100"
# - "program-arty"
arty-sw-program = examples/sw/led/led.vmem
sw-led: $(arty-sw-program)

.PHONY: $(arty-sw-program)
$(arty-sw-program):
	cd examples/sw/led && $(MAKE)

.PHONY: build-arty-35
build-arty-35: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7 --part xc7a35ticsg324-1L

.PHONY: build-arty-100
build-arty-100: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1

.PHONY: program-arty
program-arty:
	fusesoc --cores-root=. run --target=synth --run \
		lowrisc:ibex:top_artya7


# Lint check
.PHONY: lint-core-tracing
lint-core-tracing:
	fusesoc --cores-root . run --target=lint lowrisc:ibex:ibex_core_tracing \
		$(FUSESOC_CONFIG_OPTS)


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

# Echo the parameters passed to fusesoc for the chosen IBEX_CONFIG
.PHONY: test-cfg
test-cfg:
	@echo $(FUSESOC_CONFIG_OPTS)

.PHONY: python-lint
python-lint:
	$(MAKE) -C util lint
