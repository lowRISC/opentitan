# See LICENSE.SiFive for license details

debug_rom = debug_rom.sv debug_rom_one_scratch.sv

GCC?=riscv64-unknown-elf-gcc
OBJCOPY?=riscv64-unknown-elf-objcopy
OBJDUMP?=riscv64-unknown-elf-objdump
PYTHON?=python3

# The CHERIoT park loop is assembled with the CHERIoT LLVM toolchain rather than a RISC-V GCC, so
# it is deliberately not part of the "all" target.
cheriot_debug_rom = debug_rom_cheriot.sv debug_rom_cheriot.dump

CHERIOT_LLVM_ROOT?=/opt/cheriot-llvm/bin
CHERIOT_CXX?=$(CHERIOT_LLVM_ROOT)/clang++
CHERIOT_OBJCOPY?=$(CHERIOT_LLVM_ROOT)/llvm-objcopy
CHERIOT_OBJDUMP?=$(CHERIOT_LLVM_ROOT)/llvm-objdump
CHERIOT_LD?=$(CHERIOT_LLVM_ROOT)/ld.lld
CHERIOT_TARGET_FLAGS?=-target riscv32-unknown-unknown -mcpu=cheriot -mabi=cheriot \
                      -mxcheri-rvc -mrelax -fshort-wchar -nostdinc

all: $(debug_rom)

cheriot: $(cheriot_debug_rom)

.PHONY: all cheriot clean

%.sv: %.img
	$(PYTHON) gen_rom.py $<

%.img: %.bin
	dd if=$< of=$@ bs=256 count=1

%.bin: %.elf
	$(OBJCOPY) -O binary $< $@

%.elf: $(findstring debug_rom, $(debug_rom)).S link.ld
	$(GCC) $(if  $(findstring one_scratch,$@),,-DSND_SCRATCH=1) -I$(RISCV)/include -Tlink.ld $< -nostdlib -fPIC -static -Wl,--no-gc-sections -o $@

%.dump: %.elf
	$(OBJDUMP) -d $< --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data  > $@

# Explicit rules for the CHERIoT ROM. make prefers these over the pattern rules above, which would
# otherwise use the RISC-V toolchain.
debug_rom_cheriot.o: debug_rom_cheriot.S
	$(CHERIOT_CXX) -c $(CHERIOT_TARGET_FLAGS) -DSND_SCRATCH=1 $< -nostdlib -fPIC -static -o $@

debug_rom_cheriot.elf: debug_rom_cheriot.o link_cheriot.ld
	$(CHERIOT_LD) --script=link_cheriot.ld --relax -o $@ $<

debug_rom_cheriot.bin: debug_rom_cheriot.elf
	$(CHERIOT_OBJCOPY) -O binary $< $@

debug_rom_cheriot.dump: debug_rom_cheriot.elf
	$(CHERIOT_OBJDUMP) -d $< --disassemble-all --disassemble-zeroes --section=.text > $@

clean:
	rm -f *.img *.dump *.bin *.o *.elf *.sv
