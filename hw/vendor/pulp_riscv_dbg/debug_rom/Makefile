# See LICENSE.SiFive for license details

debug_rom = debug_rom.sv

GCC?=riscv64-unknown-elf-gcc
OBJCOPY?=riscv64-unknown-elf-objcopy
OBJDUMP?=riscv64-unknown-elf-objdump
PYTHON?=python

all: $(debug_rom)

%.sv: %.img
	$(PYTHON) gen_rom.py $<

%.img: %.bin
	dd if=$< of=$@ bs=256 count=1

%.bin: %.elf
	$(OBJCOPY) -O binary $< $@

%.elf: %.S link.ld
	$(GCC) -I$(RISCV)/include -Tlink.ld $< -nostdlib -fPIC -static -Wl,--no-gc-sections -o $@

%.dump: %.elf
	$(OBJDUMP) -d $< --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data  > $@

clean:
	rm -f *.img *.dump *.bin *.sv
