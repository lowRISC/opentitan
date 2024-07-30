include $(PULP_SDK_HOME)/install/rules/pulp.mk

dump_header:
	riscv32-unknown-elf-objcopy -R .l1cluster_g -R .bss_l1 --pad-to 0x0 -O binary $(TARGET_BUILD_DIR)/$(PULP_APP)/$(PULP_APP) cluster.bin
	../../common_pulp/elf_to_header.py --binary=$(TARGET_BUILD_DIR)/$(PULP_APP)/$(PULP_APP) --vectors=../cluster_code.h

override disopt += -hDzts

