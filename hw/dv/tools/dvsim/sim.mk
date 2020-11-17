# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.DEFAULT_GOAL := all

LOCK_TOOL_SRCS_DIR ?= flock --timeout 3600 ${tool_srcs_dir} --command
LOCK_SW_BUILD ?= flock --timeout 3600 ${sw_build_dir} --command

all: build run

###############################
## sim build and run targets ##
###############################
build: compile_result

prep_tool_srcs:
	@echo "[make]: prep_tool_srcs"
	mkdir -p ${tool_srcs_dir}
	${LOCK_TOOL_SRCS_DIR} "cp -Ru ${tool_srcs} ${tool_srcs_dir}/."

pre_compile: prep_tool_srcs
	@echo "[make]: pre_compile"
	mkdir -p ${build_dir}

gen_sv_flist: pre_compile
	@echo "[make]: gen_sv_flist"
	cd ${build_dir} && ${sv_flist_gen_cmd} ${sv_flist_gen_opts}

compile: gen_sv_flist
	@echo "[make]: compile"
	cd ${sv_flist_gen_dir} && ${build_cmd} ${build_opts}

post_compile: compile
	@echo "[make]: post_compile"

compile_result: post_compile
	@echo "[make]: compile_result"

run: run_result

pre_run: prep_tool_srcs
	@echo "[make]: pre_run"
	mkdir -p ${run_dir}
ifneq (${sw_test},)
	mkdir -p ${sw_build_dir}
endif

sw_build: pre_run
	@echo "[make]: sw_build"
ifneq (${sw_test},)
	# Initialize meson build system.
	${LOCK_SW_BUILD} "cd ${proj_root} && \
		BUILD_ROOT=${sw_build_dir} ${proj_root}/meson_init.sh"
	# Compile boot rom code and generate the image.
	${LOCK_SW_BUILD} "ninja -C ${sw_build_dir}/build-out \
		sw/device/boot_rom/boot_rom_export_${sw_build_device}"
	# Extract the boot rom logs.
	${proj_root}/util/device_sw_utils/extract_sw_logs.py \
		-e "${sw_build_dir}/build-out/sw/device/boot_rom/boot_rom_${sw_build_device}.elf" \
		-f .logs.fields -r .rodata .chip_info \
		-n "rom" -o "${run_dir}"
	# Copy over the boot rom image to the run_dir.
	cp ${sw_build_dir}/build-out/sw/device/boot_rom/boot_rom_${sw_build_device}.32.vmem \
		${run_dir}/rom.vmem
	cp ${sw_build_dir}/build-out/sw/device/boot_rom/boot_rom_${sw_build_device}.elf \
		${run_dir}/rom.elf

ifeq (${sw_test_is_prebuilt},1)
	# Copy over the sw test image and related sources to the run_dir.
	cp ${proj_root}/${sw_test}.64.vmem ${run_dir}/sw.vmem
	# Optionally, assume that ${sw_test}_logs.txt exists and copy over to the run_dir.
	# Ignore copy error if it actually doesn't exist. Likewise for ${sw_test}_rodata.txt.
	-cp ${proj_root}/${sw_test}_logs.txt ${run_dir}/sw_logs.txt
	-cp ${proj_root}/${sw_test}_rodata.txt ${run_dir}/sw_rodata.txt

else
	# Compile the sw test code and generate the image.
	${LOCK_SW_BUILD} "ninja -C ${sw_build_dir}/build-out \
		${sw_test}_export_${sw_build_device}"
	# Convert sw image to frame format
	# TODO only needed for loading sw image through SPI. Can enhance this later
	${LOCK_SW_BUILD} "ninja -C ${sw_build_dir}/build-out sw/host/spiflash/spiflash_export"
	${LOCK_SW_BUILD} "${sw_build_dir}/build-bin/sw/host/spiflash/spiflash --input \
		${sw_build_dir}/build-bin/${sw_test}_${sw_build_device}.bin \
		--dump-frames=${run_dir}/sw.frames.bin"
	${LOCK_SW_BUILD} "srec_cat ${run_dir}/sw.frames.bin --binary \
		--offset 0x0 --byte-swap 4 --fill 0xff -within ${run_dir}/sw.frames.bin -binary -range-pad 4 \
		--output ${run_dir}/sw.frames.vmem --vmem"
	# Extract the sw test logs.
	${proj_root}/util/device_sw_utils/extract_sw_logs.py \
		-e "${sw_build_dir}/build-out/${sw_test}_${sw_build_device}.elf" \
		-f .logs.fields -r .rodata \
		-n "sw" -o "${run_dir}"
	# Copy over the sw test image to the run_dir.
	cp ${sw_build_dir}/build-out/${sw_test}_${sw_build_device}.64.vmem ${run_dir}/sw.vmem
	cp ${sw_build_dir}/build-out/${sw_test}_${sw_build_device}.elf ${run_dir}/sw.elf
endif

endif


simulate: sw_build
	@echo "[make]: simulate"
	cd ${run_dir} && ${run_cmd} ${run_opts}

post_run: simulate
	@echo "[make]: post_run"

run_result: post_run
	@echo "[make]: run_result"

#######################
## Load waves target ##
#######################
debug_waves:
	${debug_waves_cmd} ${debug_waves_opts}

############################
## coverage rated targets ##
############################
# Merge coverage if there are multiple builds.
cov_merge:
	@echo "[make]: cov_merge"
	${cov_merge_cmd} ${cov_merge_opts}

# Open coverage tool to review and create report or exclusion file.
cov_analyze: prep_tool_srcs
	@echo "[make]: cov_analyze"
	${cov_analyze_cmd} ${cov_analyze_opts}

# Generate coverage reports.
cov_report:
	@echo "[make]: cov_report"
	${cov_report_cmd} ${cov_report_opts}

.PHONY: build \
	run \
	reg \
	pre_compile \
	compile \
	post_compile \
	compile_result \
	pre_run \
	simulate \
	post_run \
	run_result
