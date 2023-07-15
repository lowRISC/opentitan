# Copyright (c) 2022 ETH Zurich and University of Bologna
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
#

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_ram_binary")
load("//rules:exclude_files.bzl", "exclude_files")
load("//rules:linker.bzl", "ld_library")
load(
    "//rules:opentitan_test.bzl",
    "manual_test",
    "opentitan_functest",
)
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

<<<<<<<< HEAD:sw/tests/opentitan/flash_aes_smoketest/BUILD
opentitan_functest(
    name = "flash_aes_smoketest",
    srcs = ["flash_aes_smoketest.c"],
    deps = [
        "//hw/ip/aes:model",
========
opentitan_ram_binary(
    name = "sram_spi_host_test",
    srcs = [
    	"sram_spi_host_test.c",
    ],
    hdrs = [
        "sram_spi_host_test.h",
    ],
    archive_symbol_prefix = "sram_spi_host_test",
    testonly = True,
    deps = [
        "//sw/tests/opentitan/common:common",
        "//sw/tests/opentitan/common:linker",
        "//sw/tests/opentitan/common:crt",
       	"//sw/device/silicon_creator/rom:rom_common",
>>>>>>>> 01a67b2fc (Major updates: secure boot, repo organization, automation.):sw/tests/opentitan/sram_spi_host_test/BUILD
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)