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

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_rom_binary")
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

ld_library(
    name = "linker",
    script = "link.ld",
    testonly = True,
)

cc_library(
    name = "common",
    srcs = [
    	"utils.h",
        "utils.c",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    alwayslink = True,
)

cc_library(
    name = "crt",
    srcs = [
        "crt0.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    alwayslink = True,
)