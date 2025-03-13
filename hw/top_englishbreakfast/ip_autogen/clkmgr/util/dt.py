# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from dtgen.helper import IpHelper, Extension, StructType, ScalarType, ArrayMapType
from topgen.lib import Name
from typing import Dict
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from ipconfig import ClkmgrIpConfig  # noqa: E402

HEADER_EXT_TEMPLATE = """
/**
 * Get the number of software gateable clocks.
 *
 * @param dt Instance of clkmgr.
 * @return Number of gateable clocks.
 */
size_t dt_clkmgr_gateable_clock_count(dt_clkmgr_t dt);

/**
 * Get the instance ID of a gateable clock.
 *
 * The clocks are ordered as they appear in the registers.
 *
 * @param dt Instance of clkmgr.
 * @param idx Index of the gateable clock, between 0 and `dt_clkmgr_sw_clock_count(dt)-1`.
 * @return Instance ID of the device whose clock is gateable.
 */
dt_instance_id_t dt_clkmgr_gateable_clock(dt_clkmgr_t dt, size_t idx);

/**
 * Get the number of software hintable clocks.
 *
 * @param dt Instance of clkmgr.
 * @return Number of hintable clocks.
 */
size_t dt_clkmgr_hintable_clock_count(dt_clkmgr_t dt);

/**
 * Get the instance ID of a hintable clock.
 *
 * The clocks sources are ordered as they appear in the registers.
 *
 * @param dt Instance of clkmgr.
 * @param idx Index of the hintable clock, between 0 and `dt_clkmgr_hint_clock_count(dt)-1`.
 * @return Instance ID of the device whose clock is hintable.
 */
dt_instance_id_t dt_clkmgr_hintable_clock(dt_clkmgr_t dt, size_t idx);
"""

SOURCE_EXT_TEMPLATE = """
size_t dt_clkmgr_gateable_clock_count(dt_clkmgr_t dt) {
  return %(sw_clk_count)d;
}

dt_instance_id_t dt_clkmgr_gateable_clock(dt_clkmgr_t dt, size_t idx) {
  return TRY_GET_DT(dt, kDtInstanceIdUnknown)->ext.sw_clks[idx];
}

size_t dt_clkmgr_hintable_clock_count(dt_clkmgr_t dt) {
  return %(hint_clk_count)d;
}

dt_instance_id_t dt_clkmgr_hintable_clock(dt_clkmgr_t dt, size_t idx) {
  return TRY_GET_DT(dt, kDtInstanceIdUnknown)->ext.hint_clks[idx];
}
"""


class ClkmgrExt(Extension):
    SW_CLOCKS_FIELD_NAME = Name(["sw", "clks"])
    HINT_CLOCKS_FIELD_NAME = Name(["hint", "clks"])

    def __init__(self, ip_helper: IpHelper):
        self.ip_helper = ip_helper
        if self.ip_helper.ipconfig is None:
            raise RuntimeError("the clkmgr extension requires the ipconfig to be provided")
        self.ipconfig = ClkmgrIpConfig(self.ip_helper.ipconfig)

    @staticmethod
    def create_ext(ip_helper: IpHelper):
        if ip_helper.ip.name == "clkmgr":
            return ClkmgrExt(ip_helper)

    def extend_dt_ip(self) -> StructType:
        sw_clk_count = len(self.ipconfig.sw_clks())
        hint_clk_count = len(self.ipconfig.hint_clks())
        instance_id_enum = self.ip_helper.top_helper.instance_id_enum

        st = StructType()
        # Add field to list gateable clocks.
        st.add_field(
            name = self.SW_CLOCKS_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = ScalarType(instance_id_enum.name),
                index_type = ScalarType("size_t"),
                length = str(sw_clk_count),
            ),
            docstring = "List of gateable clocks, in the order of the register fields",
        )
        # Add field to list hintable clocks.
        st.add_field(
            name = self.HINT_CLOCKS_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = ScalarType(instance_id_enum.name),
                index_type = ScalarType("size_t"),
                length = str(hint_clk_count),
            ),
            docstring = "List of hintable clocks, in the order of the register fields",
        )
        return st

    def fill_dt_ip(self, m) -> Dict:
        sw_clks = {}
        for (idx, clk) in enumerate(self.ipconfig.sw_clks()):
            sw_clks[str(idx)] = Name.from_snake_case(clk["module"])
        hint_clks = {}
        for (idx, clk) in enumerate(self.ipconfig.hint_clks()):
            hint_clks[str(idx)] = Name.from_snake_case(clk["module"])

        return {
            self.SW_CLOCKS_FIELD_NAME: sw_clks,
            self.HINT_CLOCKS_FIELD_NAME: hint_clks,
        }

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        sw_clk_count = len(self.ipconfig.sw_clks())
        hint_clk_count = len(self.ipconfig.hint_clks())

        if pos == Extension.DtIpPos.HeaderEnd:
            return HEADER_EXT_TEMPLATE
        elif pos == Extension.DtIpPos.SourceEnd:
            subs = {
                'sw_clk_count': sw_clk_count,
                'hint_clk_count': hint_clk_count,
            }
            return SOURCE_EXT_TEMPLATE % subs
        else:
            return ""
