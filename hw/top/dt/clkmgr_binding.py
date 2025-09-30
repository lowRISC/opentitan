# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from dtgen.helper import indent_text, IpHelper, Extension, StructType, ScalarType, ArrayMapType
from topgen.lib import Name
from typing import Dict, Optional
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from clkmgr_ipconfig import ClkmgrIpConfig  # noqa: E402

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

/**
 * Description of a measurable clock.
 *
 */
%(measurable_clk_struct)s

/**
 * Get the number of measurable clocks.
 *
 * @param dt Instance of clkmgr.
 * @return Number of measurable clocks.
 */
size_t dt_clkmgr_measurable_clock_count(dt_clkmgr_t dt);

/**
 * Get the description of a measurable clock.
 *
 * @param dt Instance of clkmgr.
 * @param idx Index of the measurable clock, between 0 and
 *            `dt_clkmgr_measurable_clock_count(dt)-1`.
 * @return Description of the measurable clock.
 */
%(measurable_clk_struct_name)s dt_clkmgr_measurable_clock(dt_clkmgr_t dt, size_t idx);
"""

SOURCE_EXT_TEMPLATE = """
size_t dt_clkmgr_gateable_clock_count(dt_clkmgr_t dt) {
  return %(sw_clk_count)d;
}

dt_instance_id_t dt_clkmgr_gateable_clock(dt_clkmgr_t dt, size_t idx) {
  return TRY_GET_DT(dt, kDtInstanceIdUnknown)->clkmgr_ext.sw_clks[idx];
}

size_t dt_clkmgr_hintable_clock_count(dt_clkmgr_t dt) {
  return %(hint_clk_count)d;
}

dt_instance_id_t dt_clkmgr_hintable_clock(dt_clkmgr_t dt, size_t idx) {
  return TRY_GET_DT(dt, kDtInstanceIdUnknown)->clkmgr_ext.hint_clks[idx];
}

size_t dt_clkmgr_measurable_clock_count(dt_clkmgr_t dt) {
  return %(measurable_clk_count)d;
}

%(measurable_clk_struct_name)s dt_clkmgr_measurable_clock(dt_clkmgr_t dt, size_t idx) {
  %(measurable_clk_struct_name)s invalid_clk = %(invalid_measure_clk)s;
  return TRY_GET_DT(dt, invalid_clk)->clkmgr_ext.measurable_clks[idx];
}
"""


class ClkmgrExt(Extension):
    SW_CLOCKS_FIELD_NAME = Name(["sw", "clks"])
    HINT_CLOCKS_FIELD_NAME = Name(["hint", "clks"])
    MEASURABLE_CLOCKS_FIELD_NAME = Name(["measurable", "clks"])

    MEASURABLE_CLOCK_STRUCT_NAME = Name.from_snake_case("dt_clkmgr_measurable_clk")
    MEASURABLE_CLOCK_STRUCT_CLK_FIELD_NAME = Name(["clock"])
    MEASURABLE_CLOCK_STRUCT_CTRL_EN_OFF_FIELD_NAME = Name(["meas", "ctrl", "en", "off"])
    MEASURABLE_CLOCK_STRUCT_CTRL_EN_EN_OFF_FIELD_NAME = \
        Name(["meas", "ctrl", "en", "en", "field"])
    MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_FIELD_NAME = Name(["meas", "ctrl", "shadowed", "off"])
    MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_LO_FIELD_NAME = \
        Name(["meas", "ctrl", "shadowed", "lo", "field"])
    MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_HI_FIELD_NAME = \
        Name(["meas", "ctrl", "shadowed", "hi", "field"])

    def __init__(self, ip_helper: IpHelper):
        self.ip_helper = ip_helper
        if self.ip_helper.ipconfig is None:
            raise RuntimeError("the clkmgr extension requires the ipconfig to be provided")
        self.ipconfig = ClkmgrIpConfig(self.ip_helper.ipconfig)

        # Create a type to represent a measurable clock.
        self.measurable_clk_struct = StructType(self.MEASURABLE_CLOCK_STRUCT_NAME)
        self.measurable_clk_struct.add_field(
            name = self.MEASURABLE_CLOCK_STRUCT_CLK_FIELD_NAME,
            field_type = ScalarType(self.ip_helper.top_helper.DT_CLOCK_ENUM_NAME),
            docstring = "Clock",
        )
        self.measurable_clk_struct.add_field(
            name = self.MEASURABLE_CLOCK_STRUCT_CTRL_EN_OFF_FIELD_NAME,
            field_type = ScalarType("uint32_t"),
            docstring = "MEAS_CTRL_EN register offset",
        )
        self.measurable_clk_struct.add_field(
            name = self.MEASURABLE_CLOCK_STRUCT_CTRL_EN_EN_OFF_FIELD_NAME,
            field_type = ScalarType("bitfield_field32_t"),
            docstring = "MEAS_CTRL_EN_EN bitfield",
        )
        self.measurable_clk_struct.add_field(
            name = self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_FIELD_NAME,
            field_type = ScalarType("uint32_t"),
            docstring = "CTRL_SHADOWED register offset",
        )
        self.measurable_clk_struct.add_field(
            name = self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_LO_FIELD_NAME,
            field_type = ScalarType("bitfield_field32_t"),
            docstring = "CTRL_SHADOWED_LO bitfield",
        )
        self.measurable_clk_struct.add_field(
            name = self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_HI_FIELD_NAME,
            field_type = ScalarType("bitfield_field32_t"),
            docstring = "CTRL_SHADOWED_HI bitfield",
        )

        # For an invalid clock, use an invalid clock ID, empty bitfields and
        # invalid offsets.
        empty_bitfield = "((bitfield_field32_t) { .mask = 0, .index = 0 })"
        self.invalid_clk = {
            self.MEASURABLE_CLOCK_STRUCT_CLK_FIELD_NAME: Name(["count"]),
            self.MEASURABLE_CLOCK_STRUCT_CTRL_EN_OFF_FIELD_NAME: "0xdead",
            self.MEASURABLE_CLOCK_STRUCT_CTRL_EN_EN_OFF_FIELD_NAME: empty_bitfield,
            self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_FIELD_NAME: "0xdead",
            self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_LO_FIELD_NAME: empty_bitfield,
            self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_HI_FIELD_NAME: empty_bitfield,
        }

    @staticmethod
    def create_ext(ip_helper: IpHelper) -> Optional["Extension"]:
        if ip_helper.ip.name == "clkmgr":
            return ClkmgrExt(ip_helper)

    def extend_dt_ip(self) -> tuple[Name, StructType]:
        sw_clk_count = len(self.ipconfig.sw_clks())
        hint_clk_count = len(self.ipconfig.hint_clks())
        measurable_clk_count = len(self.ipconfig.measurable_clks())
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
        # Add field to list measurable clocks.
        st.add_field(
            name = self.MEASURABLE_CLOCKS_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = self.measurable_clk_struct,
                index_type = ScalarType("size_t"),
                length = str(measurable_clk_count),
            ),
            docstring = "List of measurables clocks",
        )
        return Name(["clkmgr_ext"]), st

    def fill_dt_ip(self, m) -> Dict:
        sw_clks = {}
        for (idx, clk) in enumerate(self.ipconfig.sw_clks()):
            sw_clks[str(idx)] = Name.from_snake_case(clk["module"])
        hint_clks = {}
        for (idx, clk) in enumerate(self.ipconfig.hint_clks()):
            hint_clks[str(idx)] = Name.from_snake_case(clk["module"])
        measurable_clks = {}
        for (idx, clk) in enumerate(self.ipconfig.measurable_clks()):
            reg_prefix = "CLKMGR_{}_MEAS_CTRL_".format(clk.upper())
            measurable_clks[str(idx)] = {
                self.MEASURABLE_CLOCK_STRUCT_CLK_FIELD_NAME: Name.from_snake_case(clk),
                self.MEASURABLE_CLOCK_STRUCT_CTRL_EN_OFF_FIELD_NAME:
                    reg_prefix + "EN_REG_OFFSET",
                self.MEASURABLE_CLOCK_STRUCT_CTRL_EN_EN_OFF_FIELD_NAME:
                    reg_prefix + "EN_EN_FIELD",
                self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_FIELD_NAME:
                    reg_prefix + "SHADOWED_REG_OFFSET",
                self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_LO_FIELD_NAME:
                    reg_prefix + "SHADOWED_LO_FIELD",
                self.MEASURABLE_CLOCK_CTRL_SHADOWED_OFF_HI_FIELD_NAME:
                    reg_prefix + "SHADOWED_HI_FIELD",
            }

        return {
            self.SW_CLOCKS_FIELD_NAME: sw_clks,
            self.HINT_CLOCKS_FIELD_NAME: hint_clks,
            self.MEASURABLE_CLOCKS_FIELD_NAME: measurable_clks,
        }

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        sw_clk_count = len(self.ipconfig.sw_clks())
        hint_clk_count = len(self.ipconfig.hint_clks())
        measurable_clk_count = len(self.ipconfig.measurable_clks())

        if pos == Extension.DtIpPos.HeaderEnd:
            subs = {
                'measurable_clk_struct': self.measurable_clk_struct.render_type_def(),
                'measurable_clk_struct_name': self.MEASURABLE_CLOCK_STRUCT_NAME.as_c_type(),
            }
            return HEADER_EXT_TEMPLATE % subs
        elif pos == Extension.DtIpPos.SourceEnd:
            subs = {
                'sw_clk_count': sw_clk_count,
                'hint_clk_count': hint_clk_count,
                'measurable_clk_count': measurable_clk_count,
                'invalid_measure_clk':
                    indent_text(self.measurable_clk_struct.render_value(self.invalid_clk), "  "),
                'measurable_clk_struct_name': self.MEASURABLE_CLOCK_STRUCT_NAME.as_c_type(),
            }
            return SOURCE_EXT_TEMPLATE % subs
        elif pos == Extension.DtIpPos.SourceIncludes:
            return '#include "hw/top/clkmgr_regs.h"'
        elif pos == Extension.DtIpPos.HeaderIncludes:
            return '#include "sw/device/lib/base/bitfield.h"'
        else:
            return ""
