# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from dtgen.helper import IpHelper, Extension, StructType, ScalarType, ArrayMapType
from topgen.lib import Name
from typing import Optional
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from ipconfig import IpConfig  # noqa: E402

HEADER_EXT_TEMPLATE = """
/**
 * Get the number of software resets.
 *
 * @param dt Instance of rstmgr.
 * @return Number of software resets.
 */
size_t dt_rstmgr_sw_reset_count(dt_rstmgr_t dt);

/**
 * Get the reset ID of a software reset.
 *
 * The resets are ordered in the same way as they appear in the registers.
 *
 * @param dt Instance of rstmgr.
 * @param idx Index of the software reset, between 0 and `dt_rstmgr_sw_reset_count(dt)-1`.
 * @return Reset ID.
 */
dt_reset_t dt_rstmgr_sw_reset(dt_rstmgr_t dt, size_t idx);

"""

SOURCE_EXT_TEMPLATE = """
size_t dt_rstmgr_sw_reset_count(dt_rstmgr_t dt) {
  return %(sw_reset_count)d;
}

dt_reset_t dt_rstmgr_sw_reset(dt_rstmgr_t dt, size_t idx) {
  if (idx >= %(sw_reset_count)d) {
    return kDtResetUnknown;
  }
  return TRY_GET_DT(dt, kDtResetUnknown)->ext.sw_rst[idx];
}
"""


class RstmgrExt(Extension):
    SW_RESETS_FIELD_NAME = Name(["sw", "rst"])

    def __init__(self, ip_helper: IpHelper):
        self.ip_helper = ip_helper
        if self.ip_helper.ipconfig is None:
            raise RuntimeError("the rstmgr extension requires the ipconfig to be provided")
        self.ipconfig = IpConfig(self.ip_helper.ipconfig)

    def create_ext(ip_helper: IpHelper):
        if ip_helper.ip.name == "rstmgr":
            return RstmgrExt(ip_helper)

    def extend_dt_ip(self) -> Optional[StructType]:
        sw_rsts_count = len(self.ipconfig.sw_rsts_list())

        st = StructType()
        # Add field to list SW resets.
        st.add_field(
            name = self.SW_RESETS_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = ScalarType(self.ip_helper.top_helper.DT_RESET_ENUM_NAME),
                index_type = ScalarType("size_t"),
                length = str(sw_rsts_count),
            ),
            docstring = "List of software resets, in the order of the register fields",
        )
        return st

    def fill_dt_ip(self, m) -> Optional[dict]:
        sw_rsts = {}
        for (idx, rst) in enumerate(self.ipconfig.sw_rsts_list()):
            sw_rsts[str(idx)] = Name.from_snake_case(rst)

        return {
            self.SW_RESETS_FIELD_NAME: sw_rsts,
        }

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        if pos == Extension.DtIpPos.HeaderEnd:
            return HEADER_EXT_TEMPLATE
        elif pos == Extension.DtIpPos.SourceEnd:
            subs = {
                'sw_reset_count': len(self.ipconfig.sw_rsts_list()),
            }
            return SOURCE_EXT_TEMPLATE % subs
        else:
            return ""
