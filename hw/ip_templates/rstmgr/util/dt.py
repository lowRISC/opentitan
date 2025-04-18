# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from dtgen.helper import IpHelper, Extension, StructType, ScalarType, ArrayMapType
from topgen.lib import Name
from typing import Optional
from collections import OrderedDict
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
 * @return Reset ID, or `kDtResetUnknown` for invalid parameters.
 */
dt_reset_t dt_rstmgr_sw_reset(dt_rstmgr_t dt, size_t idx);

/**
 * Description of a reset request source.
 *
 * A reset request source is always identified by the instance ID of the module where it comes
 * from. In principle, some instances could have several reset requests. If this is the case,
 * the `rst_req` can be used to distinguish between those. It should be cast to the
 * `dt_<ip>_reset_req_t` type of the corresponding IP.
 *
 * WARNING At the moment, three hardcoded reset requests are treated specially and have their
 * `rst_req` field set to `0` because there is no corresponding reset request declared by those IPs:
 * - the main power glitch reset request, coming from the `pwrmgr`,
 * - the escalation reset request, coming from the `alert_handler`,
 * - the non-debug-module reset request, coming from the `rv_dm`.
 */
%(reset_req_src_struct)s

/**
 * Get the number of hardware reset requests.
 *
 * @param dt Instance of rstmgr.
 * @return Number of reset requests.
 */
size_t dt_rstmgr_hw_reset_req_src_count(dt_rstmgr_t dt);

/**
 * Get the description of a reset request.
 *
 * The reset requests are ordered as they appear in the registers.
 *
 * @param dt Instance of rstmgr.
 * @param idx Index of the reset request source, between 0 and
 *            `dt_pwrmgr_hw_reset_req_src_count(dt)-1`.
 * @return Description of the reset.
 */
dt_rstmgr_reset_req_src_t dt_rstmgr_hw_reset_req_src(dt_rstmgr_t dt, size_t idx);
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
    RSTREQ_SOURCE_STRUCT_NAME = Name.from_snake_case("dt_rstmgr_reset_req_src")
    RSTREQ_SOURCE_INST_FIELD_NAME = Name(["inst", "id"])
    RSTREQ_SOURCE_REQ_FIELD_NAME = Name(["reset", "req"])

    SW_RESETS_FIELD_NAME = Name(["sw", "rst"])
    HW_REQS_FIELD_NAME = Name(["hw", "req"])

    def __init__(self, ip_helper: IpHelper):
        self.ip_helper = ip_helper
        if self.ip_helper.ipconfig is None:
            raise RuntimeError("the rstmgr extension requires the ipconfig to be provided")
        self.ipconfig = IpConfig(self.ip_helper.ipconfig)

        # Create a type to represent a reset request.
        self.reset_req_src_struct = StructType(self.RSTREQ_SOURCE_STRUCT_NAME)
        self.reset_req_src_struct.add_field(
            name = self.RSTREQ_SOURCE_INST_FIELD_NAME,
            field_type = ScalarType(self.ip_helper.top_helper.DT_INSTANCE_ID_NAME),
            docstring = "Instance ID of the source of this reset request.",
        )
        self.reset_req_src_struct.add_field(
            name = self.RSTREQ_SOURCE_REQ_FIELD_NAME,
            field_type = ScalarType("size_t"),
            docstring = "Index of the reset request signal for that instance.",
        )

    def create_ext(ip_helper: IpHelper):
        if ip_helper.ip.name == "rstmgr":
            return RstmgrExt(ip_helper)

    def extend_dt_ip(self) -> Optional[StructType]:
        sw_rsts_count = len(self.ipconfig.sw_rsts_list())
        hw_reqs_count = len(self.ipconfig.hw_reset_req_list())

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
        # Add field to list HW reset requests.
        st.add_field(
            name = self.HW_REQS_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = self.reset_req_src_struct,
                index_type = ScalarType("size_t"),
                length = str(hw_reqs_count),
            ),
            docstring = "List of hardware reset requests, in the order of the register fields",
        )
        return st

    def fill_dt_ip(self, m) -> dict:
        sw_rsts = {}
        self._extra_includes = OrderedDict()
        for (idx, rst) in enumerate(self.ipconfig.sw_rsts_list()):
            sw_rsts[str(idx)] = Name.from_snake_case(rst)
        hw_reqs = {}
        for (idx, reset) in enumerate(self.ipconfig.hw_reset_req_list()):
            # NOTE Englishbreakfast pretends to have an escalation signal but
            # in fact does not have an alert_handler so we need to special case
            # that. Similarly there is no rv_dm.
            if self.ip_helper.top_helper.top["name"] == "englishbreakfast" and \
                    reset["module"] in ["alert_handler", "rv_dm"]:
                inst_id = Name(["unknown"])
            else:
                inst_id = Name.from_snake_case(reset["module"])
            # Even though the ipconfig currently models internal and debug reset
            # requests like peripherals, they are in reality hardcoded signals and
            # therefore there is not correspondingly named reset requests coming from
            # those blocks. For now, simply hardwire those to 0 to workaround the issue.
            if reset["name"] not in ["Ndm", "MainPwr", "Esc"] and inst_id != Name(["unknown"]):
                module_type = self.ip_helper.top_helper.get_module_type(reset["module"])
                self._extra_includes[module_type] = None
                rstreq = Name(["dt"])
                rstreq += Name.from_snake_case(module_type)
                rstreq += Name(["reset", "req"])
                rstreq += Name.from_snake_case(
                    self.ip_helper.simplify_reset_request_name(reset["name"]))
                rstreq = rstreq.as_c_enum()
            else:
                rstreq = "0"
            hw_reqs[str(idx)] = {
                self.RSTREQ_SOURCE_INST_FIELD_NAME: inst_id,
                self.RSTREQ_SOURCE_REQ_FIELD_NAME: rstreq,
            }

        return {
            self.SW_RESETS_FIELD_NAME: sw_rsts,
            self.HW_REQS_FIELD_NAME: hw_reqs,
        }

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        if pos == Extension.DtIpPos.HeaderEnd:
            subs = {
                'reset_req_src_struct': self.reset_req_src_struct.render_type_def(),
            }
            return HEADER_EXT_TEMPLATE % subs
        elif pos == Extension.DtIpPos.SourceIncludes:
            includes = ""
            for ip in self._extra_includes:
                includes += f"#include \"dt_{ip}.h\"\n"
            return includes
        elif pos == Extension.DtIpPos.SourceEnd:
            subs = {
                'sw_reset_count': len(self.ipconfig.sw_rsts_list()),
            }
            return SOURCE_EXT_TEMPLATE % subs
        else:
            return ""
