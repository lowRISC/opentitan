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
from ipconfig import PwrmgrIpConfig  # noqa: E402

HEADER_EXT_TEMPLATE = """
/**
 * Description of a wakeup source.
 *
 * A wakeup source is always identified by the instance ID of the module where it comes from.
 * Some instances can have several wakeup signals, e.g. the pinmux has two (`pin` and `usb`).
 * For such IPs, it is not sufficient to know the instance, we also need to know which
 * signal triggered the wakeup. The `wakeup` index can be used to distinguish between those.
 * This value should be casted to the `dt_<ip>_wakeup_t` type of the corresponding IP.
 * For example, if the `pwrmgr` has two `pinmux` wakeup sources as described above, it's
 * two wakeup sources will be described as follows:
 * ```c
 * {.inst_id = kDtInstanceIdPinmux, .wakeup = kDtPinmuxWakeupPinWkupReq}, // for `pin`
 * {.inst_id = kDtInstanceIdPinmux, .wakeup = kDtPinmuxWakeupUsbWkupReq}, // for `usb`
 * ```
 */
%(wakeup_src_struct)s

/**
 * Get the number of wakeup sources.
 *
 * @param dt Instance of pwrmgr.
 * @return Number of wakeup sources.
 */
size_t dt_pwrmgr_wakeup_src_count(dt_pwrmgr_t dt);

/**
 * Get the description of a wakeup source.
 *
 * The wakeup sources are ordered as they appear in the registers.
 *
 * @param dt Instance of pwrmgr.
 * @param idx Index of the wakeup source, between 0 and `dt_pwrmgr_wakeup_src_count(dt)-1`.
 * @return Description of the source.
 */
dt_pwrmgr_wakeup_src_t dt_pwrmgr_wakeup_src(dt_pwrmgr_t dt, size_t idx);

/**
 * Description of a reset request source.
 *
 * A reset request source is always identified by the instance ID of the module where it comes
 * from. In principle, some instances could have several reset requests. If this is the case,
 * the `rst_req` can be used to distinguish between those. It should be cast to the
 * `dt_<ip>_reset_req_t` type of the corresponding IP.
 */
%(reset_req_src_struct)s

/**
 * Get the number of peripheral reset requests.
 *
 * @param dt Instance of pwrmgr.
 * @return Number of reset requests.
 */
size_t dt_pwrmgr_reset_request_src_count(dt_pwrmgr_t dt);

/**
 * Get the description of a reset request.
 *
 * The reset requests are ordered as they appear in the registers.
 *
 * @param dt Instance of pwrmgr.
 * @param idx Index of the reset request source, between 0 and
 *            `dt_pwrmgr_reset_request_src_count(dt)-1`.
 * @return Description of the reset.
 */
dt_pwrmgr_reset_req_src_t dt_pwrmgr_reset_request_src(dt_pwrmgr_t dt, size_t idx);
"""

SOURCE_EXT_TEMPLATE = """
size_t dt_pwrmgr_wakeup_src_count(dt_pwrmgr_t dt) {
  return %(wakeup_src_count)d;
}

dt_pwrmgr_wakeup_src_t dt_pwrmgr_wakeup_src(dt_pwrmgr_t dt, size_t idx) {
  dt_pwrmgr_wakeup_src_t invalid = {.inst_id = kDtInstanceIdUnknown, .wakeup = 0};
  return TRY_GET_DT(dt, invalid)->ext.wakeup_src[idx];
}

size_t dt_pwrmgr_reset_request_src_count(dt_pwrmgr_t dt) {
  return %(reset_reqs_count)d;
}

dt_pwrmgr_reset_req_src_t dt_pwrmgr_reset_request_src(dt_pwrmgr_t dt, size_t idx) {
  dt_pwrmgr_reset_req_src_t invalid = {.inst_id = kDtInstanceIdUnknown, .reset_req = 0};
  return TRY_GET_DT(dt, invalid)->ext.rst_reqs[idx];
}
"""


class PwrmgrExt(Extension):
    WAKEUP_SOURCE_STRUCT_NAME = Name.from_snake_case("dt_pwrmgr_wakeup_src")
    WAKEUP_SOURCE_INST_FIELD_NAME = Name(["inst", "id"])
    WAKEUP_SOURCE_WAKEUP_FIELD_NAME = Name(["wakeup"])
    RSTREQ_SOURCE_STRUCT_NAME = Name.from_snake_case("dt_pwrmgr_reset_req_src")
    RSTREQ_SOURCE_INST_FIELD_NAME = Name(["inst", "id"])
    RSTREQ_SOURCE_REQ_FIELD_NAME = Name(["reset", "req"])
    EXT_WAKEUP_SOURCES_FIELD_NAME = Name(["wakeup", "src"])
    EXT_RESET_REQS_FIELD_NAME = Name(["rst", "reqs"])

    def __init__(self, ip_helper: IpHelper):
        self.ip_helper = ip_helper
        if self.ip_helper.ipconfig is None:
            raise RuntimeError("the pwrmgr extension requires the ipconfig to be provided")
        self.ipconfig = PwrmgrIpConfig(self.ip_helper.ipconfig)

        # Create a type to represent a wakeup.
        self.wakeup_src_struct = StructType(self.WAKEUP_SOURCE_STRUCT_NAME)
        self.wakeup_src_struct.add_field(
            name = self.WAKEUP_SOURCE_INST_FIELD_NAME,
            field_type = ScalarType(self.ip_helper.top_helper.DT_INSTANCE_ID_NAME),
            docstring = "Instance ID of the source of this wakeup.",
        )
        self.wakeup_src_struct.add_field(
            name = self.WAKEUP_SOURCE_WAKEUP_FIELD_NAME,
            field_type = ScalarType("size_t"),
            docstring = "Index of the wakeup signal for that instance.",
        )
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

    @staticmethod
    def create_ext(ip_helper: IpHelper):
        if ip_helper.ip.name == "pwrmgr":
            return PwrmgrExt(ip_helper)

    def extend_dt_ip(self) -> Optional[StructType]:
        wakeup_count = len(self.ipconfig.wakeup_list())
        rstreq_count = len(self.ipconfig.peripheral_reset_req_list())

        st = StructType()
        # Add field to list wakeup sources.
        st.add_field(
            name = self.EXT_WAKEUP_SOURCES_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = self.wakeup_src_struct,
                index_type = ScalarType("size_t"),
                length = str(wakeup_count),
            ),
            docstring = "List of wakeup sources, in the order of the register fields",
        )
        # Add field to list reset requests.
        st.add_field(
            name = self.EXT_RESET_REQS_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = self.reset_req_src_struct,
                index_type = ScalarType("size_t"),
                length = str(rstreq_count),
            ),
            docstring = "List of reset requests, in the order of the register fields",
        )
        return st

    def fill_dt_ip(self, m) -> Optional[dict]:
        wakeup_srcs = {}
        self._extra_includes = OrderedDict()
        for (idx, wakeup) in enumerate(self.ipconfig.wakeup_list()):
            # We need to create the wakeup name from another module.
            module_type = self.ip_helper.top_helper.get_module_type(wakeup["module"])
            self._extra_includes[module_type] = None
            wkup_name = Name(["dt"])
            wkup_name += Name.from_snake_case(module_type)
            wkup_name += Name(["wakeup"])
            wkup_name += Name.from_snake_case(wakeup["name"])
            wakeup_srcs[str(idx)] = {
                self.WAKEUP_SOURCE_INST_FIELD_NAME: Name.from_snake_case(wakeup["module"]),
                self.WAKEUP_SOURCE_WAKEUP_FIELD_NAME: wkup_name.as_c_enum()
            }
        rst_reqs = {}
        for (idx, reset) in enumerate(self.ipconfig.peripheral_reset_req_list()):
            # We need to create the reset name from another module.
            module_type = self.ip_helper.top_helper.get_module_type(reset["module"])
            self._extra_includes[module_type] = None
            rstreq = Name(["dt"])
            rstreq += Name.from_snake_case(module_type)
            rstreq += Name(["reset", "req"])
            rstreq += Name.from_snake_case(
                self.ip_helper.simplify_reset_request_name(reset["name"]))
            rst_reqs[str(idx)] = {
                self.RSTREQ_SOURCE_INST_FIELD_NAME: Name.from_snake_case(reset["module"]),
                self.RSTREQ_SOURCE_REQ_FIELD_NAME: rstreq.as_c_enum()
            }

        return {
            self.EXT_WAKEUP_SOURCES_FIELD_NAME: wakeup_srcs,
            self.EXT_RESET_REQS_FIELD_NAME: rst_reqs,
        }

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        if pos == Extension.DtIpPos.HeaderEnd:
            subs = {
                'wakeup_src_struct': self.wakeup_src_struct.render_type_def(),
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
                'wakeup_src_count': len(self.ipconfig.wakeup_list()),
                'reset_reqs_count': len(self.ipconfig.peripheral_reset_req_list()),
            }
            return SOURCE_EXT_TEMPLATE % subs
        else:
            return ""
