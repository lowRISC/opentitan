# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from dtgen.helper import indent_text, IpHelper, Extension, StructType, ScalarType, ArrayMapType
from topgen.lib import CEnum, Name
from typing import Dict, Optional
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from ipconfig import OtpCtrlIpConfig  # noqa: E402

HEADER_EXT_TEMPLATE = """
/**
 * Description of an OTP partition.
 *
 */
%(otp_partition_info_struct)s

/**
 * SW readable OTP partition identifier.
 */
%(otp_partition_ids_enum)s

/**
 * Get a SW readable OTP partition information.
 *
 * @param dt Instance of otp_ctrl.
 * @param partition OTP partition identifier.
 * @return OTP partition information.
 */
%(otp_partition_info_struct_name)s
dt_otp_ctrl_sw_readable_partition(dt_otp_ctrl_t dt, %(otp_partition_ids_enum_name)s partition);
"""

SOURCE_EXT_TEMPLATE = """

%(otp_partition_info_struct_name)s
dt_otp_ctrl_sw_readable_partition(dt_otp_ctrl_t dt, %(otp_partition_ids_enum_name)s partition) {
  %(otp_partition_info_struct_name)s invalid_part = %(invalid_partition)s;
  return TRY_GET_DT(dt, invalid_part)->sw_readable_partitions.info[partition];
}

"""


class OtpCtrlExt(Extension):
    OTP_PARTITION_INFO_FIELD_NAME = Name(["info"])

    OTP_PARTITION_INFO_STRUCT_START_ADDR_FIELD_NAME = Name(["start", "addr"])
    OTP_PARTITION_INFO_STRUCT_SIZE_FIELD_NAME = Name(["size"])
    OTP_PARTITION_INFO_STRUCT_DIGEST_ADDR_FIELD_NAME = Name(["digest", "reg", "offset"])
    OTP_PARTITION_INFO_STRUCT_ALIGN_MASK_FIELD_NAME = Name(["align", "mask"])
    OTP_PARTITION_INFO_STRUCT_NAME = Name.from_snake_case("dt_otp_partition_info")

    def __init__(self, ip_helper: IpHelper):
        if ip_helper.ipconfig is None:
            raise RuntimeError("the OTP controller extension requires the ipconfig to be provided")

        self._otp_partition_ids_prefix = Name(["Otp", "Partition"])
        self._ipconfig = OtpCtrlIpConfig(ip_helper.ipconfig, self._otp_partition_ids_prefix)
        self._otp_partition_ids = CEnum(top_name = None, name = self._otp_partition_ids_prefix)
        for partition in self._ipconfig.sw_readable_partitions():
            self._otp_partition_ids.add_constant(partition["name"])
        self._otp_partition_ids.add_count_constant()

        # An OTP partition information structure
        self._otp_partition_info_struct = StructType(self.OTP_PARTITION_INFO_STRUCT_NAME)
        self._otp_partition_info_struct.add_field(
            name = self.OTP_PARTITION_INFO_STRUCT_START_ADDR_FIELD_NAME,
            field_type = ScalarType("uint32_t"),
            docstring = "The absolute OTP address at which this partition starts",
        )
        self._otp_partition_info_struct.add_field(
            name = self.OTP_PARTITION_INFO_STRUCT_SIZE_FIELD_NAME,
            field_type = ScalarType("size_t"),
            docstring = "Size (in bytes) of the partition, excluding the digest field",
        )
        self._otp_partition_info_struct.add_field(
            name = self.OTP_PARTITION_INFO_STRUCT_DIGEST_ADDR_FIELD_NAME,
            field_type = ScalarType("uint32_t"),
            docstring = "The OTP digest CSR (where the digest is buffered) offset for " +
            "this partition.",
        )
        self._otp_partition_info_struct.add_field(
            name = self.OTP_PARTITION_INFO_STRUCT_ALIGN_MASK_FIELD_NAME,
            field_type = ScalarType("uint32_t"),
            docstring = "The alignment mask for this partition",
        )

        self._invalid_partition_info = {
            self.OTP_PARTITION_INFO_STRUCT_START_ADDR_FIELD_NAME: "0xdeadbeef",
            self.OTP_PARTITION_INFO_STRUCT_SIZE_FIELD_NAME: "0x0",
            self.OTP_PARTITION_INFO_STRUCT_DIGEST_ADDR_FIELD_NAME: "0xdeadbeef",
            self.OTP_PARTITION_INFO_STRUCT_ALIGN_MASK_FIELD_NAME: "0x0",
        }

    @staticmethod
    def create_ext(ip_helper: IpHelper) -> Optional["Extension"]:
        if ip_helper.ip.name == "otp_ctrl":
            return OtpCtrlExt(ip_helper)

    def extend_dt_ip(self) -> tuple[Name, StructType]:
        partition_count = len(self._ipconfig.sw_readable_partitions())
        st = StructType()
        # Add field to list measurable clocks.
        st.add_field(
            name = self.OTP_PARTITION_INFO_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = self._otp_partition_info_struct,
                index_type = ScalarType("size_t"),
                length = str(partition_count),
            ),
            docstring = "List of SW readable OTP partitions",
        )
        return Name(["sw_readable_partitions"]), st

    def fill_dt_ip(self, m) -> Dict:
        otp_partitions = {}
        for partition in self._ipconfig.sw_readable_partitions():
            part_prefix = "OTP_CTRL_" + partition["name"].as_c_define() + "_"
            part_param_prefix = "OTP_CTRL_PARAM_" + partition["name"].as_c_define() + "_"

            for (id, value, _) in self._otp_partition_ids.constants:
                if id == partition["id"]:
                    otp_partitions[id.as_c_enum()] = {
                        self.OTP_PARTITION_INFO_STRUCT_START_ADDR_FIELD_NAME:
                            part_param_prefix + "OFFSET",
                        self.OTP_PARTITION_INFO_STRUCT_SIZE_FIELD_NAME:
                            part_param_prefix + "SIZE - " + part_param_prefix + "DIGEST_SIZE",
                        self.OTP_PARTITION_INFO_STRUCT_DIGEST_ADDR_FIELD_NAME:
                            part_prefix + "DIGEST_0_REG_OFFSET",
                        self.OTP_PARTITION_INFO_STRUCT_ALIGN_MASK_FIELD_NAME: "0x3",
                    }

        return {
            self.OTP_PARTITION_INFO_FIELD_NAME: otp_partitions,
        }

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        if pos == Extension.DtIpPos.HeaderEnd:
            subs = {
                'otp_partition_info_struct': self._otp_partition_info_struct.render_type_def(),
                'otp_partition_info_struct_name': self._otp_partition_info_struct.as_c_type(),
                'otp_partition_ids_enum': self._otp_partition_ids.render(),
                'otp_partition_ids_enum_name': self._otp_partition_ids.name.as_c_type(),
            }
            return HEADER_EXT_TEMPLATE % subs
        elif pos == Extension.DtIpPos.SourceIncludes:
            return '#include "hw/top/otp_ctrl_regs.h"'
        elif pos == Extension.DtIpPos.SourceEnd:
            subs = {
                'otp_partition_info_struct_name': self._otp_partition_info_struct.as_c_type(),
                'otp_partition_ids_enum_name': self._otp_partition_ids.name.as_c_type(),
                'invalid_partition':
                    indent_text(self._otp_partition_info_struct.
                                render_value(self._invalid_partition_info), " "),
            }
            return SOURCE_EXT_TEMPLATE % subs
        else:
            return ""
