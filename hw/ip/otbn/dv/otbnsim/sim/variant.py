# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.variant import Extension, Variant  # type: ignore

RV32IXotbn = Variant("RV32IXotbn", custext=[Extension(
    name="Xotbn", description="OpenTitan BigNum Extension", implies=["Zicsr"])])
