# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Code providing types specific to generation'''

from typing import Dict

# Some common types.
# This represents a configuration typically from a hjson file.
ConfigT = Dict[str, object]
# This represents a parameter list used for ipgen. It is identical to
# ConfigT. Perhaps typing.NewType can disambiguate?
ParamsT = Dict[str, object]
