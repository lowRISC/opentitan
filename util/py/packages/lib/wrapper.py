# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


class Wrapper:
    """A thin wrapper that allows replacing an already referenced object.

    This allows updating a global after it has been imported by other modules.
    """

    def __init__(self):
        self._wrapped_value = None

    def replace_wrapped(self, v_new):
        self._wrapped_value = v_new

    def __getattr__(self, name):
        if self._wrapped_value is None:
            raise RuntimeError("Wrapped value is not initialized yet")
        return getattr(self._wrapped_value, name)
