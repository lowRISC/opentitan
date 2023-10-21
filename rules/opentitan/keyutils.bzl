# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules:opentitan.bzl", "key_allowed_in_lc_state")

def rsa_key_for_lc_state(key_structs, hw_lc_state):
    """Return a dictionary containing a single key that can be used in the given
    LC state. The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.rsa != None and key_allowed_in_lc_state(k.rsa, hw_lc_state))]
    if len(keys) == 0:
        fail("There are no RSA keys compatible with HW LC state {} in key structs".format(hw_lc_state))
    return {
        keys[0].rsa.label: keys[0].rsa.name,
    }

def rsa_key_by_name(key_structs, nickname):
    """Return a dictionary containing a single key that matches the name given.
    The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.rsa != None and k.rsa.name == nickname)]
    if len(keys) == 0:
        fail("There are no RSA keys compatible with name {} in key structs".format(nickname))
    return {
        keys[0].rsa.label: keys[0].rsa.name,
    }
