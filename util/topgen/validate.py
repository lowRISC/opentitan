# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log

def validate_top(topcfg):

    # return as it is for now
    return topcfg

def validate_reset(top):

    # check all resets used in the system are defined
    log.info("Validating resets")
    all_resets = set()
    [all_resets.add(r) for m in top['module'] for r in m['reset']]
    [all_resets.add(r) for x in top['xbar'] for r in x['reset']]

    defined_resets = [reset['name'] for reset in top['resets']]
    log.info("All known resets are %s" % defined_resets)

    for reset in all_resets:
        if reset not in defined_resets:
            log.error("%s is not a defined reset" % reset)
