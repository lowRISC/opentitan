# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Supported DICE certificate formats which can be used in e.g. perso firmware.
DICE_FORMATS = [
    # An X.509 certificate chain, using ECDSA P-256 signing, rooted by a CA signed UDS cert.
    "x509",
    # A CWT certificate chain, using COSE signing with ECDSA P-256, rooted in a UDS public
    # key (i.e. a COSE_Key) which is recorded by the host.
    "cwt",
    # A hybrid scheme based on two parallel X.509 certificate chains, one using ECDSA P-256
    # signing (as for "x509"), and the other using ML-DSA (either ML-DSA-44 or ML-DSA-87),
    # depending on the ROM_EXT's configuration. This is also rooted in CA signed UDS certs.
    "mldsa",
]
