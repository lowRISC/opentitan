// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/static_dice_mldsa_cdi.h"

#include "sw/device/lib/base/macros.h"

// ML-DSA DICE certs and keys.
//
// This is placed at a fixed location in memory within the
// .static_dice section. It will be populated by the imm_section (for UDS/CDI_0)
// and ROM_EXT (for CDI_1) to hand over post-quantum DICE chain data.
OT_SET_BSS_SECTION(".static_dice.mldsa_cdi",
                   OT_USED static_dice_mldsa_cdi_t static_dice_mldsa_cdi;)
