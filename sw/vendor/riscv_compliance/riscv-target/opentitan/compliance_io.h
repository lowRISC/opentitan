// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RISC-V Compliance IO Test Header File


#ifndef _COMPLIANCE_IO_H
#define _COMPLIANCE_IO_H

//-----------------------------------------------------------------------
// RV IO Macros (Non functional)
//-----------------------------------------------------------------------

#define RVTEST_IO_INIT
#define RVTEST_IO_WRITE_STR(_SP, _STR)
#define RVTEST_IO_CHECK()
#define RVTEST_IO_ASSERT_GPR_EQ(_SP, _R, _I)
#define RVTEST_IO_ASSERT_SFPR_EQ(_F, _R, _I)
#define RVTEST_IO_ASSERT_DFPR_EQ(_D, _R, _I)

#endif // _COMPLIANCE_IO_H
