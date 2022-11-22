// See LICENSE.SiFive for license details.

#include "encoding.h"

// The debugger can assume as second scratch register.
// # define SND_SCRATCH 1
// These are implementation-specific addresses in the Debug Module
#define HALTED    0x100
#define GOING     0x108
#define RESUMING  0x110
#define EXCEPTION 0x118

// Region of memory where each hart has 1
// byte to read.
#define FLAGS 0x400
#define FLAG_GO     0
#define FLAG_RESUME 1

        .option norvc
        .global entry
        .global exception

        // Entry location on ebreak, Halt, or Breakpoint
        // It is the same for all harts. They branch when
        // their GO or RESUME bit is set.

entry:
       jal zero, _entry
       nop
resume:
       jal zero, _resume
       nop
exception:
       jal zero, _exception
       nop



_entry:
        // This fence is required because the execution may have written something
        // into the Abstract Data or Program Buffer registers.
        fence
        csrw CSR_DSCRATCH0, s0       // Save s0 to allow signaling MHARTID
#ifdef SND_SCRATCH
        csrw CSR_DSCRATCH1, a0       // Save a0 to allow loading arbitrary DM base
        auipc a0, 0                  // Get PC
        srli a0, a0, 12              // And throw away lower 12 bits to get the DM base
        slli a0, a0, 12
#endif
        // We continue to let the hart know that we are halted in order that
        // a DM which was reset is still made aware that a hart is halted.
        // We keep checking both whether there is something the debugger wants
        // us to do, or whether we should resume.
entry_loop:
        csrr s0, CSR_MHARTID
#ifdef SND_SCRATCH
        sw   s0, HALTED(a0)
        add  s0, s0, a0
#else
        sw   s0, HALTED(zero)
#endif
        lbu  s0, FLAGS(s0) // 1 byte flag per hart. Only one hart advances here.
        andi s0, s0, (1 << FLAG_GO)
        bnez s0, going
        csrr s0, CSR_MHARTID
#ifdef SND_SCRATCH
        add  s0, s0, a0
#endif
        lbu  s0, FLAGS(s0) // multiple harts can resume  here
        andi s0, s0, (1 << FLAG_RESUME)
        bnez s0, resume
        jal  zero, entry_loop

_exception:
        // We can only get here due to an exception while in debug mode. Hence,
        // we do not need to save a0 to a scratch register as it has already
        // been saved on debug entry.
#ifdef SND_SCRATCH
        auipc a0, 0                  // Get POC
        srli a0, a0, 12              // And throw away lower 12 bits to get the DM base
        slli a0, a0, 12
        sw   zero, EXCEPTION(a0)     // Let debug module know you got an exception.
        // It is safe to always restore the scratch registers here as they must
        // have been saved on debug entry. Restoring them here avoids issues
        // with registers being overwritten by exceptions occuring during
        // program buffer execution.
        csrr a0, CSR_DSCRATCH1       // Restore a0 here
#else
        sw   zero, EXCEPTION(zero)     // Let debug module know you got an exception.
#endif
        csrr s0, CSR_DSCRATCH0       // Restore s0 here
        ebreak

going:
#ifdef SND_SCRATCH
        sw zero, GOING(a0)          // When debug module sees this write, the GO flag is reset.
        csrr a0, CSR_DSCRATCH1      // Restore a0 here
#else
        sw zero, GOING(zero)          // When debug module sees this write, the GO flag is reset.
#endif
        csrr s0, CSR_DSCRATCH0      // Restore s0 here
        jal zero, whereto
_resume:
        csrr s0, CSR_MHARTID
#ifdef SND_SCRATCH
        sw   s0, RESUMING(a0)   // When Debug Module sees this write, the RESUME flag is reset.
        csrr a0, CSR_DSCRATCH1  // Restore a0 here
#else
        sw   s0, RESUMING(zero)   // When Debug Module sees this write, the RESUME flag is reset.
#endif
        csrr s0, CSR_DSCRATCH0  // Restore s0 here
        dret

        // END OF ACTUAL "ROM" CONTENTS. BELOW IS JUST FOR LINKER SCRIPT.

.section .whereto
whereto:
        nop
        // Variable "ROM" This is : jal x0 abstract, jal x0 program_buffer,
        //                or jal x0 resume, as desired.
        //                Debug Module state machine tracks what is 'desired'.
        //                We don't need/want to use jalr here because all of the
        //                Variable ROM contents are set by
        //                Debug Module before setting the OK_GO byte.
