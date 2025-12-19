// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

// This pass is intended to straightforwardly and blindly transform all $*ff*
// cells into $FF cells and $check cells into $assert etc cells, it does so
// without introducing new FFs, unlike the versions yosys already provides.
// Currently only $dffe, $aldff and $dff cells are supported.

#include "kernel/ff.h"
#include "kernel/ffinit.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct GlobalClockPass : public Pass {
  GlobalClockPass()
      : Pass("global_clk",
             "introduce a global clock to the design, lower formal cells, and "
             "all flip flops to FFs") {}

  void help() override {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    global_clk [clock name]\n");
    log("\n");
    log("    Lowers $check cells to $assert, $assume, $cover, $live or "
        "$fairness, and in\n");
    log("doing so removes any clocking information. Also replaces all FF types "
        "with\n");
    log("equivalent globally clocked FFs, where again clocking information is "
        "removed\n");
    log("entirely. This may not be correct for latches, which are flopped only "
        "on the global\n");
    log("clock also.\n");
    log("    This pass operates on selected whole modules, of which there may "
        "only be one.\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override {
    if (args.size() != 2) {
      help();
      return;
    }

    if (design->selected_whole_modules().size() != 1) {
      log_error("Only one module may be selected");
      return;
    }
    auto *mod = design->selected_whole_modules()[0];

    auto *gclk = mod->wire(args[1]);
    if (!gclk) {
      log_error("Could not find global clock %s", args[1].c_str());
      return;
    }
    // FIXME: Either use this or don't ask for it!

    log_header(design, "Executing GLOBAL_CLK pass.\n");

    // Will be helpful for extracting FF information
    SigMap sigmap(mod);
    FfInitVals initvals(&sigmap, mod);

    // Can't create cells while iterating them, so copy into a new vector.
    std::vector<RTLIL::Cell *> cells;
    for (auto *cell : mod->cells())
      cells.push_back(cell);

    for (auto *cell : cells) {
      // Lower $check into $assert, $assume etc, without checking clocking
      // information.
      if (cell->type == ID($check)) {
        RTLIL::IdString type;
        auto flavor = cell->getParam(ID(FLAVOR)).decode_string();
        if (flavor == "assert")
          type = ID($assert);
        else if (flavor == "assume")
          type = ID($assume);
        else if (flavor == "cover")
          type = ID($cover);
        else if (flavor == "live")
          type = ID($live);
        else if (flavor == "fair")
          type = ID($fair);
        else {
          log_error("Bad assert flavour %s", flavor.c_str());
          log_abort();
        }

        RTLIL::Cell *lowered = mod->addCell(NEW_ID, type);
        lowered->attributes = cell->attributes;
        lowered->setPort(ID::A, cell->getPort(ID::A));
        lowered->setPort(ID::EN, cell->getPort(ID::EN));
        mod->swap_names(cell, lowered);
        mod->remove(cell);
        continue;
      }

      if (!RTLIL::builtin_ff_cell_types().count(cell->type))
        continue;
      FfData ff(&initvals, cell);

      if (ff.has_gclk)
        continue;  // FF cell, already happy

      if (!ff.has_clk) {
        log_assert(cell->type == ID($dlatch));

        // module \$dlatch (EN, D, Q);
        //     parameter WIDTH = 0;
        //     parameter EN_POLARITY = 1'b1;
        //     input EN;
        //     input [WIDTH-1:0] D;
        //     output reg [WIDTH-1:0] Q;
        //     always @* begin
        //         if (EN == EN_POLARITY)
        //             Q = D;
        //     end
        // endmodule

        auto en = cell->getPort(ID(EN));
        if (!en.is_wire() || en.as_wire() != gclk) {
          log("Warning: Dlatch with non-gclock en\n");
        }
        if (cell->getParam(ID(EN_POLARITY)).as_bool() != 1) {
          log("Warning: gclk dlatch with non-posedge en\n");
        }
        cell->type = ID($ff);
        cell->unsetPort(ID(EN));
        cell->unsetParam(ID(EN_POLARITY));
        continue;
      }
      if (ff.has_srst) {
        log_error("FIXME: has_srst %s\n", cell->type.c_str());
        continue;
      }
      if (ff.has_arst) {
        log_error("FIXME: has_arst %s\n", cell->type.c_str());
        continue;
      }
      if (ff.has_sr) {
        log_error("FIXME: has_sr %s\n", cell->type.c_str());
        continue;
      }
      if (ff.ce_over_srst) {
        log_error("FIXME: ce_over_srst %s\n", cell->type.c_str());
        continue;
      }
      if (ff.is_fine) {
        log_error("FIXME: is_fine %s\n", cell->type.c_str());
        continue;
      }
      if (ff.has_ce) {
        log_assert(cell->type == ID($dffe));

        // Yosys defines $dffe like so:
        // module \$dffe (CLK, EN, D, Q);
        //     parameter WIDTH = 0;
        //     parameter CLK_POLARITY = 1'b1;
        //     parameter EN_POLARITY = 1'b1;
        //     input CLK, EN;
        //     input [WIDTH-1:0] D;
        //     output reg [WIDTH-1:0] Q;
        //     wire pos_clk = CLK == CLK_POLARITY;
        //     always   (posedge pos_clk) begin
        //         if (EN == EN_POLARITY) Q <= D;
        //     end
        // endmodule
        // Hence produce an FF where Q = (en == aload_polarity) ? D : Q

        bool en_polarity = cell->getParam(ID(EN_POLARITY)).as_bool();
        RTLIL::Const width = cell->getParam(ID(WIDTH));
        RTLIL::SigSpec d = cell->getPort(ID(D));
        RTLIL::SigSpec q = cell->getPort(ID(Q));
        RTLIL::SigSpec en = cell->getPort(ID(EN));
        mod->remove(cell);

        auto *sel = mod->addWire(NEW_ID, width.as_int());
        auto *mux = mod->addCell(NEW_ID, ID($mux));
        mux->setParam(ID(WIDTH), width);
        mux->setPort(ID(A), en_polarity ? q : d);
        mux->setPort(ID(B), en_polarity ? d : q);
        mux->setPort(ID(S), en);
        mux->setPort(ID(Y), sel);

        auto *ff = mod->addCell(NEW_ID, ID($ff));
        ff->setParam(ID(WIDTH), width);
        ff->setPort(ID(D), sel);
        ff->setPort(ID(Q), q);
        continue;
      }
      if (ff.has_aload) {
        log_assert(cell->type == ID($aldff));

        // $aldff is defined like so:
        // module \$aldff (CLK, ALOAD, AD, D, Q);
        //     parameter WIDTH = 0;
        //     parameter CLK_POLARITY = 1'b1;
        //     parameter ALOAD_POLARITY = 1'b1;
        //     input CLK, ALOAD;
        //     input [WIDTH-1:0] AD;
        //     input [WIDTH-1:0] D;
        //     output reg [WIDTH-1:0] Q;
        //     wire pos_clk = CLK == CLK_POLARITY;
        //     wire pos_aload = ALOAD == ALOAD_POLARITY;
        //     always   (posedge pos_clk, posedge pos_aload) begin
        //         if (pos_aload)
        //             Q <= AD;
        //         else
        //             Q <= D;
        //     end
        // endmodule
        // Hence produce an FF where sel = (aload == aload_polarity) ? AD : D
        //                               = aload ? (aload_polarity ? AD : D) :
        //                               (aload_polarity ? D : AD)
        // This sames a cell since aload_polarity is a constant, so we can skip
        // the equality check.

        bool aload_polarity = cell->getParam(ID(ALOAD_POLARITY)).as_bool();
        RTLIL::Const width = cell->getParam(ID(WIDTH));

        RTLIL::SigBit aload = cell->getPort(ID(ALOAD));
        RTLIL::SigSpec ad = cell->getPort(ID(AD));
        RTLIL::SigSpec d = cell->getPort(ID(D));
        RTLIL::SigSpec q = cell->getPort(ID(Q));
        mod->remove(cell);

        auto *sel = mod->addWire(NEW_ID, width.as_int());
        auto *mux = mod->addCell(NEW_ID, ID($mux));
        mux->setParam(ID(WIDTH), width);
        mux->setPort(ID(A), aload_polarity ? d : ad);
        mux->setPort(ID(B), aload_polarity ? ad : d);
        mux->setPort(ID(S), aload);
        mux->setPort(ID(Y), sel);

        auto *ff = mod->addCell(NEW_ID, ID($ff));
        ff->setParam(ID(WIDTH), width);
        ff->setPort(ID(D), sel);
        ff->setPort(ID(Q), q);
        continue;
      }

      log_assert(cell->type == ID($dff));

      // $dff is defined as
      // module \$dff (CLK, D, Q);
      //     parameter WIDTH = 0;
      //     parameter CLK_POLARITY = 1'b1;
      //     input CLK;
      //     input [WIDTH-1:0] D;
      //     output reg [WIDTH-1:0] Q;
      //     wire pos_clk = CLK == CLK_POLARITY;
      //     always   (posedge pos_clk) begin
      //         Q <= D;
      //     end
      // endmodule
      // Hence this is very straightforward to map to an $FF

      cell->type = ID($ff);
      cell->unsetPort(ID(CLK));
      cell->unsetParam(ID(CLK_POLARITY));
    }
  }
} ChformalPass;

PRIVATE_NAMESPACE_END
