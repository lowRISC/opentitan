// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_transaction_item extends uvm_sequence_item;

  `uvm_object_utils(spi_transaction_item)
  `uvm_object_new

  // knobs

  // there are 3 possible commands
  // read, write and command only
  // but there are also 3 different modes
  // standard, duplex and quad.
  // the cmd only is weighted by the number of enables
  // to keep distribution.
  // see constraint for further details
  // NOTICE read_weight + write_weight <= 100
  int  read_weight                    = 45;
  int  write_weight                   = 50;
  rand int  alt_weight                = 50;
  bit  std_en                         = 1;
  bit  dual_en                        = 0;
  bit  quad_en                        = 0;

  int  rx_only_weight                 = 20;
  int  tx_only_weight                 = 20;

   // transaction len
  int  spi_len_min                    = 1;
  int  spi_len_max                    = 4;

  // number segments
  int  spi_num_seg_min                = 1;
  int  spi_num_seg_max                = 8;

  // num dummy cycles
  int num_dummy                       = 0;
  //num_addr_bytes
  int num_cmd_bytes                   = 4;
  // max num devices
  int max_spi_device                  = 1;
  // device ID
  int max_spi_devices                 = 1;
  rand int csid;
  // num segments
  rand int num_segments               = 2;
  // spi command
  rand spi_cmd_e cmd;

  spi_segment_item  segment, segment_clone;
  spi_segment_type_e seg_type = spi_segment_type_e'(0);
  spi_segment_item   segments[$];


  // command constraint
  // keeps distribution of read/write/cmd only
  // if only std_en
  // readStd  = 45/100
  // writeStd = 50/100
  // cmd_only =  5/100
  // with duplex en also
  // readStd  = 45/200, readDual  = 45/200 (overall read pct 45/100)
  // writeStd = 50/200, writeDual = 50/200 (overall write pct 50/100)
  // cmd_only = 2*5/200 (overall 5/100) etc.
  constraint cmd_c {
    solve alt_weight before cmd;
    alt_weight dist {
      0        := 50,
      [1:50]   := 20,
      [51:100] := 30
    };
    alt_weight dist {0        := 50,
                     [1:50]   := 20,
                     [51:100] := 30
    };
    cmd dist {ReadStd   := read_weight*std_en,
              WriteStd  := write_weight*std_en,
              ReadDual  := read_weight*dual_en,
              WriteDual := write_weight*dual_en,
              ReadQuad  := read_weight*quad_en,
              WriteQuad := write_weight*quad_en,
              AltCmd    := alt_weight
    };

    read_weight + write_weight == 100;
  }

  constraint csid_c {
    csid inside { [0:max_spi_devices-1] };
  }

  constraint num_segments_c {
    num_segments inside { [spi_num_seg_min:spi_num_seg_max] };
  }

  function void post_randomize();
    generate_segments();
    update_csaat();
  endfunction


  function void segment_init();
    segment                  = new();
    segment.rx_only_weight   = rx_only_weight;
    segment.tx_only_weight   = tx_only_weight;
    segment.num_dummy        = num_dummy;
    segment.num_cmd_bytes    = num_cmd_bytes;
    segment.spi_len_min      = spi_len_min;
    segment.spi_len_max      = spi_len_max;
  endfunction


  function int get_num_segments();
    return segments.size();
  endfunction

  function void update_csaat();
    // set last segments csaat to 1
    // except the last segment (csaat default = 0)
    segments[0].command_reg.csaat = 0;
  endfunction


  function void generate_segments();
    seg_type = Command;

    for (int i = 0; i < num_segments; i++) begin
      segment_init();
      segment.cmd              = cmd;
      segment.seg_type         = seg_type;
      `DV_CHECK_RANDOMIZE_FATAL(segment)

      `downcast(segment_clone, segment.clone());
      segments.push_front(segment_clone);

      // if we are already in Data segments
      // the following segments will also be data
      if ( seg_type != Data) seg_type = seg_type.next();

      if ((num_dummy == 0) && (seg_type == Dummy)) begin
        seg_type = seg_type.next();
      end
    end
  endfunction


  function string convert2string();
    string txt ="";

    txt = $sformatf("\n ----| SPI TRANSACTION |-----");
    txt = {txt, $sformatf("\n ----| Command type %s", cmd.name)};

    foreach (segments[i]) begin
      txt = {txt, $sformatf("\n Segment [%d] \n, %s", i, segments[i].convert2string())};
    end
    return txt;
  endfunction


  function void do_copy(uvm_object rhs);
    spi_transaction_item rhs_;
    `downcast(rhs, rhs_);
    super.do_copy(rhs);
  endfunction // do_copy
endclass
