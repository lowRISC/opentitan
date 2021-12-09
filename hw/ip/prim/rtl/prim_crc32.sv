// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// CRC32 calculator
//
// This module takes in n-bits data words (n defined by BytePerWord parameter) and updates an
// internally stored CRC with each valid data word. The polynomial used is the standard CRC32 IEEE
// one. An interface is provided to set the internal CRC to an arbitrary value. The output CRC is an
// inverted version of the internally stored CRC and the input CRC is inverted before being stored.
// This is done so results match existing widely used software libraries (e.g. the crc32
// functionality available in Python). Note that a initial CRC of 0x0 (corresponding to an internal
// CRC of 0xffffffff) must be used to match results generated elsewhere.


module prim_crc32 #(
  parameter int unsigned BytesPerWord = 4
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  input  logic                      set_crc_i,
  input  logic [31:0]               crc_in_i,

  input  logic                      data_valid_i,
  input  logic [BytesPerWord*8-1:0] data_i,

  output logic [31:0]               crc_out_o
);
  // Generated using hw/ip/prim/util/prim_crc32_table_gen.py
  function automatic logic [31:0] crc32_byte_calc(logic [7:0] b);
    unique case (b)
      8'hff:   crc32_byte_calc = 32'h2d02ef8d;
      8'hfe:   crc32_byte_calc = 32'h5a05df1b;
      8'hfd:   crc32_byte_calc = 32'hc30c8ea1;
      8'hfc:   crc32_byte_calc = 32'hb40bbe37;
      8'hfb:   crc32_byte_calc = 32'h2a6f2b94;
      8'hfa:   crc32_byte_calc = 32'h5d681b02;
      8'hf9:   crc32_byte_calc = 32'hc4614ab8;
      8'hf8:   crc32_byte_calc = 32'hb3667a2e;
      8'hf7:   crc32_byte_calc = 32'h23d967bf;
      8'hf6:   crc32_byte_calc = 32'h54de5729;
      8'hf5:   crc32_byte_calc = 32'hcdd70693;
      8'hf4:   crc32_byte_calc = 32'hbad03605;
      8'hf3:   crc32_byte_calc = 32'h24b4a3a6;
      8'hf2:   crc32_byte_calc = 32'h53b39330;
      8'hf1:   crc32_byte_calc = 32'hcabac28a;
      8'hf0:   crc32_byte_calc = 32'hbdbdf21c;
      8'hef:   crc32_byte_calc = 32'h30b5ffe9;
      8'hee:   crc32_byte_calc = 32'h47b2cf7f;
      8'hed:   crc32_byte_calc = 32'hdebb9ec5;
      8'hec:   crc32_byte_calc = 32'ha9bcae53;
      8'heb:   crc32_byte_calc = 32'h37d83bf0;
      8'hea:   crc32_byte_calc = 32'h40df0b66;
      8'he9:   crc32_byte_calc = 32'hd9d65adc;
      8'he8:   crc32_byte_calc = 32'haed16a4a;
      8'he7:   crc32_byte_calc = 32'h3e6e77db;
      8'he6:   crc32_byte_calc = 32'h4969474d;
      8'he5:   crc32_byte_calc = 32'hd06016f7;
      8'he4:   crc32_byte_calc = 32'ha7672661;
      8'he3:   crc32_byte_calc = 32'h3903b3c2;
      8'he2:   crc32_byte_calc = 32'h4e048354;
      8'he1:   crc32_byte_calc = 32'hd70dd2ee;
      8'he0:   crc32_byte_calc = 32'ha00ae278;
      8'hdf:   crc32_byte_calc = 32'h166ccf45;
      8'hde:   crc32_byte_calc = 32'h616bffd3;
      8'hdd:   crc32_byte_calc = 32'hf862ae69;
      8'hdc:   crc32_byte_calc = 32'h8f659eff;
      8'hdb:   crc32_byte_calc = 32'h11010b5c;
      8'hda:   crc32_byte_calc = 32'h66063bca;
      8'hd9:   crc32_byte_calc = 32'hff0f6a70;
      8'hd8:   crc32_byte_calc = 32'h88085ae6;
      8'hd7:   crc32_byte_calc = 32'h18b74777;
      8'hd6:   crc32_byte_calc = 32'h6fb077e1;
      8'hd5:   crc32_byte_calc = 32'hf6b9265b;
      8'hd4:   crc32_byte_calc = 32'h81be16cd;
      8'hd3:   crc32_byte_calc = 32'h1fda836e;
      8'hd2:   crc32_byte_calc = 32'h68ddb3f8;
      8'hd1:   crc32_byte_calc = 32'hf1d4e242;
      8'hd0:   crc32_byte_calc = 32'h86d3d2d4;
      8'hcf:   crc32_byte_calc = 32'h0bdbdf21;
      8'hce:   crc32_byte_calc = 32'h7cdcefb7;
      8'hcd:   crc32_byte_calc = 32'he5d5be0d;
      8'hcc:   crc32_byte_calc = 32'h92d28e9b;
      8'hcb:   crc32_byte_calc = 32'h0cb61b38;
      8'hca:   crc32_byte_calc = 32'h7bb12bae;
      8'hc9:   crc32_byte_calc = 32'he2b87a14;
      8'hc8:   crc32_byte_calc = 32'h95bf4a82;
      8'hc7:   crc32_byte_calc = 32'h05005713;
      8'hc6:   crc32_byte_calc = 32'h72076785;
      8'hc5:   crc32_byte_calc = 32'heb0e363f;
      8'hc4:   crc32_byte_calc = 32'h9c0906a9;
      8'hc3:   crc32_byte_calc = 32'h026d930a;
      8'hc2:   crc32_byte_calc = 32'h756aa39c;
      8'hc1:   crc32_byte_calc = 32'hec63f226;
      8'hc0:   crc32_byte_calc = 32'h9b64c2b0;
      8'hbf:   crc32_byte_calc = 32'h5bdeae1d;
      8'hbe:   crc32_byte_calc = 32'h2cd99e8b;
      8'hbd:   crc32_byte_calc = 32'hb5d0cf31;
      8'hbc:   crc32_byte_calc = 32'hc2d7ffa7;
      8'hbb:   crc32_byte_calc = 32'h5cb36a04;
      8'hba:   crc32_byte_calc = 32'h2bb45a92;
      8'hb9:   crc32_byte_calc = 32'hb2bd0b28;
      8'hb8:   crc32_byte_calc = 32'hc5ba3bbe;
      8'hb7:   crc32_byte_calc = 32'h5505262f;
      8'hb6:   crc32_byte_calc = 32'h220216b9;
      8'hb5:   crc32_byte_calc = 32'hbb0b4703;
      8'hb4:   crc32_byte_calc = 32'hcc0c7795;
      8'hb3:   crc32_byte_calc = 32'h5268e236;
      8'hb2:   crc32_byte_calc = 32'h256fd2a0;
      8'hb1:   crc32_byte_calc = 32'hbc66831a;
      8'hb0:   crc32_byte_calc = 32'hcb61b38c;
      8'haf:   crc32_byte_calc = 32'h4669be79;
      8'hae:   crc32_byte_calc = 32'h316e8eef;
      8'had:   crc32_byte_calc = 32'ha867df55;
      8'hac:   crc32_byte_calc = 32'hdf60efc3;
      8'hab:   crc32_byte_calc = 32'h41047a60;
      8'haa:   crc32_byte_calc = 32'h36034af6;
      8'ha9:   crc32_byte_calc = 32'haf0a1b4c;
      8'ha8:   crc32_byte_calc = 32'hd80d2bda;
      8'ha7:   crc32_byte_calc = 32'h48b2364b;
      8'ha6:   crc32_byte_calc = 32'h3fb506dd;
      8'ha5:   crc32_byte_calc = 32'ha6bc5767;
      8'ha4:   crc32_byte_calc = 32'hd1bb67f1;
      8'ha3:   crc32_byte_calc = 32'h4fdff252;
      8'ha2:   crc32_byte_calc = 32'h38d8c2c4;
      8'ha1:   crc32_byte_calc = 32'ha1d1937e;
      8'ha0:   crc32_byte_calc = 32'hd6d6a3e8;
      8'h9f:   crc32_byte_calc = 32'h60b08ed5;
      8'h9e:   crc32_byte_calc = 32'h17b7be43;
      8'h9d:   crc32_byte_calc = 32'h8ebeeff9;
      8'h9c:   crc32_byte_calc = 32'hf9b9df6f;
      8'h9b:   crc32_byte_calc = 32'h67dd4acc;
      8'h9a:   crc32_byte_calc = 32'h10da7a5a;
      8'h99:   crc32_byte_calc = 32'h89d32be0;
      8'h98:   crc32_byte_calc = 32'hfed41b76;
      8'h97:   crc32_byte_calc = 32'h6e6b06e7;
      8'h96:   crc32_byte_calc = 32'h196c3671;
      8'h95:   crc32_byte_calc = 32'h806567cb;
      8'h94:   crc32_byte_calc = 32'hf762575d;
      8'h93:   crc32_byte_calc = 32'h6906c2fe;
      8'h92:   crc32_byte_calc = 32'h1e01f268;
      8'h91:   crc32_byte_calc = 32'h8708a3d2;
      8'h90:   crc32_byte_calc = 32'hf00f9344;
      8'h8f:   crc32_byte_calc = 32'h7d079eb1;
      8'h8e:   crc32_byte_calc = 32'h0a00ae27;
      8'h8d:   crc32_byte_calc = 32'h9309ff9d;
      8'h8c:   crc32_byte_calc = 32'he40ecf0b;
      8'h8b:   crc32_byte_calc = 32'h7a6a5aa8;
      8'h8a:   crc32_byte_calc = 32'h0d6d6a3e;
      8'h89:   crc32_byte_calc = 32'h94643b84;
      8'h88:   crc32_byte_calc = 32'he3630b12;
      8'h87:   crc32_byte_calc = 32'h73dc1683;
      8'h86:   crc32_byte_calc = 32'h04db2615;
      8'h85:   crc32_byte_calc = 32'h9dd277af;
      8'h84:   crc32_byte_calc = 32'head54739;
      8'h83:   crc32_byte_calc = 32'h74b1d29a;
      8'h82:   crc32_byte_calc = 32'h03b6e20c;
      8'h81:   crc32_byte_calc = 32'h9abfb3b6;
      8'h80:   crc32_byte_calc = 32'hedb88320;
      8'h7f:   crc32_byte_calc = 32'hc0ba6cad;
      8'h7e:   crc32_byte_calc = 32'hb7bd5c3b;
      8'h7d:   crc32_byte_calc = 32'h2eb40d81;
      8'h7c:   crc32_byte_calc = 32'h59b33d17;
      8'h7b:   crc32_byte_calc = 32'hc7d7a8b4;
      8'h7a:   crc32_byte_calc = 32'hb0d09822;
      8'h79:   crc32_byte_calc = 32'h29d9c998;
      8'h78:   crc32_byte_calc = 32'h5edef90e;
      8'h77:   crc32_byte_calc = 32'hce61e49f;
      8'h76:   crc32_byte_calc = 32'hb966d409;
      8'h75:   crc32_byte_calc = 32'h206f85b3;
      8'h74:   crc32_byte_calc = 32'h5768b525;
      8'h73:   crc32_byte_calc = 32'hc90c2086;
      8'h72:   crc32_byte_calc = 32'hbe0b1010;
      8'h71:   crc32_byte_calc = 32'h270241aa;
      8'h70:   crc32_byte_calc = 32'h5005713c;
      8'h6f:   crc32_byte_calc = 32'hdd0d7cc9;
      8'h6e:   crc32_byte_calc = 32'haa0a4c5f;
      8'h6d:   crc32_byte_calc = 32'h33031de5;
      8'h6c:   crc32_byte_calc = 32'h44042d73;
      8'h6b:   crc32_byte_calc = 32'hda60b8d0;
      8'h6a:   crc32_byte_calc = 32'had678846;
      8'h69:   crc32_byte_calc = 32'h346ed9fc;
      8'h68:   crc32_byte_calc = 32'h4369e96a;
      8'h67:   crc32_byte_calc = 32'hd3d6f4fb;
      8'h66:   crc32_byte_calc = 32'ha4d1c46d;
      8'h65:   crc32_byte_calc = 32'h3dd895d7;
      8'h64:   crc32_byte_calc = 32'h4adfa541;
      8'h63:   crc32_byte_calc = 32'hd4bb30e2;
      8'h62:   crc32_byte_calc = 32'ha3bc0074;
      8'h61:   crc32_byte_calc = 32'h3ab551ce;
      8'h60:   crc32_byte_calc = 32'h4db26158;
      8'h5f:   crc32_byte_calc = 32'hfbd44c65;
      8'h5e:   crc32_byte_calc = 32'h8cd37cf3;
      8'h5d:   crc32_byte_calc = 32'h15da2d49;
      8'h5c:   crc32_byte_calc = 32'h62dd1ddf;
      8'h5b:   crc32_byte_calc = 32'hfcb9887c;
      8'h5a:   crc32_byte_calc = 32'h8bbeb8ea;
      8'h59:   crc32_byte_calc = 32'h12b7e950;
      8'h58:   crc32_byte_calc = 32'h65b0d9c6;
      8'h57:   crc32_byte_calc = 32'hf50fc457;
      8'h56:   crc32_byte_calc = 32'h8208f4c1;
      8'h55:   crc32_byte_calc = 32'h1b01a57b;
      8'h54:   crc32_byte_calc = 32'h6c0695ed;
      8'h53:   crc32_byte_calc = 32'hf262004e;
      8'h52:   crc32_byte_calc = 32'h856530d8;
      8'h51:   crc32_byte_calc = 32'h1c6c6162;
      8'h50:   crc32_byte_calc = 32'h6b6b51f4;
      8'h4f:   crc32_byte_calc = 32'he6635c01;
      8'h4e:   crc32_byte_calc = 32'h91646c97;
      8'h4d:   crc32_byte_calc = 32'h086d3d2d;
      8'h4c:   crc32_byte_calc = 32'h7f6a0dbb;
      8'h4b:   crc32_byte_calc = 32'he10e9818;
      8'h4a:   crc32_byte_calc = 32'h9609a88e;
      8'h49:   crc32_byte_calc = 32'h0f00f934;
      8'h48:   crc32_byte_calc = 32'h7807c9a2;
      8'h47:   crc32_byte_calc = 32'he8b8d433;
      8'h46:   crc32_byte_calc = 32'h9fbfe4a5;
      8'h45:   crc32_byte_calc = 32'h06b6b51f;
      8'h44:   crc32_byte_calc = 32'h71b18589;
      8'h43:   crc32_byte_calc = 32'hefd5102a;
      8'h42:   crc32_byte_calc = 32'h98d220bc;
      8'h41:   crc32_byte_calc = 32'h01db7106;
      8'h40:   crc32_byte_calc = 32'h76dc4190;
      8'h3f:   crc32_byte_calc = 32'hb6662d3d;
      8'h3e:   crc32_byte_calc = 32'hc1611dab;
      8'h3d:   crc32_byte_calc = 32'h58684c11;
      8'h3c:   crc32_byte_calc = 32'h2f6f7c87;
      8'h3b:   crc32_byte_calc = 32'hb10be924;
      8'h3a:   crc32_byte_calc = 32'hc60cd9b2;
      8'h39:   crc32_byte_calc = 32'h5f058808;
      8'h38:   crc32_byte_calc = 32'h2802b89e;
      8'h37:   crc32_byte_calc = 32'hb8bda50f;
      8'h36:   crc32_byte_calc = 32'hcfba9599;
      8'h35:   crc32_byte_calc = 32'h56b3c423;
      8'h34:   crc32_byte_calc = 32'h21b4f4b5;
      8'h33:   crc32_byte_calc = 32'hbfd06116;
      8'h32:   crc32_byte_calc = 32'hc8d75180;
      8'h31:   crc32_byte_calc = 32'h51de003a;
      8'h30:   crc32_byte_calc = 32'h26d930ac;
      8'h2f:   crc32_byte_calc = 32'habd13d59;
      8'h2e:   crc32_byte_calc = 32'hdcd60dcf;
      8'h2d:   crc32_byte_calc = 32'h45df5c75;
      8'h2c:   crc32_byte_calc = 32'h32d86ce3;
      8'h2b:   crc32_byte_calc = 32'hacbcf940;
      8'h2a:   crc32_byte_calc = 32'hdbbbc9d6;
      8'h29:   crc32_byte_calc = 32'h42b2986c;
      8'h28:   crc32_byte_calc = 32'h35b5a8fa;
      8'h27:   crc32_byte_calc = 32'ha50ab56b;
      8'h26:   crc32_byte_calc = 32'hd20d85fd;
      8'h25:   crc32_byte_calc = 32'h4b04d447;
      8'h24:   crc32_byte_calc = 32'h3c03e4d1;
      8'h23:   crc32_byte_calc = 32'ha2677172;
      8'h22:   crc32_byte_calc = 32'hd56041e4;
      8'h21:   crc32_byte_calc = 32'h4c69105e;
      8'h20:   crc32_byte_calc = 32'h3b6e20c8;
      8'h1f:   crc32_byte_calc = 32'h8d080df5;
      8'h1e:   crc32_byte_calc = 32'hfa0f3d63;
      8'h1d:   crc32_byte_calc = 32'h63066cd9;
      8'h1c:   crc32_byte_calc = 32'h14015c4f;
      8'h1b:   crc32_byte_calc = 32'h8a65c9ec;
      8'h1a:   crc32_byte_calc = 32'hfd62f97a;
      8'h19:   crc32_byte_calc = 32'h646ba8c0;
      8'h18:   crc32_byte_calc = 32'h136c9856;
      8'h17:   crc32_byte_calc = 32'h83d385c7;
      8'h16:   crc32_byte_calc = 32'hf4d4b551;
      8'h15:   crc32_byte_calc = 32'h6ddde4eb;
      8'h14:   crc32_byte_calc = 32'h1adad47d;
      8'h13:   crc32_byte_calc = 32'h84be41de;
      8'h12:   crc32_byte_calc = 32'hf3b97148;
      8'h11:   crc32_byte_calc = 32'h6ab020f2;
      8'h10:   crc32_byte_calc = 32'h1db71064;
      8'h0f:   crc32_byte_calc = 32'h90bf1d91;
      8'h0e:   crc32_byte_calc = 32'he7b82d07;
      8'h0d:   crc32_byte_calc = 32'h7eb17cbd;
      8'h0c:   crc32_byte_calc = 32'h09b64c2b;
      8'h0b:   crc32_byte_calc = 32'h97d2d988;
      8'h0a:   crc32_byte_calc = 32'he0d5e91e;
      8'h09:   crc32_byte_calc = 32'h79dcb8a4;
      8'h08:   crc32_byte_calc = 32'h0edb8832;
      8'h07:   crc32_byte_calc = 32'h9e6495a3;
      8'h06:   crc32_byte_calc = 32'he963a535;
      8'h05:   crc32_byte_calc = 32'h706af48f;
      8'h04:   crc32_byte_calc = 32'h076dc419;
      8'h03:   crc32_byte_calc = 32'h990951ba;
      8'h02:   crc32_byte_calc = 32'hee0e612c;
      8'h01:   crc32_byte_calc = 32'h77073096;
      8'h00:   crc32_byte_calc = 32'h00000000;
      default: crc32_byte_calc = '0;
    endcase
  endfunction

  logic [31:0] crc_d, crc_q;
  logic        crc_en;
  logic [31:0] crc_stages[BytesPerWord + 1];

  assign crc_en = set_crc_i | data_valid_i;

  assign crc_stages[0] = crc_q;

  for (genvar i = 0;i < BytesPerWord; ++i) begin : g_crc_stages
    assign crc_stages[i + 1] =
      {8'h00, crc_stages[i][31:8]} ^
      crc32_byte_calc(crc_stages[i][7:0] ^ data_i[i * 8 +: 8]);
  end

  always_comb begin
    if (set_crc_i) begin
      crc_d = ~crc_in_i;
    end else begin
      crc_d = crc_stages[BytesPerWord];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crc_q <= 32'hFFFFFFFF;
    end else if (crc_en) begin
      crc_q <= crc_d;
    end
  end

  assign crc_out_o = ~crc_q;
endmodule
