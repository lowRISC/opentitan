// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SYNTHESIS
  export "DPI-C" function simutil_get_scramble_key;

  function int simutil_get_scramble_key(output bit [127:0] val);
    if (!key_valid_i) begin
      return 0;
    end

    if (DataKeyWidth != 128) begin
      return 0;
    end

    val = key_i;
    return 1;
  endfunction

  export "DPI-C" function simutil_get_scramble_nonce;

  function int simutil_get_scramble_nonce(output bit [319:0] nonce);
    if (!key_valid_i) begin
      return 0;
    end

    if (NonceWidth > 320) begin
      return 0;
    end

    nonce = '0;
    nonce[NonceWidth-1:0] = nonce_i;
    return 1;
  endfunction
`endif
