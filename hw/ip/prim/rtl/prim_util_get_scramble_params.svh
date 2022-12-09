// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SYNTHESIS
  export "DPI-C" function simutil_get_scramble_key;

  function int simutil_get_scramble_key(output bit [127:0] val);
    int valid;
    valid = key_valid_i && DataKeyWidth == 128 ? 1 : 0;
    if (valid == 1) val = key_i;
    return valid;
  endfunction

  export "DPI-C" function simutil_get_scramble_nonce;

  function int simutil_get_scramble_nonce(output bit [319:0] nonce);
    int valid;
    valid = key_valid_i && NonceWidth <= 320 ? 1 : 0;
    if (valid == 1) begin
       nonce = '0;
       nonce[NonceWidth-1:0] = nonce_i;
    end
    return valid;
  endfunction
`endif
