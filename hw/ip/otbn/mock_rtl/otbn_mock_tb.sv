// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_mock_tb();
  logic clk;
  logic rst_n;

  initial begin
    clk = 0;
    rst_n = 1;
    #3;
    rst_n = 0;
    #3;
    rst_n = 1;
    #4;
    forever begin
      #5;
      clk = ~clk;
    end
  end

  logic [4:0] rf_rd_addr_a;
  logic [4:0] rf_rd_addr_b;

  logic [4:0]   rf_wr_addr;
  logic [1:0]   rf_wr_en;
  logic [255:0] rf_wr_data;
  logic         rf_wr_data_sel;

  logic       shift_left;
  logic [7:0] shift_amt;
  logic       shift_en;

  logic [1:0] a_qw_sel;
  logic [1:0] b_qw_sel;

  logic [1:0] pre_acc_shift;

  logic [11:0] imm;
  logic        imm_sel;

  logic zero_acc;
  logic mac_en;
  logic mul_en;
  logic acc_shift_out;
  logic add_en;
  logic sub_en;
  logic pseudo_mod;

  logic [255:0] mod_wr_data;
  logic         mod_wr_en;

  logic [255:0] rf_rd_data_a;
  logic [255:0] rf_rd_data_b;

  logic error;
  logic tb_check;
  logic [31:0] errors_seen;
  logic [255:0] expected_result;

  initial begin
    rf_rd_addr_a <= '0;
    rf_rd_addr_b <= '0;
    rf_wr_addr <= '0;
    rf_wr_en <= '0;
    rf_wr_data <= '0;
    rf_wr_data_sel <= '0;
    shift_left <= 0;
    shift_amt <= '0;
    shift_en <= 0;
    a_qw_sel <= '0;
    b_qw_sel <= '0;
    pre_acc_shift <= '0;
    imm <= '0;
    imm_sel <= 0;
    zero_acc <= '0;
    mac_en <= '0;
    mul_en <= '0;
    acc_shift_out <= '0;
    add_en <= '0;
    sub_en <= 0;
    pseudo_mod <= 0;
    mod_wr_data <= '0;;
    mod_wr_en <= 0;
    tb_check <= 0;
    expected_result <= '0;

    @(posedge clk);

    rf_wr_addr <= 1;
    rf_wr_data <= 256'hc62b1dbd2e335e8f3ac4aa13e00ec9365246635d2f3a165cbba94fcebbfb6500;
    rf_wr_data_sel <= 1;
    rf_wr_en <= 2'b11;

    @(posedge clk);

    rf_wr_addr <= 2;
    rf_wr_data <= 256'h446d11cbeab5ee1e458a917fcc2744c82a212b74f31716a1ee8fc494fdd12f1f;
    rf_wr_data_sel <= 1;
    rf_wr_en <= 2'b11;

    @(posedge clk);

    rf_rd_addr_a <= 1;
    rf_rd_addr_b <= 2;
    rf_wr_addr <= 3;
    rf_wr_en <= 2'b11;
    rf_wr_data_sel <= 0;
    add_en <= 1'b1;

    @(posedge clk);

    rf_wr_addr <= 4;
    shift_amt <= 24;

    @(posedge clk);

    rf_wr_addr <= 5;
    shift_left <= 1'b1;

    @(posedge clk);

    rf_wr_addr <= 6;
    sub_en <= 1'b1;
    add_en <= 1'b0;
    shift_amt <= 0;
    shift_left <= 1'b0;

    @(posedge clk);

    rf_wr_addr <= 7;
    shift_amt <= 24;

    @(posedge clk);

    rf_wr_addr <= 8;
    shift_left <= 1'b1;

    @(posedge clk);

    rf_wr_addr <= 9;
    sub_en <= 1'b0;
    shift_en <= 1'b1;
    shift_amt <= 47;
    shift_left <= 1'b0;

    @(posedge clk);

    shift_en <= 1'b0;
    shift_amt <= 0;
    rf_wr_en <= 2'b0;
    mod_wr_data <= 256'h4d6d3b775930912981d087c14fcb7b88c9f4dfc65551b682;
    mod_wr_en <= 1'b1;

    @(posedge clk);

    rf_wr_addr <= 10;
    rf_wr_en <= 2'b11;
    mod_wr_en <= 1'b0;
    add_en <= 1'b1;
    shift_amt <= 0;
    pseudo_mod <= 1;

    @(posedge clk);

    rf_wr_addr <= 11;
    add_en <= 1'b0;
    sub_en <= 1'b1;

    @(posedge clk);

    pseudo_mod <= 0;
    rf_wr_addr <= 12;
    add_en <= 1'b1;
    sub_en <= 1'b0;
    imm_sel <= 1'b1;
    imm <= 12'h4d8;

    @(posedge clk);

    rf_wr_addr <= 13;
    add_en <= 1'b0;
    sub_en <= 1'b1;
    imm <= 12'h1f1;

    @(posedge clk);

    rf_wr_addr <= 1;
    rf_wr_data <= 256'h70b438448ec83e0c65da3949575ff6fe;
    rf_wr_data_sel <= 1;
    add_en <= 1'b0;
    sub_en <= 1'b0;

    @(posedge clk);

    rf_wr_addr <= 2;
    rf_wr_data <= 256'hbefe38561857bdf696987717bfce1567;
    rf_wr_data_sel <= 1;

    @(posedge clk);

    rf_wr_en <= 2'b00;
    rf_rd_addr_a <= 1;
    rf_rd_addr_b <= 2;
    mac_en <= 1'b1;
    zero_acc <= 1'b1;
    rf_wr_data_sel <= 0;

    @(posedge clk);

    a_qw_sel <= 1;
    b_qw_sel <= 0;
    pre_acc_shift <= 1;
    zero_acc <= 1'b0;

    @(posedge clk);

    a_qw_sel <= 0;
    b_qw_sel <= 1;
    pre_acc_shift <= 1;

    @(posedge clk);

    a_qw_sel <= 1;
    b_qw_sel <= 1;
    pre_acc_shift <= 2;
    rf_wr_addr <= 14;
    rf_wr_en <= 2'b11;

    @(posedge clk);

    rf_wr_addr <= 15;
    a_qw_sel <= 2'b00;
    b_qw_sel <= 2'b00;
    mac_en <= 1'b0;
    mul_en <= 1'b1;

    @(posedge clk);

    mul_en <= 1'b0;
    rf_wr_en <= 2'b0;
    rf_rd_addr_a <= 3;
    tb_check <= 1'b1;
    expected_result <= 256'h0a982f8918e94cad804f3b93ac360dfe7c678ed222512cfeaa391463b9cc941f;

    @(posedge clk);

    rf_rd_addr_a <= 4;
    expected_result <= 256'hc62b1e019b452a79f0b2c8596aa04902798b2b8750658b4fd2bff1bd4bbff9fd;

    @(posedge clk);

    rf_rd_addr_a <= 5;
    expected_result <= 256'h9215d3ab4c78e920ba90d158a838ea61c7397a73d128a62150a720fddafb6500;

    @(posedge clk);

    rf_rd_addr_a <= 6;
    expected_result <= 256'h81be0bf1437d7070f53a189413e7846e282537e83c22ffbacd198b39be2a35e1;

    @(posedge clk);

    rf_rd_addr_a <= 7;
    expected_result <= 256'hc62b1d78c12192a484d68bce557d496a2b019b330e0ea169a492ade02c36d003;

    @(posedge clk);

    rf_rd_addr_a <= 8;
    expected_result <= 256'hfa4067cf0fedd3fdbaf882cf17e4a80add534c468d4b869826ab7e9f9cfb6500;

    @(posedge clk);

    rf_rd_addr_a <= 9;
    expected_result <= 256'h9f9d77f6ca0088da2397d56bdc3c8b1522ff984e8990544256e9e62e2d43dd1f;

    @(posedge clk);

    rf_rd_addr_a <= 10;
    expected_result <= 256'h0a982f8918e94cad32e2001c53057cd4fa970710d285b175e044349d647add9d;

    @(posedge clk);

    rf_rd_addr_a <= 11;
    expected_result <= 256'h81be0bf1437d7070a7ccdd1cbab6f344a654b026ec5784320324ab7368d87f5f;

    @(posedge clk);

    rf_rd_addr_a <= 12;
    expected_result <= 256'hc62b1dbd2e335e8f3ac4aa13e00ec9365246635d2f3a165cbba94fcebbfb69d8;

    @(posedge clk);

    rf_rd_addr_a <= 13;
    expected_result <= 256'hc62b1dbd2e335e8f3ac4aa13e00ec9365246635d2f3a165cbba94fcebbfb630f;

    @(posedge clk);

    rf_rd_addr_a <= 14;
    expected_result <= 256'h5415ad60098fb525b271470c529b4620d316a866317cf8aba2f43bff49433632;

    @(posedge clk);

    rf_rd_addr_a <= 15;
    expected_result <= 256'h3bea8684e04a27c3a2f43bff49433632;

    @(posedge clk);

    tb_check <= 0;

    @(posedge clk);

    if (errors_seen == 0) begin
      $display("Test PASS");
      $finish();
    end

  end

  assign error = tb_check && (rf_rd_data_a != expected_result);

  always @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
      errors_seen <= '0;
    end if(error) begin
      $display("Error seen at %t, expected %x, saw %x", $time(), expected_result, rf_rd_data_a);
      errors_seen <= errors_seen + 1'b1;
    end
  end

  otbn_mock otbn_mock_i (
    .clk_i            ( clk            ),
    .rst_ni           ( rst_n          ),

    .rf_rd_addr_a_i   ( rf_rd_addr_a   ),
    .rf_rd_addr_b_i   ( rf_rd_addr_b   ),

    .rf_wr_addr_i     ( rf_wr_addr     ),
    .rf_wr_en_i       ( rf_wr_en       ),
    .rf_wr_data_i     ( rf_wr_data     ),
    .rf_wr_data_sel_i ( rf_wr_data_sel ),

    .shift_left_i     ( shift_left     ),
    .shift_amt_i      ( shift_amt      ),
    .shift_en_i       ( shift_en       ),

    .a_qw_sel_i       ( a_qw_sel       ),
    .b_qw_sel_i       ( b_qw_sel       ),

    .pre_acc_shift_i  ( pre_acc_shift  ),

    .imm_i            ( imm            ),
    .imm_sel_i        ( imm_sel        ),

    .zero_acc_i       ( zero_acc       ),
    .mac_en_i         ( mac_en         ),
    .mul_en_i         ( mul_en         ),
    .acc_shift_out_i  ( acc_shift_out  ),
    .add_en_i         ( add_en         ),
    .sub_en_i         ( sub_en         ),
    .psuedo_mod_i     ( pseudo_mod     ),

    .mod_wr_data_i    ( mod_wr_data    ),
    .mod_wr_en_i      ( mod_wr_en      ),

    .rf_rd_data_a_o   ( rf_rd_data_a   ),
    .rf_rd_data_b_o   ( rf_rd_data_b   )
  );
endmodule
