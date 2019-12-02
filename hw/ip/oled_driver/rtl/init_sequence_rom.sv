module init_sequence_rom
(
  input                        clka,
  input        [3:0]           addra,
  output logic [15:0]          douta
);
  logic [15:0] douta_d;

  always_comb begin
    douta_d = '0;

    case(addra)
      4'd0:  douta_d = 16'h1901;
      4'd1:  douta_d = 16'h51ae;
      4'd2:  douta_d = 16'h2101;
      4'd3:  douta_d = 16'h3101;
      4'd4:  douta_d = 16'h518d;
      4'd5:  douta_d = 16'h5114;
      4'd6:  douta_d = 16'h51D9;
      4'd7:  douta_d = 16'h51F1;
      4'd8:  douta_d = 16'h1264;
      4'd9:  douta_d = 16'h5081;
      4'd10: douta_d = 16'h500F;
      4'd11: douta_d = 16'h50A0;
      4'd12: douta_d = 16'h50C0;
      4'd13: douta_d = 16'h50DA;
      4'd14: douta_d = 16'h5000;
      4'd15: douta_d = 16'h50AF;
    endcase
  end

  always_ff @(posedge clka) begin
    douta <= douta_d;
  end
endmodule
