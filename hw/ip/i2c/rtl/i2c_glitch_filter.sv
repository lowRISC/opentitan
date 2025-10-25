// Code your design here


module gf(clk,rst,in_scl,in_sda,out_scl,out_sda);
  input logic clk,rst;
  input logic  in_scl,in_sda; //serial data input
  output logic out_scl,out_sda;
  
  parameter n1=5; //requirement for min number of clock cycles(for scl)
  //parameter n2=3; //for sda
  
  //define states (for scl)
  typedef enum logic [2:0] {reset_scl,idle_scl,counting_scl} type_state_scl;
  type_state_scl state_scl=reset_scl;
  type_state_scl next_state_scl=reset_scl;
  
  //state declaration (for sda)
  typedef enum logic [2:0] {reset_sda,idle_sda,counting_sda} type_state_sda;
  type_state_sda state_sda=reset_sda;
  type_state_sda next_state_sda=reset_sda;
  
  //count tracker
  logic [2:0] count1,count2;
  logic reg1,reg2; //temp reg
  
  logic sda_store;
  logic sda_valid;
  logic prev_out_scl;
  //define state values
  always_ff @(posedge clk)
    begin
      if(rst)
        begin
          state_scl<=reset_scl;
          state_sda<=reset_sda;
        end
      else
        begin
          state_scl<=next_state_scl;
          state_sda<=next_state_sda;
        end
    end
  
  
always_comb begin
  case(state_scl)
    reset_scl   : next_state_scl = idle_scl;
    idle_scl    : next_state_scl = (in_scl==1) ? counting_scl : idle_scl;
    counting_scl: begin
      if ((in_scl==reg1) && (count1==n1))
                      next_state_scl = idle_scl;   // stable → accept
      else if (in_scl!=reg1)
                      next_state_scl = idle_scl;   // unstable → reject
                    else
                      next_state_scl = counting_scl;
                  end
  endcase
end
  
  //state operation for each state in sda
  //define the operation in each state for scl
  always_ff @(posedge clk) begin
  case(state_scl)
    reset_scl: begin
      out_scl   <= 0;
      prev_out_scl<=0;
      reg1   <= 0;
      count1 <= 0;
    end
    idle_scl: begin
      if(in_scl==1)
        begin
          reg1=in_scl;
          count1<=1;
        end
      else if(in_scl==0 )
        begin
          //after checking stability for 5 clock cycles, you need to wait for n cycles to retain the actual high oulse before de-asserting the clock pulse to zero
          out_scl<=out_scl;
          count1=count1-1;
          if(count1==1)
            begin
              //after scl has been retained, check if in_sda has been stable for entire scl_high duration, if yes, restore the signal in the output of the filter, else, compress it to zero
              if(sda_store==in_sda)
                out_sda<=in_sda;
              else
                out_sda<=0;
              out_scl<=0;
            end
          reg1=0;
        end
    end
    counting_scl: begin
      if (in_scl==reg1) begin
        count1 = count1 + 1;
        if (count1>=n1)
          begin
          out_scl <= in_scl;   // update output only after stability check
          sda_store <= in_sda;
          end
      end
    end
  endcase
end
endmodule
  
  
