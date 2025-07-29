module exponent_sub #(parameter EXP_WIDTH = 8, MANT_WIDTH = 23)(
  input clk,
  input arst_n,
  input [EXP_WIDTH-1:0] exp_a, exp_b,
  output reg  [$clog2(MANT_WIDTH + 4)-1:0] shift_spaces,
  output reg [1:0] exp_disc,
  output reg [EXP_WIDTH-1:0] exp_value
);

  always @(posedge clk, negedge arst_n) begin
    if (!arst_n) begin
      exp_value <= 0;
      exp_disc <= 0;
      shift_spaces <= 0;
    end else begin
      // Comparación de exponentes
      if (exp_a > exp_b) begin
        exp_disc <= 2'b10;
        exp_value <= exp_a;
        shift_spaces <= (exp_a - exp_b > 31) ? 5'd31 : (exp_a - exp_b);
      end else if (exp_a < exp_b) begin
        exp_disc <= 2'b00;
        exp_value <= exp_b;
        shift_spaces <= (exp_b - exp_a > 31) ? 5'd31 : (exp_b - exp_a);
      end else begin
        exp_disc <= 2'b11;
        exp_value <= exp_a;
        shift_spaces <= 0;
      end
    end
  end

endmodule
