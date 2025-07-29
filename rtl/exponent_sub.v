module exponent_sub #(parameter EXP_WIDTH = 8)(
	input clk,
	input arst_n,
	input [EXP_WIDTH-1:0] exp_a, exp_b,
	output reg [4:0] shift_spaces,
	output reg [1:0] exp_disc,
	output reg [EXP_WIDTH-1:0] exp_value
);    

	wire a_greater, a_less, a_equal;

	assign a_greater = (exp_a > exp_b);        
	assign a_less    = (exp_a < exp_b);           
 	assign a_equal   = (exp_a == exp_b);           

	always @(posedge clk or negedge arst_n) begin
  	if (!arst_n) begin
    	exp_disc      <= 2'b00;
      exp_value     <= {EXP_WIDTH{1'b0}};
      shift_spaces  <= 5'b00000;
    end else begin
      // Determinar cuál exponente usar y cuántos espacios de shift
      exp_disc <= a_greater ? 2'b10 : a_less    ? 2'b00 : 2'b11;
            
     	exp_value <= (a_greater || a_equal) ? exp_a : exp_b;

      shift_spaces <= a_greater ? (exp_a - exp_b) : a_less    ? (exp_b - exp_a) : 5'b00000;
    end
  end

endmodule
