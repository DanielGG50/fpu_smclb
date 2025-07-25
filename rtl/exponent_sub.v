module exponent_sub #(parameter EXP_WIDTH = 8)(    // Module that represents the EXP_WIDTH subtractor block
	input clk,	
	input arst_n,
	input [EXP_WIDTH-1: 0] exp_a, exp_b,
	output reg [4:0] shift_spaces,
	output reg [1:0] exp_disc,
	output reg [EXP_WIDTH-1:0] exp_value 
);    

	wire a_greater, a_less, a_equal;
	wire [EXP_WIDTH-1:0] diff = (a_greater ? exp_a - exp_b : a_less    ? exp_b - exp_a : 0);
	
	assign a_greater = (exp_a > exp_b);        // Compare
	assign a_less = (exp_a < exp_b);           // Imput 
	assign a_equal = (exp_a == exp_b);         // Exponents

	always @(*) begin                        // Determins output case
  	exp_disc_comb = a_greater ? 2'b10 : 
		a_less ? 2'b00 : 2'b11; 
	end

	always @(*) begin
		exp_value_comb = (a_greater || a_equal) ? exp_a : exp_b;    // Outputs greater exponent
	end         

	always @(*) begin
		shift_spaces_comb = (diff > 31) ? 5'd31 : diff[4:0];
	end 
   
	reg [4:0] shift_spaces_comb;
	reg [1:0] exp_disc_comb;
	reg [EXP_WIDTH-1:0] exp_value_comb;

	always @(posedge clk, negedge arst_n)
		if (!arst_n) begin
			exp_value <= 0;
			exp_disc <= 0;
			shift_spaces <= 0;	
 		end else begin
			exp_value <= exp_value_comb;
			exp_disc <= exp_disc_comb;		
			shift_spaces <= shift_spaces_comb;
		end

endmodule 
/*
module exponent_sub #(parameter EXP_WIDTH = 8)(    // Module that represents the EXP_WIDTH subtractor block
	input clk,	
	input arst_n,
	input [EXP_WIDTH-1: 0] exp_a, exp_b,
	output reg [4:0] shift_spaces,
	output reg [1:0] exp_disc,
	output reg [EXP_WIDTH-1:0] exp_value 
);    

	wire a_greater, a_less, a_equal;

	assign a_greater = (exp_a > exp_b);        // Compare
	assign a_less = (exp_a < exp_b);           // Imput 
	assign a_equal = (exp_a == exp_b);         // Exponents

	always @(*) begin                        // Determins output case
  	exp_disc_comb = a_greater ? 2'b10 : 
		a_less ? 2'b00 : 2'b11; 
	end

	always @(*) begin
		exp_value_comb = (a_greater || a_equal) ? exp_a : exp_b;    // Outputs greater exponent
	end         

	always @(*) begin
		shift_spaces_comb = a_greater ? exp_a - exp_b : a_less ? exp_b - exp_a : 5'b00000;
	end 
   
	reg [4:0] shift_spaces_comb;
	reg [1:0] exp_disc_comb;
	reg [EXP_WIDTH-1:0] exp_value_comb;

	always @(posedge clk, negedge arst_n)
		if (!arst_n) begin
			exp_value <= 0;
			exp_disc <= 0;
			shift_spaces <= 0;	
 		end else begin
			exp_value <= exp_value_comb;
			exp_disc <= exp_disc_comb;		
			shift_spaces <= shift_spaces_comb;
		end

endmodule 
*/
