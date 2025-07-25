module exponent_sub_fv #(parameter EXP_WIDTH = 8)(    // Module that represents the EXP_WIDTH subtractor block
	input clk,
	input arst_n,
	input [EXP_WIDTH-1: 0] exp_a, exp_b,
	input [4:0] shift_spaces,
	input [1:0] exp_disc,
	input [EXP_WIDTH-1:0] exp_value
);

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

		// Values for exp_disc
	localparam A_GREATER = 2'b10;
	localparam A_LESS = 2'b00;
	localparam A_EQUAL = 2'b11;
		// Sifting max_value
	localparam MAX_SHIFT = 2**5 -1;
		// eliminated [4:0]
	wire [EXP_WIDTH-1:0] x, y;
	assign x = exp_a - exp_b;
	assign y = exp_b - exp_a;
		
	//`AST(exp_value, a_greater, (exp_a > exp_b) |=>, (exp_disc == A_GREATER) && (exp_value == $past(exp_a)) && (shift_spaces == $past(x)) )
	//`AST(exp_value, b_greater, (exp_b > exp_a) |=>, (exp_disc == A_LESS) && (exp_value == $past(exp_b)) && (shift_spaces == $past(y)) )
	`AST(exp_value, a_b_equal, (exp_b == exp_a) |=>, (exp_disc == A_EQUAL) && (exp_value == $past(exp_a)) && (shift_spaces == 0) )
	`AST(exp_value, a_greater, (exp_a > exp_b) && (x < MAX_SHIFT) |=>, (exp_disc == A_GREATER) && (exp_value == $past(exp_a)) && (shift_spaces == $past(x)) )
	`AST(exp_value, b_greater, (exp_b > exp_a) && (y < MAX_SHIFT) |=>, (exp_disc == A_LESS) && (exp_value == $past(exp_b)) && (shift_spaces == $past(y)) )
	`AST(exp_value, a_greater_max_shift, (exp_a > exp_b) && (x >= MAX_SHIFT) |=>, (exp_disc == A_GREATER) && (exp_value == $past(exp_a)) && (shift_spaces == MAX_SHIFT) )
	`AST(exp_value, b_greater_max_shift, (exp_b > exp_a) && (y >= MAX_SHIFT) |=>, (exp_disc == A_LESS) && (exp_value == $past(exp_b)) && (shift_spaces == MAX_SHIFT) )
		
endmodule

bind exponent_sub exponent_sub_fv exponent_sub_fv_i (.*);

