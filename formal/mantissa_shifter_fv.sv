module mantissa_shifter_fv #(parameter MANTISSA_WIDTH=23)(
	input clk,
	input arst_n,	
	input [MANTISSA_WIDTH-1:0] ma,
	input [MANTISSA_WIDTH-1:0] mb,
	input [4:0] shift_spaces,
	input [1:0] exp_magnitude,
	input [MANTISSA_WIDTH+3:0] mantissa_a_out,
	input [MANTISSA_WIDTH+3:0] mantissa_b_out
);

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	localparam AGREATER = 2'b10;
	localparam BGREATER = 2'b00;
	localparam EQUAL = 2'b11;

	wire operand_a, operand_b;

	assign operand_a = {1'b1, ma, 3'b0};  // Addition of leading, guard, round and sticky bits
	assign operand_b = {1'b1, mb, 3'b0};  // Addition of leading, guard, round and sticky bits


	`AST(shifter, a_greater, exp_magnitude == AGREATER |=>, (mantissa_a_out == $past(operand_a)) )
	`AST(shifter, b_greater, exp_magnitude == BGREATER |=>, (mantissa_b_out == $past(operand_b)) ) 
	`AST(shifter, a_b_equal, exp_magnitude == EQUAL |=>, (mantissa_a_out == $past(operand_a)) )

endmodule

bind mantissa_shifter mantissa_shifter_fv mantissa_shifter_fv_i (.*);
