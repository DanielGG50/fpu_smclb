module  exponent_sub #(parameter EXP_WIDTH = 8)(    // Module that represents the EXP_WIDTH subtractor block
input [EXP_WIDTH-1: 0] exp_a, exp_b,
input [4:0] shift_spaces,
input sign_a, sign_b,
input [1:0] exp_disc,
input [EXP_WIDTH-1:0] exp_value,
input operation_select
);

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

endmodule

bind exponent_sub_fv exponent_sub exponent_sub_fv_i (.*);

