module add_sub_main_fv #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)(
	input [WIDTH-1:0] a,	
	input [WIDTH-1:0] b,
	input operation_select,
	input clk,
	input arst_n,
	input [WIDTH-1:0] R
);

	parameter CAN_NAN = 32'h7FC00000;
	parameter RSLT_DLY = 5;

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`AST(fpu, input_nan, ( ((a[30:23] == 8'hFF) && (a[22:0] != 0)) || ((b[30:23] == 8'hFF) && (b[22:0] != 0)) ) |->, ##(RSLT_DLY) R == CAN_NAN)


endmodule

bind add_sub_main add_sub_main_fv add_sub_main_i (.*);
