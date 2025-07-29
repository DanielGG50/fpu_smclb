module select_result_fv #(parameter WIDTH = 32) (
  input [WIDTH-1:0] R_normal,
  input [2:0] exception_flag,
  input sign_a, sign_b,
  input [WIDTH-2:0] copied_operand,
  input [WIDTH-1:0] R,
	input clk, arst_n
);

	
  `define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  `define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  `define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

 




endmodule

bind select_result select_result_fv select_result_i (.*);
