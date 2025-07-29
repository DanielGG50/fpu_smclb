module exception_block_fv(
  input logic clk,
  input logic arst_n, 
  input logic [31:0] a,
  input logic [31:0] b,
  input logic operation_select,
  input logic exception,
  input logic [31:0] result 
);

  // Specific Values
  localparam POS_INF = 32'h7F800000;
  localparam POS_ZERO = 32'h00000000;
  localparam NEG_ZERO = 32'h80000000;
  localparam NEG_INF = 32'hFF800000;
  localparam CAN_NAN = 32'h7fC00000;



  `define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  `define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  `define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  ///////// ASSUME OPERATION ///////////////
  //`ASM(fpu, sub, , operation_select == 1'b1)
	//`ASM(fpu, add, , operation_select == 1'b0)



  ///////// ASSERTIONS /////////////////
  		// Both operations
				// NaNs
  `AST(fpu, input_nan, ((a[30:23] == 255 && a[22:0] > 0) || (b[30:23] == 255 && b[22:0] > 0)) |=>, result == CAN_NAN)
	
			// exception flag
	logic a_exception_value = a[30:0] == 31'h00000000 || a[30:0] == 31'h7F800000 || (a[30:23] == 255 && a[22:0] > 0);
	logic b_exception_value = b[30:0] == 31'h00000000 || b[30:0] == 31'h7F800000 || (b[30:23] == 255 && b[22:0] > 0);
  
	`AST(fpu, exception_flag_high, (a_exception_value || b_exception_value) |=>, exception)
	`AST(fpu, exception_flag_low, (~a_exception_value && ~b_exception_value) |=>, ~exception)
			// Both a & B zero
	`AST(fpu, inputs_eq_zero, a[30:0] == 0 && b[30:0] == 0 |=>, (result[30:0] == 0) && (result[31] == ($past(a[31]) & $past(b[31]))))

  		// Sub
  			// Infinites
  `AST(sub, pinf_min_pinf, ((operation_select == 1'b1) && (a == POS_INF) && (b == POS_INF)) |=>, result == CAN_NAN)
  `AST(sub, pinf_min_ninf, ((operation_select == 1'b1) && (a == POS_INF) && (b == NEG_INF)) |=>, result == POS_INF)
  `AST(sub, ninf_min_ninf, ((operation_select == 1'b1) && (a == NEG_INF) && (b == NEG_INF)) |=>, result == CAN_NAN)
  `AST(sub, ninf_min_pinf, ((operation_select == 1'b1) && (a == NEG_INF) && (b == POS_INF)) |=>, result == NEG_INF)
  			// finites
  `AST(sub, pinf_min_fin,  ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_INF)) |=>, result == POS_INF)
  `AST(sub, ninf_min_fin,  ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == NEG_INF)) |=>, result == NEG_INF)
  `AST(sub, fin_min_pinf,  ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == POS_INF)) |=>, result == NEG_INF)
  `AST(sub, fin_min_ninf,  ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == NEG_INF)) |=>, result == POS_INF)
			// Zeros
  `AST(sub, fin_min_zero, ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b[30:0] == 0)) |=>, result == $past(a))
  `AST(sub, zero_min_fin, ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_ZERO)) |=>, (result[30:0] == $past(b[30:0]) && result[31] == !($past(b[31]))))

	  		// Add
  			// Infinites
  `AST(add, pinf_pls_pinf, ((operation_select == 1'b0) && (a == POS_INF) && (b == POS_INF)) |=>, result == POS_INF)
  `AST(add, pinf_pls_ninf, ((operation_select == 1'b0) && (a == POS_INF) && (b == NEG_INF)) |=>, result == CAN_NAN)
  `AST(add, ninf_pls_ninf, ((operation_select == 1'b0) && (a == NEG_INF) && (b == NEG_INF)) |=>, result == NEG_INF)
  `AST(add, ninf_pls_pinf, ((operation_select == 1'b0) && (a == NEG_INF) && (b == POS_INF)) |=>, result == CAN_NAN)
  			// finites
  `AST(add, pinf_pls_fin,  ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_INF)) |=>, result == POS_INF)
  `AST(add, ninf_pls_fin,  ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == NEG_INF)) |=>, result == NEG_INF)
  `AST(add, fin_pls_pinf,  ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == POS_INF)) |=>, result == POS_INF)
  `AST(add, fin_pls_ninf,  ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == NEG_INF)) |=>, result == NEG_INF)
			// Zeros
  `AST(add, fin_pls_zero, ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b[30:0] == 0)) |=>, result == $past(a))
  `AST(add, zero_pls_fin, ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_ZERO)) |=>, result == $past(b))

endmodule

bind exception_block exception_block_fv fv_exception_block_i (.*);

