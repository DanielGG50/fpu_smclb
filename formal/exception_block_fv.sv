module exception_block_fv #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23) (
  input logic clk,
  input logic arst_n, 
  input logic [WIDTH-1:0] a,
  input logic [WIDTH-1:0] b,
  input logic operation_select,
  input logic [2:0] exception_flag,
  input logic [WIDTH-2:0] copied_operand
);

  // Specific Values
  localparam CAN_NAN = 32'h7fC00000;

	localparam [2:0]
  FLAG_NONE          = 3'b000,
  FLAG_NAN           = 3'b001,
  FLAG_COPY_A        = 3'b010,
 	FLAG_COPY_B        = 3'b011,
 	FLAG_FIN_MIN_INF   = 3'b100,
  FLAG_ZERO_MIN_ZERO = 3'b101,
  FLAG_ZERO_MIN_SOME = 3'b110,
  FLAG_SUB_SAME_VAL  = 3'b111;



  `define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  `define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  `define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
  ``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

  ///////// ASSUME OPERATION ///////////////
  //`ASM(fpu, sub, , operation_select == 1'b1)
	//`ASM(fpu, add, , operation_select == 1'b0)

	`ASM(fpu, a_or_b_nan, ,((a[30:23] == (EXP_BITS**2-1)) && (a[22:0] > 0)) )

  ///////// ASSERTIONS /////////////////
  		// Both operations
				// NaNs
	`AST(fpu, input_nan, ((a[30:23] == (EXP_BITS**2-1) && a[22:0] > 0) || (b[30:23] == (EXP_BITS**2-1) && b[22:0] > 0)) |->, ##2 exception_flag == FLAG_NAN )
	
			// exception flag
	logic a_exception_value = a[30:0] == 31'h00000000 || a[30:0] == 31'h7F800000 || (a[30:23] == 255 && a[22:0] > 0);
	logic b_exception_value = b[30:0] == 31'h00000000 || b[30:0] == 31'h7F800000 || (b[30:23] == 255 && b[22:0] > 0);
  
	//`AST(fpu, exception_case_high, (a_exception_value || b_exception_value) |=>, exception_flag != 0)
	//`AST(fpu, exception_case_low, (~a_exception_value && ~b_exception_value) |=>, exception_flag == 0)
			// Both a & B zero
	//`AST(fpu, inputs_eq_zero, a[30:0] == 0 && b[30:0] == 0 |=>, exception_flag == FLAG_ZERO_MIN_ZERO)

  		// Sub
  			// Infinites
  //`AST(sub, pinf_min_pinf, ((operation_select == 1'b1) && (a == POS_INF) && (b == POS_INF)) |=>, result == CAN_NAN)
  //`AST(sub, pinf_min_ninf, ((operation_select == 1'b1) && (a == POS_INF) && (b == NEG_INF)) |=>, result == POS_INF)
  //`AST(sub, ninf_min_ninf, ((operation_select == 1'b1) && (a == NEG_INF) && (b == NEG_INF)) |=>, result == CAN_NAN)
  //`AST(sub, ninf_min_pinf, ((operation_select == 1'b1) && (a == NEG_INF) && (b == POS_INF)) |=>, result == NEG_INF)
  			// finites
  //`AST(sub, pinf_min_fin,  ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_INF)) |=>, result == POS_INF)
  //`AST(sub, ninf_min_fin,  ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == NEG_INF)) |=>, result == NEG_INF)
  //`AST(sub, fin_min_pinf,  ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == POS_INF)) |=>, result == NEG_INF)
  //`AST(sub, fin_min_ninf,  ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == NEG_INF)) |=>, result == POS_INF)
			// Zeros
  //`AST(sub, fin_min_zero, ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b[30:0] == 0)) |=>, result == $past(a))
  //`AST(sub, zero_min_fin, ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_ZERO)) |=>, (result[30:0] == $past(b[30:0]) && result[31] == !($past(b[31]))))

	  		// Add
  			// Infinites
  //`AST(add, pinf_pls_pinf, ((operation_select == 1'b0) && (a == POS_INF) && (b == POS_INF)) |=>, result == POS_INF)
  //`AST(add, pinf_pls_ninf, ((operation_select == 1'b0) && (a == POS_INF) && (b == NEG_INF)) |=>, result == CAN_NAN)
  //`AST(add, ninf_pls_ninf, ((operation_select == 1'b0) && (a == NEG_INF) && (b == NEG_INF)) |=>, result == NEG_INF)
  //`AST(add, ninf_pls_pinf, ((operation_select == 1'b0) && (a == NEG_INF) && (b == POS_INF)) |=>, result == CAN_NAN)
  			// finites
  //`AST(add, pinf_pls_fin,  ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_INF)) |=>, result == POS_INF)
  //`AST(add, ninf_pls_fin,  ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == NEG_INF)) |=>, result == NEG_INF)
  //`AST(add, fin_pls_pinf,  ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == POS_INF)) |=>, result == POS_INF)
  //`AST(add, fin_pls_ninf,  ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == NEG_INF)) |=>, result == NEG_INF)
			// Zeros
  //`AST(add, fin_pls_zero, ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b[30:0] == 0)) |=>, result == $past(a))
  //`AST(add, zero_pls_fin, ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_ZERO)) |=>, result == $past(b))

endmodule

bind exception_block exception_block_fv fv_exception_block_i (.*);

