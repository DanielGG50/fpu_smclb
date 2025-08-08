module add_sub_main_fv #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)(
	input [WIDTH-1:0] a,	
	input [WIDTH-1:0] b,
	input operation_select,
	input clk,
	input arst_n,
	input [WIDTH-1:0] R
);

  // Specific Values
  localparam POS_INF = 32'h7F800000;
  localparam POS_ZERO = 32'h00000000;
  localparam NEG_ZERO = 32'h80000000;
  localparam NEG_INF = 32'hFF800000;
  localparam CAN_NAN = 32'h7fC00000;

	parameter RSLT_DLY = 5;

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	initial begin
		a =0;
		b = 0;
	end

	function automatic bit [WIDTH-1:0] calculate_shortreal_sum(input bit [WIDTH-1:0] a, b);
  	shortreal shortreal_a, shortreal_b, shortreal_R;
  	shortreal_a = $bitstoshortreal(a);
  	shortreal_b = $bitstoshortreal(b);
  	shortreal_R = shortreal_a + shortreal_b;
  	return $shortrealtobits(shortreal_R);
	endfunction

	logic [WIDTH-1:0] R_function;
/*
	initial forever begin
  	@(posedge clk);
    R_function = calculate_shortreal_sum(a, b);
	end
*/

	// Normal inputs 
	`AST(fpu, add_normal_inputs, ((a[30:23] != 8'h00) && (a[30:23] != 8'hFF) && (b[30:23] != 8'h00) && (b[30:23] != 8'hFF) && (~operation_select)), |-> ##RSLT_DLY R == $past(R_function, RSLT_DLY))


	// EXCEPTIONS 
		// NaN
	`AST(fpu, input_nan, ( ((a[30:23] == 8'hFF) && (a[22:0] != 0)) || ((b[30:23] == 8'hFF) && (b[22:0] != 0)) ) |->, ##(RSLT_DLY) R == CAN_NAN)

		// Both a & B zero
	`AST(fpu, inputs_eq_zero, a[30:0] == 0 && b[30:0] == 0 |->, ##(RSLT_DLY) (R[30:0] == 0) && (R[31] == ($past(a[31], RSLT_DLY) & $past(b[31], RSLT_DLY))))
  	
		// Sub
  			// Infinites
  `AST(sub, pinf_min_pinf, ((operation_select == 1'b1) && (a == POS_INF) && (b == POS_INF)) |->, ##RSLT_DLY R == CAN_NAN)
  `AST(sub, pinf_min_ninf, ((operation_select == 1'b1) && (a == POS_INF) && (b == NEG_INF)) |->, ##RSLT_DLY R == POS_INF)
  `AST(sub, ninf_min_ninf, ((operation_select == 1'b1) && (a == NEG_INF) && (b == NEG_INF)) |->, ##RSLT_DLY R == CAN_NAN)
  `AST(sub, ninf_min_pinf, ((operation_select == 1'b1) && (a == NEG_INF) && (b == POS_INF)) |->, ##RSLT_DLY R == NEG_INF)
  			// finites
  `AST(sub, pinf_min_fin,  ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_INF)) |->, ##RSLT_DLY R == POS_INF)
  `AST(sub, ninf_min_fin,  ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == NEG_INF)) |->, ##RSLT_DLY R == NEG_INF)
  `AST(sub, fin_min_pinf,  ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == POS_INF)) |->, ##RSLT_DLY R == NEG_INF)
  `AST(sub, fin_min_ninf,  ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == NEG_INF)) |->, ##RSLT_DLY R == POS_INF)
			// Zeros
  `AST(sub, fin_min_zero, ((operation_select == 1'b1) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b[30:0] == 0)) |->, ##RSLT_DLY R == $past(a, RSLT_DLY))
  `AST(sub, zero_min_fin, ((operation_select == 1'b1) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_ZERO)) |->, ##RSLT_DLY (R[30:0] == $past(b[30:0], RSLT_DLY) && R[31] == !($past(b[31], RSLT_DLY))))

	  		// Add
  			// Infinites
  `AST(add, pinf_pls_pinf, ((operation_select == 1'b0) && (a == POS_INF) && (b == POS_INF)) |->, ##(RSLT_DLY) R == POS_INF)
  `AST(add, pinf_pls_ninf, ((operation_select == 1'b0) && (a == POS_INF) && (b == NEG_INF)) |->, ##(RSLT_DLY) R == CAN_NAN)
  `AST(add, ninf_pls_ninf, ((operation_select == 1'b0) && (a == NEG_INF) && (b == NEG_INF)) |->, ##(RSLT_DLY) R == NEG_INF)
  `AST(add, ninf_pls_pinf, ((operation_select == 1'b0) && (a == NEG_INF) && (b == POS_INF)) |->, ##(RSLT_DLY) R == CAN_NAN)
  			// finites
  `AST(add, pinf_pls_fin,  ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_INF)) |->, ##(RSLT_DLY) R == POS_INF)
  `AST(add, ninf_pls_fin,  ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == NEG_INF)) |->, ##(RSLT_DLY) R == NEG_INF)
  `AST(add, fin_pls_pinf,  ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == POS_INF)) |->, ##(RSLT_DLY) R == POS_INF)
  `AST(add, fin_pls_ninf,  ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b == NEG_INF)) |->, ##(RSLT_DLY) R == NEG_INF)
			// Zeros
  `AST(add, fin_pls_zero, ((operation_select == 1'b0) && ((a[30:23] < 8'hFF) && (a[22:0] > 0)) && (b[30:0] == 0)) |->, ##(RSLT_DLY) R == $past(a, RSLT_DLY))
  `AST(add, zero_pls_fin, ((operation_select == 1'b0) && ((b[30:23] < 8'hFF) && (b[22:0] > 0)) && (a == POS_ZERO)) |->, ##(RSLT_DLY) R == $past(b, RSLT_DLY))

endmodule

bind add_sub_main add_sub_main_fv add_sub_main_i (.*);
