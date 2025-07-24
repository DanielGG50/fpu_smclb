module mantissa_add_sub_fv #(parameter MANTISSA_WIDTH = 23)(
	input clk,
	input arst_n,
	input [MANTISSA_WIDTH+3:0] man_a,
	input [MANTISSA_WIDTH+3:0] man_b,
	input operation_select, // 0 = suma, 1 = resta
	input ma_sign, mb_sign,
	input [MANTISSA_WIDTH+3:0] result,
	input carry_out 
);

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	logic a_greater = man_a >= man_b;
	logic a_less = man_a < man_b;



	//Add
		// Adding two numbers with same sign
			//Result
	`AST(add, add_same_signs, !operation_select && (ma_sign ==mb_sign) |=>, {carry_out, result} == $past(man_a) + $past(man_b))
	
			// Carry_out
	`AST(add, no_ovf_numeric, !operation_select && (ma_sign == mb_sign) && (man_a + man_b <= (2**(MANTISSA_WIDTH+4)-1)) |=>, !carry_out)
	`AST(add, overflow, !operation_select && (ma_sign == mb_sign) && (man_a[MANTISSA_WIDTH+3] && man_b[MANTISSA_WIDTH+3]) |=>, carry_out)
	`AST(add, ovf_numeric, !operation_select && (ma_sign == mb_sign) && (man_a + man_b > (2**(MANTISSA_WIDTH+4)-1)) |=>, carry_out)
		// Adding two_numbers with different sign
	`AST(add, add_a_greater_b_diff_sign, !operation_select && (a_greater) && (ma_sign == ~mb_sign) |=>, result == $past(man_a) - $past(man_b))
	`AST(sub, sub_b_greater_a_diff_sign, !operation_select && (a_less) && (ma_sign == ~mb_sign)  |=>, result == $past(man_b) - $past(man_a))
	// Adding two numbers with any sign comb.
	`AST(add, no_overflow, !operation_select && (!man_a[MANTISSA_WIDTH+3] && !man_b[MANTISSA_WIDTH+3]) |=>, !carry_out)
	
	// Sub
		// Subtracting two numbers with same signs
			// Carry_out
	`AST(sub, no_overflow, operation_select && (ma_sign == mb_sign) |=>, !carry_out)
	`AST(sub, ovf_numeric, operation_select && (ma_sign == ~ mb_sign) && (man_a + man_b > (2**(MANTISSA_WIDTH+4)-1)) |=>, carry_out) 
			// Result
	`AST(sub, sub_a_greater_b_same_sign, operation_select && (a_greater) && (ma_sign == mb_sign) |=>, result == $past(man_a) - $past(man_b))
	`AST(sub, sub_b_greater_a_same_sign, operation_select && (a_less) && (ma_sign == mb_sign)  |=>, result == $past(man_b) - $past(man_a))
		// Sub with diff sign
	`AST(sub, sub_diff_signs, operation_select && (ma_sign == ~mb_sign) |=>, {carry_out, result} == $past(man_a) + $past(man_b))

endmodule

bind mantissa_add_sub mantissa_add_sub_fv fv_m_add_sub_i (.*);

