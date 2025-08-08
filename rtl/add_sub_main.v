/*
module add_sub_main #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)(
    input [WIDTH-1:0] a,
    input [WIDTH-1:0] b,
    input operation_select,
    input clk,
    input arst_n,
    output [WIDTH-1:0] R
);
    // Divide inputs
    wire [EXP_BITS-1:0] a_exp = a[WIDTH-2:MANT_BITS];
    wire [EXP_BITS-1:0] b_exp = b[WIDTH-2:MANT_BITS];

    wire [MANT_BITS-1:0] a_frac = a[MANT_BITS-1:0];
    wire [MANT_BITS-1:0] b_frac = b[MANT_BITS-1:0];
    
    wire a_sign = a[WIDTH-1];
    wire b_sign = b[WIDTH-1];

    //wire operation_select_for_input_reg = operation_select;

    // Signals between exponent_sub and mantissa_shifter
    wire [4:0] shift_spaces;
    wire [1:0] exp_disc;

    // Signals between mantissa_shifter and mantissa_add_sub
    wire [MANT_BITS+3:0] mantissa_a_shifted;
    wire [MANT_BITS+3:0] mantissa_b_shifted;

    // Signals between exp_sub and normalize_rounder
    wire [EXP_BITS-1:0] exp_value;

    // Signals between Sign_logic and normalize_rounder
    wire result_sign;

    // Signals between mantissa_add_sub and normalize_rounder
    wire [MANT_BITS+3:0] mantissa_result;
    wire carry_out;

    // Signals between exception_block and select_result
    wire [2:0] exception_flag;
    wire [WIDTH-2:0] copied_operand;


    // Necessary ffs to syncronize mantissas with exponent_sub output
    wire [MANT_BITS-1:0] a_frac_dlyd;
    wire [MANT_BITS-1:0] b_frac_dlyd;

    d_ff #(.WIDTH(MANT_BITS)) in_man_shift_man_a (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_frac),
        .q(a_frac_dlyd)
    );

    d_ff #(.WIDTH(MANT_BITS)) in_man_shift_man_b (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_frac),
        .q(b_frac_dlyd)
    );

    // Necessary ffs to syncronize op_sel and signs with mantissa shifter output
    wire operation_select_dlyd_1, operation_select_dlyd_2, operation_select_dlyd_dummy;
    wire a_sign_dlyd_1, a_sign_dlyd_2;
    wire b_sign_dlyd_1, b_sign_dlyd_2;
        
        // Operation Select
    d_ff #(.WIDTH(1)) op_sel_dly_0 (
        .clk(clk),
        .arst_n(arst_n),
        .d(operation_select),
        .q(operation_select_dlyd_dummy)
    ); 

    d_ff #(.WIDTH(1)) op_sel_dly_1 (
        .clk(clk),
        .arst_n(arst_n),
        .d(operation_select_dlyd_dummy),
        .q(operation_select_dlyd_1)
    ); 

	 d_ff #(.WIDTH(1)) op_sel_dly_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(operation_select_dlyd_1),
        .q(operation_select_dlyd_2)
    );
        // A_sign
    delay_chain #(.WIDTH(1), .STAGES(2)) a_sign_dly_1_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign),
        .q(a_sign_dlyd_2)
    );

        // B Sign
    delay_chain #(.WIDTH(1), .STAGES(2)) b_sign_dly_1_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign),
        .q(b_sign_dlyd_2)
    );

    // Necessary ffs to syncronize mantissa add_sub output with op_sel and exponent with normalize rounder
    wire operation_select_dlyd_3;
    wire [EXP_BITS-1:0] exp_value_dlyd_3;

    d_ff #(.WIDTH(1)) operation_select_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(operation_select_dlyd_2),
        .q(operation_select_dlyd_3)
    );

    delay_chain #(.WIDTH(EXP_BITS), .STAGES(2)) exp_value_dly_1_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(exp_value),
        .q(exp_value_dlyd_3)
    );

    // Necessary ffs to syncronize exception and signs with select_result

    wire [2:0] exception_flag_dlyd_5;
    wire [WIDTH-2:0] copied_operand_dlyd_5;
    wire a_sign_dlyd_3, a_sign_dlyd_4, a_sign_dlyd_5;
    wire b_sign_dlyd_3, b_sign_dlyd_4, b_sign_dlyd_5;

        // Exception flag 
    delay_chain #(.WIDTH(3), .STAGES(4)) exception_flag_dly (
        .clk(clk),
        .arst_n(arst_n),
        .d(exception_flag),
        .q(exception_flag_dlyd_5)
    );

        // Copied operand
    delay_chain #(.WIDTH(WIDTH-1), .STAGES(4)) copied_operand_dly (
        .clk(clk),
        .arst_n(arst_n),
        .d(copied_operand),
        .q(copied_operand_dlyd_5)
    );

        // A Sign
    d_ff #(.WIDTH(1)) a_sign_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign_dlyd_2),
        .q(a_sign_dlyd_3)
    );

    d_ff #(.WIDTH(1)) a_sign_dly_4 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign_dlyd_3),
        .q(a_sign_dlyd_4)
    );

    d_ff #(.WIDTH(1)) a_sign_dly_5 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign_dlyd_4),
        .q(a_sign_dlyd_5)
    );
        // B Sign
    d_ff #(.WIDTH(1)) b_sign_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign_dlyd_2),
        .q(b_sign_dlyd_3)
    );

    d_ff #(.WIDTH(1)) b_sign_dly_4 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign_dlyd_3),
        .q(b_sign_dlyd_4)
    );

    d_ff #(.WIDTH(1)) b_sign_dly_5 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign_dlyd_4),
        .q(b_sign_dlyd_5)
    );

    // Exception block module
    exception_block #(.WIDTH(WIDTH), .EXP_BITS(EXP_BITS), .MANT_BITS(MANT_BITS)) except_inst (
        .clk(clk),
        .arst_n(arst_n),
        .a(a),
        .b(b),
        .operation_select(operation_select), // Used dummy register
        .exception_flag(exception_flag),
        .copied_operand(copied_operand)
    );

    // Sign Logic module
    sign_logic sign_logic_inst (
        .clk(clk),
        .arst_n(arst_n),
        .sign_a(a_sign),
        .sign_b(b_sign),
        .exp_a(a_exp),
        .exp_b(b_exp),
        .mantissa_a(a_frac),
        .mantissa_b(b_frac),
        .operation_select(operation_select),
        .sign_r(result_sign)
    );

    wire result_sign_dlyd_2, result_sign_dlyd_3;
    // Necessary ff_s to syncronize sign logic with normalize rounder
    d_ff #(.WIDTH(1)) result_sign_dly_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(result_sign),
        .q(result_sign_dlyd_2)
    );
    
      d_ff #(.WIDTH(1)) result_sign_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(result_sign_dlyd_2),
        .q(result_sign_dlyd_3)
    );      
    
    // Exponent sub module
    exponent_sub #(.EXP_WIDTH(EXP_BITS), .MANT_WIDTH(MANT_BITS)) exp_sub_inst (
        .clk(clk),
        .arst_n(arst_n),
        .exp_a(a_exp),
        .exp_b(b_exp),
        .shift_spaces(shift_spaces),
        .exp_disc(exp_disc),
        .exp_value(exp_value)
    );

    // Mantissa shifter module
    mantissa_shifter #(.MANTISSA_WIDTH(MANT_BITS)) man_shift_inst (
        .clk(clk),
        .arst_n(arst_n),
        .ma(a_frac_dlyd),
        .mb(b_frac_dlyd),
        .shift_spaces(shift_spaces),
        .exp_disc(exp_disc),
        .mantissa_a_out(mantissa_a_shifted),
        .mantissa_b_out(mantissa_b_shifted)
    );

    mantissa_add_sub #(.MANTISSA_WIDTH(MANT_BITS)) mant_add_sub_inst (
        .clk(clk),
        .arst_n(arst_n),
        .man_a(mantissa_a_shifted),
        .man_b(mantissa_b_shifted),
        .operation_select(operation_select_dlyd_2),
        .ma_sign(a_sign_dlyd_2),
        .mb_sign(b_sign_dlyd_2),
        .result(mantissa_result),
        .carry_out(carry_out)
    );

    // Normalize and rounder module
    wire [WIDTH-1:0] normal_result;

    normalize_rounder #(.WIDTH(WIDTH)) norm_round_inst (
        .result_mant(mantissa_result),
        .op(operation_select_dlyd_3),
        .exp_result(exp_value_dlyd_3),
        .a_sign(a_sign_dlyd_3), 
        .b_sign(b_sign_dlyd_3),
        .a_sign_scnd(a_sign_dlyd_4), // Another delay because goes into secons stage
        .b_sign_scnd(b_sign_dlyd_4),
        .result_sign(result_sign_dlyd_3),
        .carry_out(carry_out),
        .clk(clk),
        .arst_n(arst_n),
        .R(normal_result)
    );

    // Select result module
    select_result #(.WIDTH(WIDTH)) sel_result_inst (
        .R_normal(normal_result),
        .exception_flag(exception_flag_dlyd_5),
        .sign_a(a_sign_dlyd_5),
        .sign_b(b_sign_dlyd_5),
        .copied_operand(copied_operand_dlyd_5),
        .R(R)
    );

endmodule
*/

module add_sub_main #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)(
    input en,
    input [WIDTH-1:0] a,
    input [WIDTH-1:0] b,
    input operation_select,
    input clk,
    input arst_n,
    output [WIDTH-1:0] data_reg_c//R
);

    wire [WIDTH-1:0] R;

    wire [WIDTH-1:0] a_en, b_en;

    assign a_en = en ? a : 0;
    assign b_en = en ? b : 0;

    // Divide inputs
    wire [EXP_BITS-1:0] a_exp = a_en[WIDTH-2:MANT_BITS];
    wire [EXP_BITS-1:0] b_exp = b_en[WIDTH-2:MANT_BITS];

    wire [MANT_BITS-1:0] a_frac = a_en[MANT_BITS-1:0];
    wire [MANT_BITS-1:0] b_frac = b_en[MANT_BITS-1:0];

    wire a_sign = a_en[WIDTH-1];
    wire b_sign = b_en[WIDTH-1];

    //wire operation_select_for_input_reg = operation_select;

    // Signals between exponent_sub and mantissa_shifter
    wire [4:0] shift_spaces;
    wire [1:0] exp_disc;

    // Signals between mantissa_shifter and mantissa_add_sub
    wire [MANT_BITS+3:0] mantissa_a_shifted;
    wire [MANT_BITS+3:0] mantissa_b_shifted;

    // Signals between exp_sub and normalize_rounder
    wire [EXP_BITS-1:0] exp_value;

    // Signals between Sign_logic and normalize_rounder
    wire result_sign;

    // Signals between mantissa_add_sub and normalize_rounder
    wire [MANT_BITS+3:0] mantissa_result;
    wire carry_out;

    // Signals between exception_block and select_result
    wire [2:0] exception_flag;
    wire [WIDTH-2:0] copied_operand;

    // Signals between normalize rounder and select result
    wire [WIDTH-1:0] normal_result;

    // Necessary ffs to syncronize mantissas with exponent_sub output
    wire [MANT_BITS-1:0] a_frac_dlyd;
    wire [MANT_BITS-1:0] b_frac_dlyd;

    d_ff #(.WIDTH(MANT_BITS)) in_man_shift_man_a (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_frac),
        .q(a_frac_dlyd)
    );

    d_ff #(.WIDTH(MANT_BITS)) in_man_shift_man_b (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_frac),
        .q(b_frac_dlyd)
    );

    // Necessary ffs to syncronize op_sel and signs with mantissa shifter output
    wire operation_select_dlyd_2;
    wire a_sign_dlyd_1, a_sign_dlyd_2;
    wire b_sign_dlyd_1, b_sign_dlyd_2;
        
        // Operation Select
    delay_chain #(.WIDTH(1), .STAGES(2)) op_sel_dly (
        .clk(clk),
        .arst_n(arst_n),
        .d(operation_select), /// changed input_reg 
        .q(operation_select_dlyd_2)
    );

        // A_sign
    delay_chain #(.WIDTH(1), .STAGES(2)) a_sign_dly_1_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign),
        .q(a_sign_dlyd_2)
    );

        // B Sign
    delay_chain #(.WIDTH(1), .STAGES(2)) b_sign_dly_1_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign),
        .q(b_sign_dlyd_2)
    );

    // Necessary ffs to syncronize mantissa add_sub output with op_sel and exponent with normalize rounder
    wire operation_select_dlyd_3;
    wire [EXP_BITS-1:0] exp_value_dlyd_3;

    d_ff #(.WIDTH(1)) operation_select_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(operation_select_dlyd_2),
        .q(operation_select_dlyd_3)
    );

    delay_chain #(.WIDTH(EXP_BITS), .STAGES(2)) exp_value_dly_1_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(exp_value),
        .q(exp_value_dlyd_3)
    );

    // Necessary ffs to syncronize exception and signs with select_result

    wire [2:0] exception_flag_dlyd_5;
    wire [WIDTH-2:0] copied_operand_dlyd_5;
    wire a_sign_dlyd_3, a_sign_dlyd_4, a_sign_dlyd_5;
    wire b_sign_dlyd_3, b_sign_dlyd_4, b_sign_dlyd_5;

        // Exception flag 
    wire exception_flag_dlyd_1;

    delay_chain #(.WIDTH(3), .STAGES(4)) exception_flag_dly (
        .clk(clk),
        .arst_n(arst_n),
        .d(exception_flag),
        .q(exception_flag_dlyd_5)
    );

        // Copied operand
    delay_chain #(.WIDTH(WIDTH-1), .STAGES(4)) copied_operand_dly (
        .clk(clk),
        .arst_n(arst_n),
        .d(copied_operand),
        .q(copied_operand_dlyd_5)
    );

        // A Sign
    d_ff #(.WIDTH(1)) a_sign_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign_dlyd_2),
        .q(a_sign_dlyd_3)
    );

    d_ff #(.WIDTH(1)) a_sign_dly_4 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign_dlyd_3),
        .q(a_sign_dlyd_4)
    );

    d_ff #(.WIDTH(1)) a_sign_dly_5 (
        .clk(clk),
        .arst_n(arst_n),
        .d(a_sign_dlyd_4),
        .q(a_sign_dlyd_5)
    );
        // B Sign
    d_ff #(.WIDTH(1)) b_sign_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign_dlyd_2),
        .q(b_sign_dlyd_3)
    );

    d_ff #(.WIDTH(1)) b_sign_dly_4 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign_dlyd_3),
        .q(b_sign_dlyd_4)
    );

    d_ff #(.WIDTH(1)) b_sign_dly_5 (
        .clk(clk),
        .arst_n(arst_n),
        .d(b_sign_dlyd_4),
        .q(b_sign_dlyd_5)
    );

    // Necessary ff_s to syncronize sign logic with normalize rounder
    wire result_sign_dlyd_2, result_sign_dlyd_3;
    
    d_ff #(.WIDTH(1)) result_sign_dly_2 (
        .clk(clk),
        .arst_n(arst_n),
        .d(result_sign),
        .q(result_sign_dlyd_2)
    );
    
      d_ff #(.WIDTH(1)) result_sign_dly_3 (
        .clk(clk),
        .arst_n(arst_n),
        .d(result_sign_dlyd_2),
        .q(result_sign_dlyd_3)
    );      

    // Exception block module
    exception_block #(.WIDTH(WIDTH), .EXP_BITS(EXP_BITS), .MANT_BITS(MANT_BITS)) except_inst (
        .clk(clk),
        .arst_n(arst_n),
        .a(a_en),
        .b(b_en),
        .operation_select(operation_select), // changed wire
        .exception_flag(exception_flag),
        .copied_operand(copied_operand)
    );

    // Sign Logic module
    sign_logic sign_logic_inst (
        .clk(clk),
        .arst_n(arst_n),
        .sign_a(a_sign),
        .sign_b(b_sign),
        .exp_a(a_exp),
        .exp_b(b_exp),
        .mantissa_a(a_frac),
        .mantissa_b(b_frac),
        .operation_select(operation_select),
        .sign_r(result_sign)
    );
    
    // Exponent sub module
    exponent_sub #(.EXP_WIDTH(EXP_BITS)) exp_sub_inst (
        .clk(clk),
        .arst_n(arst_n),
        .exp_a(a_exp),
        .exp_b(b_exp),
        .shift_spaces(shift_spaces),
        .exp_disc(exp_disc),
        .exp_value(exp_value)
    );

    // Mantissa shifter module
    mantissa_shifter #(.MANTISSA_WIDTH(MANT_BITS)) man_shift_inst (
        .clk(clk),
        .arst_n(arst_n),
        .ma(a_frac_dlyd),
        .mb(b_frac_dlyd),
        .shift_spaces(shift_spaces),
        .exp_disc(exp_disc),
        .mantissa_a_out(mantissa_a_shifted),
        .mantissa_b_out(mantissa_b_shifted)
    );

    // mantissa add sub module
    mantissa_add_sub #(.MANTISSA_WIDTH(MANT_BITS)) mant_add_sub_inst (
        .clk(clk),
        .arst_n(arst_n),
        .man_a(mantissa_a_shifted),
        .man_b(mantissa_b_shifted),
        .operation_select(operation_select_dlyd_2),
        .ma_sign(a_sign_dlyd_2),
        .mb_sign(b_sign_dlyd_2),
        .result(mantissa_result),
        .carry_out(carry_out)
    );

    // Normalize and rounder module
    normalize_rounder #(.WIDTH(WIDTH)) norm_round_inst (
        .result_mant(mantissa_result),
        .op(operation_select_dlyd_3),
        .exp_result(exp_value_dlyd_3),
        .a_sign(a_sign_dlyd_3), 
        .b_sign(b_sign_dlyd_3),
        .a_sign_scnd(a_sign_dlyd_4), // Another delay because goes into second stage
        .b_sign_scnd(b_sign_dlyd_4),
        .result_sign(result_sign_dlyd_3),
        .carry_out(carry_out),
        .clk(clk),
        .arst_n(arst_n),
        .R(normal_result)
    );

    // Select result module
    select_result #(.WIDTH(WIDTH)) sel_result_inst (
        .R_normal(normal_result),
        .exception_flag(exception_flag_dlyd_5),
        .sign_a(a_sign_dlyd_5),
        .sign_b(b_sign_dlyd_5),
        .copied_operand(copied_operand_dlyd_5),
        .R(R)
    );

    // shift register
    reg [WIDTH-1:0] data_reg_c_r;
    reg [4:0] en_r;

    always @(posedge clk or negedge arst_n) begin
        if(!arst_n)
            en_r <= 5'd0;
        else
            en_r <= {en_r[3:0], en};
    end
 
    always @(posedge clk or negedge arst_n) begin
        if(!arst_n)
            data_reg_c_r <= 5'd0;
        else
            if(en_r[4])
                data_reg_c_r <= R;
	end

	assign data_reg_c = data_reg_c_r;
 
endmodule
