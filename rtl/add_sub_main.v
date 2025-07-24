module add_sub_main #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)(
    input [WIDTH-1:0] a,
    input [WIDTH-1:0] b,
    input operation_select,
    input clk,
    input reset,
    output [WIDTH-1:0] result
);

    //reg a_greater;
    wire carry_out;
    wire [4:0] shift_spaces;
    wire [MANT_BITS+3:0] mantissa_a_shifted; 
    wire [MANT_BITS+3:0] mantissa_b_shifted; 
    wire [MANT_BITS+3:0] mantissa_result_shifted;
    wire [MANT_BITS-1:0] mantissa_result;
    wire [EXP_BITS-1:0] exp_result;
    wire [1:0] exp_disc;
    wire sign_result;

    wire sign_a;
    assign sign_a = a[31];          // asignación bit de signo a

    wire sign_b;
    assign sign_b = b[31];          // asignación bit de signo b

    wire [MANT_BITS-1:0] mantissa_a;
    assign mantissa_a = a[22:0];    // asignación de mantisa a

    wire [MANT_BITS-1:0] mantissa_b;
    assign mantissa_b = b[22:0];    // asignación de mantisa b

    wire [EXP_BITS-1:0] exp_a; 
    assign exp_a = a[30:23];        // asignación de exponente a

    wire [EXP_BITS-1:0] exp_b;
    assign exp_b = b[30:23];        // asignación de exponente b




    sign_logic #(WIDTH) sign_ins ( 
        .sign_a(sign_a),
        .sign_b(sign_b),
        .mantissa_a(mantissa_a),
        .mantissa_b(mantissa_b),
        .exp_a(exp_a),
        .exp_b(exp_b),
        .operation_select(operation_select),
        .sign_r(sign_result)
    );


    // TODO add exception_block instance here


    exponent_sub_upd #(.EXP_WIDTH(EXP_BITS)) exp_ins  ( 
        .exp_a(exp_a),
        .exp_b(exp_b),
        .exp_disc(exp_disc),
        .sign_a(sign_a),
        .sign_b(sign_b),
        .exp_value(exp_result),
        .shift_spaces(shift_spaces),
        .operation_select(operation_select)
    );

    mantissa_shifter #(.MANTISSA_WIDTH(MANT_BITS)) mantissa_shifter_ins ( 
        .ma(mantissa_a),
        .mb(mantissa_b),
        .shift_spaces(shift_spaces),
        .exp_magnitude(exp_disc),
        .mantissa_a_out(mantissa_a_shifted),
        .mantissa_b_out(mantissa_b_shifted)
    );

    mantissa_add_sub #(.MANTISSA_WIDTH(MANT_BITS)) mantissa_add_sub_ins ( 
        .man_a(mantissa_a_shifted),
        .man_b(mantissa_b_shifted),
        .ma_sign(sign_a),
        .mb_sign(sign_b),
        .operation_select(operation_select),
        .result(mantissa_result_shifted),
        .carry_out(carry_out)
    );

    normalize_rounder #(.WIDTH(WIDTH)) normalize_rounder_inst ( 
        .result_mant(mantissa_result_shifted),
        .op(operation_select),
        .exp_result(exp_result),
        .result_sign(sign_result),
        .carry_out(carry_out),
        .R(result),
        .clk(clk),
        .reset(reset)
    );
    
endmodule
