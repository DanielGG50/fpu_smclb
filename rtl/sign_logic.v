module sign_logic #(parameter EXP_BITS = 8, parameter MANT_BITS = 23)(
    input clk,
    input arst_n,
    input sign_a,
    input sign_b,
    input [EXP_BITS-1:0] exp_a,
    input [EXP_BITS-1:0] exp_b,
    input [MANT_BITS-1:0] mantissa_a,
    input [MANT_BITS-1:0] mantissa_b,
    input operation_select, // 0 = suma, 1 = resta
    output reg sign_r
);

    wire sign_b_op = operation_select ? ~sign_b : sign_b;

    always @(posedge clk or negedge arst_n) begin
        if (!arst_n)
            sign_r <= 0;
        else begin
            if (exp_a > exp_b)
                sign_r <= sign_a;
            else if (exp_a < exp_b)
                sign_r <= sign_b_op;
            else if (mantissa_a > mantissa_b)
                sign_r <= sign_a;
            else if (mantissa_a < mantissa_b)
                sign_r <= sign_b_op;
            else
                sign_r <= sign_a & sign_b_op;
        end
    end

endmodule

