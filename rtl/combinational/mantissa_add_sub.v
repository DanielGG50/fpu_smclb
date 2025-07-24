module mantissa_add_sub #(
    parameter MANTISSA_WIDTH = 23
)(
    input [MANTISSA_WIDTH+3:0] man_a, 
    input [MANTISSA_WIDTH+3:0] man_b,
    input operation_select, // 1 = suma, 0 = resta
    input ma_sign, mb_sign,
    output reg [MANTISSA_WIDTH+3:0] result,
    output carry_out
);

    // suma entera con acarreo
    wire [MANTISSA_WIDTH+4:0] full_sum;
    

    // resta de magnitudes: siempre mayor – menor
    wire [MANTISSA_WIDTH+3:0] full_diff;

    assign full_sum =  man_a + man_b;
    assign carry_out = full_sum[MANTISSA_WIDTH+4];
    assign full_diff = (man_a >= man_b) ? (man_a - man_b) : (man_b - man_a);

    always @(*) begin
        if (ma_sign ~^ (mb_sign ~^ operation_select))
            result = full_sum[MANTISSA_WIDTH+3:0];  // bajo ajuste de overflow más adelante
        else
            result = full_diff;
    end
endmodule
