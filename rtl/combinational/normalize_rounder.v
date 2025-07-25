module normalize_rounder #(parameter WIDTH = 32) (
    input [26:0] result_mant, 
    input op, 
    input [7:0] exp_result,    
    input result_sign,
    input carry_out,
    input clk,
    input reset,
    output reg [31:0] R        
);

    reg [7:0] final_exp;
    reg [22:0] final_mant;

    reg [4:0]shift;
    wire [22:0] mant1;
    wire [22:0] mant;
    wire [2:0] GRS;
    wire round;
    wire first_bit;
    wire [26:0] rounded_mant;

    assign rounded_mant = (carry_out & ~op) ? ({1'b1, result_mant} >> 1) : result_mant;
    assign {first_bit, mant1, GRS} = rounded_mant;
    assign round = (GRS[2] & (GRS[1] | GRS[0] | mant1[0]));
    assign mant = mant1 + round;
    
    // Normalization
    reg lz_error;
    always @(*) begin
        lz_error = 0;
        if (first_bit == 0) begin
            casex (mant)
                    {1'b0, 1'b1, 22'bx}: shift=1;
                    {1'b0, 1'b1, 21'bx}: shift=2;
                    {2'b0, 1'b1, 20'bx}: shift=3;
                    {3'b0, 1'b1, 19'bx}: shift=4;
                    {4'b0, 1'b1, 18'bx}: shift=5;
                    {5'b0, 1'b1, 17'bx}: shift=6;
                    {6'b0, 1'b1, 16'bx}: shift=7;
                    {7'b0, 1'b1, 15'bx}: shift=8;
                    {8'b0, 1'b1, 14'bx}: shift=9;
                    {9'b0, 1'b1, 13'bx}: shift=10;
                    {10'b0, 1'b1, 12'bx}: shift=11;
                    {11'b0, 1'b1, 11'bx}: shift=12;
                    {12'b0, 1'b1, 10'bx}: shift=13;
                    {13'b0, 1'b1, 9'bx}: shift=14;
                    {14'b0, 1'b1, 8'bx}: shift=15;
                    {15'b0, 1'b1, 7'bx}: shift=16;
                    {16'b0, 1'b1, 6'bx}: shift=17;
                    {17'b0, 1'b1, 5'bx}: shift=18;
                    {18'b0, 1'b1, 4'bx}: shift=19;
                    {19'b0, 1'b1, 3'bx}: shift=20;
                    {20'b0, 1'b1, 2'bx}: shift=21;
                    {21'b0, 1'b1, 1'bx}: shift=22;
                    {22'b0, 1'b1}: shift=23;
                default: begin
                    shift=0;
                    lz_error = 1;
                end
            endcase
        end else begin
            shift = 0;
        end

        final_mant = mant << shift;
        if (~op)
                final_exp = exp_result + carry_out;
            else
                final_exp = exp_result - shift;
        
        R = {result_sign, final_exp, final_mant};
    end

endmodule
