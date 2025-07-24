module normalize_rounder #(parameter WIDTH = 32) (
    input [26:0] result_mant, 
    input op, 
    input [7:0] exp_result,    
    input result_sign,
    input carry_out,
    input clk,
    input reset,
    input ma_sign, mb_sign,
    output [2:0] GRS,
    output reg [8:0] e_raw,
    output reg [31:0] R        
);

    reg [7:0] final_exp = 0;
    reg [22:0] final_mant = 0;
    reg [4:0] shift = 0;
    wire [22:0] mant;
    wire first_bit;
    wire [26:0] rounded_mant;
    reg lz_error;

    assign rounded_mant = (carry_out & (ma_sign ~^ (mb_sign ~^ op))) ? ({1'b1,result_mant} >> 1) : result_mant;
    assign {first_bit,mant,GRS} = rounded_mant;

    always @(*) begin
    lz_error = 0;
    shift = 4;

    if (first_bit == 0) begin
        shift = 23;

        if (mant[22]) shift = 1;
        else if (mant[21]) shift = 2;
        else if (mant[20]) shift = 3;
        else if (mant[19]) shift = 4;
        else if (mant[18]) shift = 5;
        else if (mant[17]) shift = 6;
        else if (mant[16]) shift = 7;
        else if (mant[15]) shift = 8;
        else if (mant[14]) shift = 9;
        else if (mant[13]) shift = 10;
        else if (mant[12]) shift = 11;
        else if (mant[11]) shift = 12;
        else if (mant[10]) shift = 13;
        else if (mant[9]) shift = 14;
        else if (mant[8]) shift = 15;
        else if (mant[7]) shift = 16;
        else if (mant[6]) shift = 17;
        else if (mant[5]) shift = 18;
        else if (mant[4]) shift = 19;
        else if (mant[3]) shift = 20;
        else if (mant[2]) shift = 21;
        else if (mant[1]) shift = 22;
        else if (mant[0]) shift = 23;

        // Verificación final para resultado cero
        if (mant == 23'b0) begin
            shift = 0;
            lz_error = 1;

            // Resultado final es cero estándar en IEEE-754
            final_exp = 8'b0;
            final_mant = 23'b0;
            R = {result_sign, final_exp, final_mant};
        end else begin
            final_mant = mant << shift;
            final_exp = exp_result - shift;
            R = {result_sign, final_exp, final_mant};
        end
    end else begin
        final_mant = mant;
        if (ma_sign ~^ (mb_sign ~^ op))begin
            final_exp = exp_result + carry_out;
            e_raw = {carry_out,final_exp};
        end else begin
            final_exp = exp_result;
            e_raw = {carry_out,final_exp};    
        end 

        R = {result_sign, final_exp, final_mant};
    end
end
endmodule
