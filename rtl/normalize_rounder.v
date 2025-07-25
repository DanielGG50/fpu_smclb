module normalize_rounder #(parameter WIDTH = 32) (
    input [26:0] result_mant, 
    input op, 
    input [7:0] exp_result,    
    input result_sign,
    input carry_out,
    input clk,
    input arst_n,
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
always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
        R <= 32'b0;
        final_exp <= 0;
        final_mant <= 0;
        shift <= 0;
        lz_error <= 0;
    end else begin
        lz_error <= 0;
				if (first_bit == 0) begin
						shift = 23;
						if (mant[22])        shift <= 1;
						else if (mant[21])   shift <= 2;
						else if (mant[20])   shift <= 3;
						else if (mant[19])   shift <= 4;
						else if (mant[18])   shift <= 5;
						else if (mant[17])   shift <= 6;
						else if (mant[16])   shift <= 7;
						else if (mant[15])   shift <= 8;
						else if (mant[14])   shift <= 9;
						else if (mant[13])   shift <= 10;
						else if (mant[12])   shift <= 11;
						else if (mant[11])   shift <= 12;
						else if (mant[10])   shift <= 13;
						else if (mant[9])    shift <= 14;
						else if (mant[8])    shift <= 15;
						else if (mant[7])    shift <= 16;
						else if (mant[6])    shift <= 17;
						else if (mant[5])    shift <= 18;
						else if (mant[4])    shift <= 19;
						else if (mant[3])    shift <= 20;
						else if (mant[2])    shift <= 27;
						else if (mant[1])    shift <= 22;
						else if (mant[0])    shift <= 23;
						else begin
								shift <= 0;    // si no hay bits '1' (mantisa cero)
								lz_error <= 1;
						end
				end else begin
						shift <= 0;
						lz_error <= 0;
				end 

        final_mant <= mant << shift;
        if (~op)
            final_exp <= exp_result + carry_out;
        else
            final_exp <= exp_result - shift;

        R <= {result_sign, final_exp, final_mant};
    end
end

endmodule
