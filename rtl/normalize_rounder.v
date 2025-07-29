/*module normalize_rounder #(parameter WIDTH = 32) (
    input [26:0] result_mant, 
    input op, 
    input [7:0] exp_result,    
    input result_sign,
    input a_sign,
    input b_sign,
    input carry_out,
    input clk,
    input arst_n,
    output [2:0] GRS,
    output [31:0] R        
);

    reg result_sign_reg_1;
    reg [26:0] result_mant_reg;
    reg op_reg;
    reg [7:0] exp_result_reg;
    reg result_sign_reg;
    reg carry_out_reg;

    reg [4:0]shift;
    reg [7:0] final_exp;
    reg [22:0] final_mant;
    wire [22:0] mant1;
    wire [22:0] mant;
    wire [2:0] GRS;
    wire round;
    wire first_bit;
    wire [26:0] rounded_mant;
    reg lz_error;

    assign rounded_mant = (carry_out & ~op) ? ({1'b1, result_mant} >> 1) : result_mant;
    assign {first_bit, mant1, GRS} = rounded_mant;
    assign round = (GRS[2] & (GRS[1] | GRS[0] | mant1[0]));
    assign mant = mant1 + round;

    always @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            lz_error <= 0;
            shift <= 0;
            result_sign_reg_1 <= 0;
            result_mant_reg <= 0;
            op_reg <= 0;
            exp_result_reg <= 0;
            carry_out_reg <= 0;
        end else begin
            if (first_bit == 0) begin
                if (mant[22]) shift <= 1;
                else if (mant[21]) shift <= 2;
                else if (mant[20]) shift <= 3;
                else if (mant[19]) shift <= 4;
                else if (mant[18]) shift <= 5;
                else if (mant[17]) shift <= 6;
                else if (mant[16]) shift <= 7;
                else if (mant[15]) shift <= 8;
                else if (mant[14]) shift <= 9;
                else if (mant[13]) shift <= 10;
                else if (mant[12]) shift <= 11;
                else if (mant[11]) shift <= 12;
                else if (mant[10]) shift <= 13;
                else if (mant[9]) shift <= 14;
                else if (mant[8]) shift <= 15;
                else if (mant[7]) shift <= 16;
                else if (mant[6]) shift <= 17;
                else if (mant[5]) shift <= 18;
                else if (mant[4]) shift <= 19;
                else if (mant[3]) shift <= 20;
                else if (mant[2]) shift <= 21;
                else if (mant[1]) shift <= 22;
                else if (mant[0]) shift <= 23;
                else begin
                    shift <= 0;
                    lz_error <= 1; // No significant bits found
                end
            end    
        end
        result_mant_reg <= mant;
        op_reg <= op;
        exp_result_reg <= exp_result;
        result_sign_reg_1 <= result_sign;
        carry_out_reg <= carry_out;

    end

    always @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            final_mant <= 0;
            final_exp <= 0;
            result_sign_reg <= 0;
        end else begin
            final_mant <= result_mant_reg << shift;
            if (a_sign ~^ (b_sign ^ op_reg)) begin
                final_exp <= exp_result_reg + carry_out_reg;
            end else begin
                final_exp <= exp_result_reg - shift;
            end
            result_sign_reg <= result_sign_reg_1;
        end
    end

    assign R = {result_sign_reg, final_exp, final_mant};

endmodule*/

module normalize_rounder #(parameter WIDTH = 32) (
    input [26:0] result_mant, 
    input op, 
    input [7:0] exp_result,    
    input result_sign,
    input a_sign,
    input b_sign,
    input a_sign_scnd,
    input b_sign_scnd,
    input carry_out,
    input clk,
    input arst_n,
    output [2:0] GRS,
    output [31:0] R        
);

    reg result_sign_reg_1;
    reg [26:0] result_mant_reg;
    reg op_reg;
    reg [7:0] exp_result_reg;
    reg result_sign_reg;
    reg carry_out_reg;

    reg [4:0]shift;
    reg [7:0] final_exp;
    reg [22:0] final_mant;
    wire [22:0] mant1;
    wire [22:0] mant;
    wire [2:0] GRS;
    wire round;
    wire first_bit;
    wire [26:0] rounded_mant;
    reg lz_error;

    assign rounded_mant = (carry_out & ((a_sign ~^ (b_sign ^ op)))) ? ({1'b1, result_mant} >> 1) : result_mant;
    assign {first_bit, mant1, GRS} = rounded_mant;
    assign round = (GRS[2] & (GRS[1] | GRS[0] | mant1[0]));
    assign mant = mant1 + round;

    always @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            lz_error <= 0;
            shift <= 0;
        end else begin

            shift <= 0;
            if (~first_bit) begin
                if (mant[22]) shift <= 1;
                else if (mant[21]) shift <= 2;
                else if (mant[20]) shift <= 3;
                else if (mant[19]) shift <= 4;
                else if (mant[18]) shift <= 5;
                else if (mant[17]) shift <= 6;
                else if (mant[16]) shift <= 7;
                else if (mant[15]) shift <= 8;
                else if (mant[14]) shift <= 9;
                else if (mant[13]) shift <= 10;
                else if (mant[12]) shift <= 11;
                else if (mant[11]) shift <= 12;
                else if (mant[10]) shift <= 13;
                else if (mant[9]) shift <= 14;
                else if (mant[8]) shift <= 15;
                else if (mant[7]) shift <= 16;
                else if (mant[6]) shift <= 17;
                else if (mant[5]) shift <= 18;
                else if (mant[4]) shift <= 19;
                else if (mant[3]) shift <= 20;
                else if (mant[2]) shift <= 21;
                else if (mant[1]) shift <= 22;
                else if (mant[0]) shift <= 23;
                else begin
                    shift <= 0;
                    lz_error <= 1; // No significant bits found
                end
            end    
        end
    end

    always @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            result_sign_reg_1 <= 0;
            result_mant_reg <= 0;
            op_reg <= 0;
            exp_result_reg <= 0;
            carry_out_reg <= 0;
        end else begin
            result_mant_reg <= mant;
            op_reg <= op;
            exp_result_reg <= exp_result;
            result_sign_reg_1 <= result_sign;
            carry_out_reg <= carry_out;
        end
    end

    always @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            final_mant <= 0;
            final_exp <= 0;
            result_sign_reg <= 0;
        end else begin
            final_mant <= result_mant_reg << shift;
            if (a_sign_scnd ~^ (b_sign_scnd ^ op_reg)) begin
                final_exp <= exp_result_reg + carry_out_reg;
            end else begin
                final_exp <= exp_result_reg - shift;
            end
            result_sign_reg <= result_sign_reg_1;
        end
    end

    assign R = {result_sign_reg, final_exp, final_mant};

endmodule