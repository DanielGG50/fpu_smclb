module  exponent_sub #(parameter EXP_WIDTH = 8)(    // Module that represents the EXP_WIDTH subtractor block
    input [EXP_WIDTH-1: 0] exp_a, exp_b,
    output reg [4:0] shift_spaces,
    input sign_a, sign_b,
    output reg [1:0] exp_disc,
    output reg [EXP_WIDTH-1:0] exp_value, 
    input operation_select  
);    

    wire a_greater, a_less, a_equal;
    wire update_sign_b;

    assign a_greater = (exp_a > exp_b);        // Compare
    assign a_less = (exp_a < exp_b);           // Imput 
    assign a_equal = (exp_a == exp_b);         // Exponents

    assign update_sign_b = sign_b ^ operation_select;

    always @(*) begin                        // Determins output case
        exp_disc = a_greater ? 2'b10 : 
        a_less ? 2'b00 : 2'b11; 
    end
    
    always @(*) begin
        exp_value = (a_greater || a_equal) ? exp_a : exp_b;    // Outputs greater exponent
    end         

    always @(*) begin
        shift_spaces = a_greater ? exp_a - exp_b : a_less ? exp_b - exp_a : 5'b00000;
    end 
    
endmodule 
