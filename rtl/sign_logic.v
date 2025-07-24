module sign_logic #(parameter EXP_BITS = 8,parameter MANT_BITS  = 23)(
    input sign_a,
    input sign_b,
    input [7:0] exp_a,
    input [7:0] exp_b,
    input [MANT_BITS-1:0] mantissa_a,
    input [MANT_BITS-1:0] mantissa_b,
    input operation_select, // 1 = suma, 0 = resta
    output sign_r
);

    // invertimos el signo de b solo si es RESTA
    wire sign_b_op = operation_select ? sign_b : ~sign_b;
    
    // quién "gana" determina el signo resultante:
    //   - primero por exponente
    //   - luego por mantisa
    //   - en empate, ambos signos AND
    assign sign_r = (exp_a > exp_b)?sign_a :
                    (exp_a < exp_b)?sign_b_op :
                    (mantissa_a > mantissa_b) ? sign_a :
                    (mantissa_a < mantissa_b) ? sign_b_op :
                    (sign_a & sign_b_op);
endmodule
