module exception_block #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23) (
  input clk,
  input arst_n,
  input [WIDTH-1:0] a,
  input [WIDTH-1:0] b,
  input operation_select,
  output reg [2:0] exception_flag,
  output reg [WIDTH-2:0] copied_operand
);

  reg [WIDTH-1:0] a_reg, b_reg;
  reg operation_select_reg;

  always @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      a_reg <= 0;
      b_reg <= 0;
      operation_select_reg <= 0;
    end else begin
      a_reg <= a;
      b_reg <= b;
      operation_select_reg <= operation_select;
    end
  end

  // Lógica un ciclo después, usando los registros
  wire [EXP_BITS-1:0] a_exp = a_reg[WIDTH-2:MANT_BITS];
  wire [EXP_BITS-1:0] b_exp = b_reg[WIDTH-2:MANT_BITS];
  wire [MANT_BITS-1:0] a_frac = a_reg[MANT_BITS-1:0];
  wire [MANT_BITS-1:0] b_frac = b_reg[MANT_BITS-1:0];

  wire a_zero = (a_exp == 0 && a_frac == 0);
  wire b_zero = (b_exp == 0 && b_frac == 0);
  wire a_inf  = (a_exp == 8'hFF && a_frac == 0);
  wire b_inf  = (b_exp == 8'hFF && b_frac == 0);
  wire a_nan  = (a_exp == 8'hFF && a_frac != 0);
  wire b_nan  = (b_exp == 8'hFF && b_frac != 0);

  wire a_sign = a_reg[WIDTH-1];
  wire b_sign = b_reg[WIDTH-1];

  localparam [2:0]
    FLAG_NONE          = 3'b000,
    FLAG_NAN           = 3'b001,
    FLAG_COPY_A        = 3'b010,
    FLAG_COPY_B        = 3'b011,
    FLAG_FIN_MIN_INF   = 3'b100,
    FLAG_ZERO_MIN_ZERO = 3'b101,
    FLAG_ZERO_MIN_SOME = 3'b110,
    FLAG_SUB_SAME_VAL  = 3'b111;

  always @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      exception_flag <= 3'b000; // Reset exception flag
      copied_operand <= {(WIDTH-1){1'b0}}; // Reset copied operand
    end else begin  // NaNs

      exception_flag <= FLAG_NONE; // Default case
      copied_operand <= {(WIDTH-1){1'b0}}; // Default mantissa

      if (a_nan || b_nan) begin // If either is NaN
        exception_flag <= FLAG_NAN;
      
      end else if (a_inf && !b_inf) begin // Only a is Inf
        exception_flag <= FLAG_COPY_A;
        copied_operand <= {a_exp, a_frac}; // Copy mantissa of A

      end else if (b_inf && !a_inf) begin // Only b is Inf
        if (operation_select_reg) begin // A - (INF) = -INF, A - (-INF) = INF
          exception_flag <= FLAG_FIN_MIN_INF;
        end else begin // A + (INF) = INF, A + (-INF) = -INF
          exception_flag <= FLAG_COPY_B;
        copied_operand <= {b_exp, b_frac}; // Copy mantissa of B
        end
      end else if (a_zero && b_zero) begin // Both are zero
        exception_flag <= FLAG_ZERO_MIN_ZERO;
      
      end else if (a_zero) begin // Only a is zero
        if (operation_select_reg) begin
          exception_flag <= FLAG_ZERO_MIN_SOME; // 0 - B = - B
          copied_operand <= {b_exp, b_frac}; // Copy mantissa of B
        end else begin
          exception_flag <= FLAG_COPY_B; // 0 + B = B
          copied_operand <= {b_exp, b_frac}; // Copy mantissa of B
        end
      end else if (b_zero) begin // Only b is zero
        exception_flag <= FLAG_COPY_A; // A + 0 = A, A - 0 = A
        copied_operand <= {a_exp, a_frac}; // Copy mantissa of A

      end else if (a_inf && b_inf) begin
        if ((~operation_select_reg && a_sign == b_sign) || (operation_select_reg && a_sign == ~b_sign))
          exception_flag <= FLAG_COPY_A;
        else
          exception_flag <= FLAG_NAN;
      end else if (({a_sign, a_exp, a_frac} == {b_sign, b_exp, b_frac} && operation_select_reg) || 
                  ({a_exp, a_frac} == {b_exp, b_frac} && (a_sign == ~b_sign) && (~operation_select_reg))) begin
        exception_flag <= FLAG_SUB_SAME_VAL; // A - A = 0
        copied_operand <= {(WIDTH-1){1'b0}}; // Result is zero
      end else begin
        exception_flag <= FLAG_NONE; // No exceptions
      end
    end
  end

endmodule
