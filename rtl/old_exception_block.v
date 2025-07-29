module exception_block #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)
(
  input clk,
  input arst_n,
  input [WIDTH-1:0] a,
  input [WIDTH-1:0] b,
  input operation_select,
  output reg exception,
  output reg [WIDTH-1:0] result
);

  wire [EXP_BITS-1:0] a_exp = a[WIDTH-2:MANT_BITS];
  wire [EXP_BITS-1:0] b_exp = b[WIDTH-2:MANT_BITS];
  wire [MANT_BITS-1:0] a_frac = a[MANT_BITS-1:0];
  wire [MANT_BITS-1:0] b_frac = b[MANT_BITS-1:0];

  wire a_zero = (a_exp == 0 && a_frac == 0);
  wire b_zero = (b_exp == 0 && b_frac == 0);
  wire a_inf  = (a_exp == 8'hFF && a_frac == 0);
  wire b_inf  = (b_exp == 8'hFF && b_frac == 0);
  wire a_nan  = (a_exp == 8'hFF && a_frac != 0);
  wire b_nan  = (b_exp == 8'hFF && b_frac != 0);

  wire a_sign = a[WIDTH-1];
  wire b_sign = b[WIDTH-1];

  localparam [WIDTH-1:0] CAN_NAN = {1'b0, 8'hFF, 1'b1, 22'b0}; // 0x7FC00000

  reg exception_middle;
  reg [WIDTH-1:0] result_middle;

  always @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      exception <= 1'b0;
      result <= {WIDTH{1'b0}};
    end else begin

      exception_middle = 1'b0;
      result_middle = {WIDTH{1'b0}};
        // NaNs
      if (a_nan || b_nan) begin
        exception_middle = 1'b1;
        result_middle = CAN_NAN;
        // single inf
      end else if (a_inf && !b_inf) begin
        exception_middle = 1'b1;
				result_middle = a;
      end else if (!a_inf && b_inf) begin
        exception_middle = 1'b1;
				if (operation_select == 1'b1)  // resta: op=1 -> a - b = a + (-b): invierte signo en resta
          result_middle = {~b_sign, 8'hFF, 23'b0};
        else
          result_middle = b;
        // Zeros, +0 ± +0 = +0 ;-+0 ± -0 = depende del signo
      end else if (a_zero && b_zero) begin
        exception_middle = 1'b1;
				result_middle = {(a_sign & b_sign), 8'h00, 23'd0};
      end else if (a_zero) begin // 0 +- b
        exception_middle = 1'b1;
				if (operation_select == 1'b1)
					result_middle = {~b_sign, b[30:0]}; // Resta: 0 - B
        else
          result_middle = b; // Suma: 0 + B
      end else if (b_zero) begin
        result_middle = a;
				exception_middle = 1'b1;
        // Both inf
      end else if (a_inf && b_inf) begin
      	exception_middle = 1'b1;      
						// suma: op=0, signos iguales ? Inf; signos distintos ? NaN
            // resta: op=1, a_inf - b_inf: signos opuestos equivale a suma de inf con mismos signos
        if ((operation_select == 1'b0 && a_sign == b_sign) ||(operation_select == 1'b1 && a_sign != b_sign)) begin
          result_middle = {a_sign, 8'hFF, 23'b0};
        end else begin
          result_middle = CAN_NAN;
        end
      end
      exception <= exception_middle;
      result <= result_middle;

    end
  end

endmodule
