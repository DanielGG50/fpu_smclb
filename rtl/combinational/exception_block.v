module exception_block #(parameter WIDTH = 32, EXP_BITS = 8, MANT_BITS = 23)
(
	input clk,
	input arst_n,
  input [WIDTH-1:0] a,
  input [WIDTH-1:0] b,
  input operation_select,
  output reg exception
  output reg [WIDTH-1:0]result
);

	wire [EXP_BITS-1:0] a_exp = a[WIDTH-2:MANT_BITS];
  wire [EXP_BITS-1:0] b_exp = b[WIDTH-2:MANT_BITS];
  wire [MANT_BITS-1:0] a_frac = a[MANT_BITS-1:0];
  wire [MANT_BITS-1:0] b_frac = b[MANT_BITS-1:0]

	wire a_zero = (a_exp==8'b0 && a_frac==0);
  wire b_zero = (b_exp==8'b0 && b_frac==0);
  wire a_inf  = (a_exp==8'hFF && a_frac==0);
  wire b_inf  = (b_exp==8'hFF && b_frac==0);
  wire a_nan  = (a_exp==8'hFF && a_frac!=0);
  wire b_nan  = (b_exp==8'hFF && b_frac!=0);

	wire a_sign = a[31];
	wire b_sign = b[31];

	localparam [31:0] CAN_NAN = {1'b0, 8'hFF, 1'b1, 22'b0}; // 7FC00000

	always @(*) begin
		
		exception = 1'b0;
		
				// NaNs
    if ((a_nan) || (b_nan)) begin
    	exception = 1'b1;
      result = CAN_NAN;
    	
				// Inf
		end else if (a_inf && !b_inf) begin
    	exception = 1'b0;
			result = a;
		end else if (!a_inf && b_inf) begin
    	exception = 1'b0;
			if (operation_select == 1'b1) result = {~b_sign, 8'hFF, 23'b0}; // resta: op=1 -> a - b = a + (-b): invierte signo en resta
    	else result = b;
				
				// Zeros
		end else if (a_zero && b_zero) begin
    // +0 ± +0 = +0 ;-+0 ± -0 = depende del signo
    	exception = 1'b0;
			result = { (a_sign & b_sign), 8'h00, 23'b0 }; // IEEE permite que el signo de cero dependa
		end else if (a_zero) begin // 0 +- b
			exception = 1'b0;
			if (operation_select == 1'b1)  // Resta: 0 - B
        result = { ~b_sign, b[30:0] };
    	else                            // Suma: 0 + B
        result = b;
		end else if (b_zero) begin
    // A +- 0 El resultado es a 
    	exception = 1'b0;
			result = a;
				
				// Inf & Inf
		end else if (a_inf && b_inf) begin	// inf +- inf
    // suma: op=01, signos iguales ? Inf; signos distintos ? NaN
    // resta: op=00, a_inf - b_inf: signos opuestos equivale a suma de inf con distintos signos
    	exception = 1'b0;
			if ((operation_select == 1'b0 && a_sign == b_sign) || (operation_select == 1'b1 && a_sign != b_sign)) begin
        result = {a_sign, 8'hFF, 23'b0};
    	end else begin
        result  = CAN_NAN;
        invalid = 1'b1;
    end

	end

endmodule
