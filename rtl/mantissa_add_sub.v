module mantissa_add_sub #(parameter MANTISSA_WIDTH = 23)(
	input clk,
	input arst_n,
	input [MANTISSA_WIDTH+3:0] man_a, 
  input [MANTISSA_WIDTH+3:0] man_b,
  input operation_select, // 0 = suma, 1 = resta
  input ma_sign, mb_sign,
  output reg [MANTISSA_WIDTH+3:0] result,
  output reg carry_out
);

  always @(posedge clk, negedge arst_n)
		if (!arst_n) begin
			result <= 27'd0;
			carry_out <= 1'b0;
		end else begin
  		if (ma_sign ~^ (mb_sign ^ operation_select)) begin // Si los signos son iguales (suma real), o en resta con signos opuestos, se suma
    		{carry_out, result} <= man_a + man_b;  // bajo ajuste de overflow más adelane
    end else begin
			if (man_a >= man_b) begin
				result <= man_a - man_b;
				carry_out <= 1'b0;
			end else begin
				result <= man_b - man_a;
				carry_out <= 1'b0;
  		end
  	end
	end

endmodule
