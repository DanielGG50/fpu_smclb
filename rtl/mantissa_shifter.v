module mantissa_shifter #(parameter MANTISSA_WIDTH=23)(
	input clk,
	input arst_n,
	input [MANTISSA_WIDTH-1:0] ma,
	input [MANTISSA_WIDTH-1:0] mb,
	input [4:0] shift_spaces,
	input [1:0] exp_magnitude,
	output reg [MANTISSA_WIDTH+3:0] mantissa_a_out,
	output reg [MANTISSA_WIDTH+3:0] mantissa_b_out
);

	//local parameters
	localparam AGREATER = 2'b10;
	localparam BGREATER = 2'b00;
	localparam EQUAL = 2'b11;

	// Internal signals
	wire [MANTISSA_WIDTH+3:0] operand_a, operand_b;

	assign operand_a = {1'b1, ma, 3'b0};  // Addition of leading, guard, round and sticky bits
	assign operand_b = {1'b1, mb, 3'b0};  // Addition of leading, guard, round and sticky bits

	always @(posedge clk, negedge arst_n)
		if (!arst_n) begin
			mantissa_b_out <= 27'h0;
			mantissa_b_out <= 27'h0;
		end else begin 
			case (exp_magnitude)
				AGREATER: begin 
					mantissa_a_out <= operand_a;
					mantissa_b_out <= operand_b >> shift_spaces;
				end 
				BGREATER: begin
            mantissa_b_out <= operand_b;
            mantissa_a_out <= operand_a >> shift_spaces;
        end
        EQUAL: 
            begin 
            mantissa_a_out <= operand_a;
            mantissa_b_out <= operand_b;
        end
        default: begin 
            mantissa_a_out <= operand_a;
            mantissa_b_out <= operand_b;
        end
    endcase
	end

endmodule

