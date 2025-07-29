module select_result #(parameter WIDTH = 32) (
  input [WIDTH-1:0] R_normal,
  input [2:0] exception_flag,
  input sign_a, sign_b,
  input [WIDTH-2:0] copied_operand,
  output reg [31:0] R
);

  localparam [2:0]
    FLAG_NONE          = 3'b000,
    FLAG_NAN           = 3'b001,
    FLAG_COPY_A        = 3'b010,
    FLAG_COPY_B        = 3'b011,
    FLAG_FIN_MIN_INF   = 3'b100,
    FLAG_ZERO_MIN_ZERO = 3'b101,
    FLAG_ZERO_MIN_SOME = 3'b110,
    FLAG_SUB_SAME_VAL  = 3'b111;

  always @(*) begin
    case (exception_flag)
      FLAG_NONE: R = R_normal; // No exception, normal result
      FLAG_NAN: R = 32'h7FC00000; // NaN
      FLAG_COPY_A: R = {sign_a, copied_operand}; // Copy A
      FLAG_COPY_B: R = {sign_b, copied_operand}; // Copy B
      FLAG_FIN_MIN_INF: R = {~sign_b, 8'hFF, 23'h0}; // Result is -INF or INF based on sign
      FLAG_ZERO_MIN_ZERO: R = {(sign_a & sign_b), 8'h00, 23'h0}; // Zero result, considering signs
      FLAG_ZERO_MIN_SOME: R = {(~sign_b), copied_operand}; // Result is -Zero
      FLAG_SUB_SAME_VAL: R = {(sign_a & sign_b), copied_operand}; // Infinity + Infinity
      default: R = R_normal; // Default case
    endcase
  end
  
endmodule
