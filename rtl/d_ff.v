module d_ff #(parameter WIDTH = 32)
(
  input clk,
  input arst_n,
  input [WIDTH-1:0] d,
  output reg [WIDTH-1:0] q
);

  always @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      q <= {WIDTH{1'b0}};
    end else begin
      q <= d;
    end
  end
endmodule
