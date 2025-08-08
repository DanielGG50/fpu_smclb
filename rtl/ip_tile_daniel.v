/*
module ip_tile_daniel #(parameter CSR_IN_WIDTH = 16, CSR_OUT_WIDTH = 16, REG_WIDTH = 32)(
  input clk,
  input arst_n,
  input [CSR_IN_WIDTH - 1 : 0] csr_in,
  output wire csr_in_re,
  input [REG_WIDTH - 1 : 0] data_reg_a,
  input [REG_WIDTH - 1 : 0] data_reg_b,
  output wire [CSR_OUT_WIDTH - 1 : 0] csr_out,
  output wire csr_out_we,
  output wire [REG_WIDTH - 1 : 0] data_reg_c
);

  assign csr_out = csr_in;
  assign csr_in_re = 1'b0;
  assign csr_out_we = 1'b0;

	reg [REG_WIDTH - 1 : 0] a_delayed;

  add_sub_main top_module (
  	.en(csr_in[15]),
    .a(a_delayed), // Delayed
    .b(data_reg_b),
    .operation_select(csr_in[4]),
    .clk(clk),
    .arst_n(arst_n),
    .R(data_reg_c)
  );

	always @(posedge clk, negedge arst_n) begin // Delay A reg to match inputs, assuming a is set first
		if (!arst_n) begin
			a_delayed <= {REG_WIDTH{1'h0000}};
		end else begin
			a_delayed <= data_reg_a;	
		end
	end
	
endmodule
*/
module ip_tile_daniel_garcia #(
parameter REG_WIDTH = 32,
parameter CSR_IN_WIDTH = 16,
parameter CSR_OUT_WIDTH = 16)
(
input wire clk,
input wire arst_n,
input wire [CSR_IN_WIDTH-1:0] csr_in,
input wire  [REG_WIDTH - 1:0] data_reg_a,
input wire  [REG_WIDTH - 1:0] data_reg_b,
output wire [REG_WIDTH - 1:0] data_reg_c,
output wire [CSR_OUT_WIDTH-1:0] csr_out,
output wire csr_in_re,
output wire csr_out_we
); 

  assign csr_out = csr_in;
  assign csr_in_re = 1'b0;
  assign csr_out_we = 1'b0;

  add_sub_main top_module (
    .en(csr_in[15]),
    .a(data_reg_a), 
    .b(data_reg_b),
    .operation_select(csr_in[4]),
    .clk(clk),
    .arst_n(arst_n),
    .data_reg_c(data_reg_c)
  );

endmodule
