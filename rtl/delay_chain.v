module delay_chain #(parameter WIDTH = 1, STAGES = 2) (
    input clk,
    input arst_n,
    input [WIDTH-1:0] d,
    output [WIDTH-1:0] q
);

    reg [WIDTH-1:0] stage[0:STAGES-1];

    integer i;

    always @(posedge clk or negedge arst_n) begin
        if (!arst_n) begin
            for (i = 0; i < STAGES; i = i + 1)
                stage[i] <= 0;
        end else begin
            stage[0] <= d;
            for (i = 1; i < STAGES; i = i + 1)
                stage[i] <= stage[i-1];
        end
    end

    assign q = stage[STAGES-1];

endmodule
