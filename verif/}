module fpu_add_sub_tb;

  // Entradas
  reg [31:0] A, B;
  reg op;
  reg clk;
  reg arst_n;

  // Salidas
  wire [31:0] Z;

  // Instancia del DUT
  add_sub_main dut (
    .a(A),
    .b(B),
    .operation_select(op),
    .clk(clk),
    .arst_n(arst_n),
    .R(Z)
  );

  // Reloj
  initial clk = 0;
  always #5 clk = ~clk;

  // Procedimiento de pruebas
  initial begin
    $display("Inicio del testbench para FPU");

    // Reset
    arst_n = 0; A = 0; B = 0;
    #1; @(posedge clk); arst_n = 1;

    ///////////////////////
    // CASOS DE SUMA
    ///////////////////////
    
    op = 1'b0;

		@(posedge clk)
    A = 32'h7f800000;
    B = 32'h41200000;

		@(posedge clk)
    A = 32'h7F800000;
    B = 32'h7F800000;

    // Denormalized
    @(posedge clk)
    A = 32'h00400000;  // 10.0
    B = 32'h00471000;  // 5.0

    // Denormalized
    @(posedge clk)
    A = 32'h00c38800;  // 10.0
    B = 32'h00471000;  // 5.0


    // Suma normal
    @(posedge clk);
	  A = 32'h41200000;  // 10.0
    B = 32'h40a00000;  // Changed 4 for C
		
    // Suma normal
    @(posedge clk);
    op = 1'b1;
		A = 32'h4120400a;  
    B = 32'hc120400a;  
   
    @(posedge clk);
    op = 1'b0;
    A = 32'h4120400a;  
    B = 32'hc120400a;  

    @(posedge clk);
    A = 32'h4120400a;  
    B = 32'h4120400a;    
    
    @(posedge clk);
    op = 1'b1;
    A = 32'h4120400a;  
    B = 32'h4120400a;      
		@(posedge clk);
		op = 1'b0;
    A = 32'hC1200000;  // 10.0
    B = 32'hC0a00000;  // 5.0

		@(posedge clk);		
		A = 32'h40200000;
		B = 32'h411e6666;
	
		@(posedge clk)
    A = 32'hff800000;
    B = 32'hc1200000;  // -10.0
	
		@(posedge clk);		
		A = 32'h3f9e6666;
		B = 32'h40066606;
		
    // Suma +? + -? = NaN
		@(posedge clk)    
    A = 32'h7f800000;
    B = 32'hff800000;

    // Suma con NaN
		@(posedge clk)
    A = 32'h7fc00000;
    B = 32'h41200000;

    // Suma con +0
		@(posedge clk)    
    A = 32'h00000000;
    B = 32'h41200000;

    // Suma -0 + -5
		@(posedge clk)
    A = 32'h80000000;
    B = 32'hc0a00000;

    ///////////////////////
    // CASOS DE RESTA
    ///////////////////////
    op = 1'b1;

    // Resta normal
		@(posedge clk)
    A = 32'h41600000;  // 14.0
    B = 32'h40a00000;  // 5.0

    // Resta con +? - finito = +?
		@(posedge clk)    
    A = 32'h7f800000;
    B = 32'h41200000;

    // Resta con -? - finito = -?
		@(posedge clk)    
    A = 32'hff800000;
    B = 32'h41200000;

    // Resta +? - +? = NaN
		@(posedge clk)    
    A = 32'h7f800000;
    B = 32'h7f800000;

    // Resta con NaN
		@(posedge clk)    
    A = 32'h41200000;
    B = 32'h7fc00000;

    // Resta +0 - 10
		@(posedge clk)    
    A = 32'h00000000;
    B = 32'h41200000;

    // Resta -0 - (-10)
		@(posedge clk)    
    A = 32'h80000000;
    B = 32'hc1200000;

    #200;
    $display("Fin del testbench.");
    $finish;
  end

 	initial begin
		$shm_open("shm_db");
		$shm_probe("ASMTR");
  end


endmodule

