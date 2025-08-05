module tb_ip_tile_daniel;

	parameter CSR_IN_WIDTH = 16;
	parameter CSR_OUT_WIDTH = 16;
	parameter REG_WIDTH = 32;

	bit clk;
	bit arst_n;
	interface_ip_tile intf(clk, arst_n);

	always #5ns clk = !clk;
	assign #20ns arst_n = 1'b1;

	ip_tile_daniel DUT(
	  .clk(clk),
	  .arst_n(arst_n),
	  .csr_in(intf.csr_in),
	  .csr_in_re(intf.csr_in_re),
	  .data_reg_a(intf.data_reg_a),
	  .data_reg_b(intf.data_reg_b),
	  .csr_out(intf.csr_out),
	  .csr_out_we(intf.csr_out_we),
	  .data_reg_c(intf.data_reg_c)
	);

	initial begin
  	clk = 0;
  	@(posedge arst_n);	
	
		@(posedge clk); // suma INF + X  
		intf.write_data_reg_a(32'h7F800000);
		intf.write_data_reg_b(32'h41200000);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); 	// sum INF + INF  
		intf.write_data_reg_a(32'h7F800000);
		intf.write_data_reg_b(32'h7F800000);
		intf.write_csr_in(16'h8000);
		/*
		@(posedge clk); // suma subnormal
		intf.write_csr_in(16'h0010);
		intf.write_data_reg_a(32'h00400000);
		intf.write_data_reg_b(32'h00471000);
		
		@(posedge clk); // suma subnormales
		intf.write_data_reg_a(32'h00C38800);
		intf.write_data_reg_b(32'h00471000);
		*/
		//@(posedge clk); // suma x + y
		intf.write_data_reg_a(32'h41200000);
		intf.write_data_reg_b(32'h40A00000);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // resta x - (-x) 
		intf.write_data_reg_a(32'h4120400A);
		intf.write_data_reg_b(32'hC120400A);
		intf.write_csr_in(16'h8010); 
		
		//@(posedge clk); // suma x + (-x)
		intf.write_data_reg_a(32'h4120400A);
		intf.write_data_reg_b(32'hC120400A);
		intf.write_csr_in(16'h8000);//intf.write_csr_in(16'h8000);  
		
		//@(posedge clk); // suma x + x								
		intf.write_data_reg_a(32'h4120400A);
		intf.write_data_reg_b(32'h4120400A);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // resta x - x
		intf.write_data_reg_a(32'h4120400A);
		intf.write_data_reg_b(32'h4120400A);
		intf.write_csr_in(16'h8010);  
		
		//@(posedge clk); // suma x + y
		intf.write_data_reg_a(32'hC1200000);
		intf.write_data_reg_b(32'hC0A00000);
		intf.write_csr_in(16'h8000);	
		
		//@(posedge clk); // suma x + y
		intf.write_data_reg_a(32'h40200000);
		intf.write_data_reg_b(32'h411E6666);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // suma -INF + x
		intf.write_data_reg_a(32'hFF800000);
		intf.write_data_reg_b(32'hC1200000);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // suma x + y
		intf.write_data_reg_a(32'h3F9E6666);
		intf.write_data_reg_b(32'h40066606);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // Suma +inf + -inf = NaN
		intf.write_data_reg_a(32'h7F800000);
		intf.write_data_reg_b(32'hFF800000);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // NaN + x
		intf.write_data_reg_a(32'hFF882410);
		intf.write_data_reg_b(32'h41200000);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // Suma con +0
		intf.write_data_reg_a(32'h00000000);
		intf.write_data_reg_b(32'h41200000);
		intf.write_csr_in(16'h8000);
		
		//@(posedge clk); // Suma -0 + -5
		intf.write_data_reg_a(32'h80000000);
		intf.write_data_reg_b(32'hC0A00000);
		intf.write_csr_in(16'h8000);
		
		///////////////////////
		// CASOS DE RESTA
		///////////////////////
		
		//@(posedge clk); // resta x - y
		intf.write_data_reg_a(32'h41600000);
		intf.write_data_reg_b(32'h40A00000);
		intf.write_csr_in(16'h8010);  
		
		//@(posedge clk); // Resta +inf - fin = +inf
		intf.write_data_reg_a(32'h7F800000);
		intf.write_data_reg_b(32'h41200000);
		intf.write_csr_in(16'h8010);
		
		//@(posedge clk); // Resta -inf - fin = -inf
		intf.write_data_reg_a(32'hFF800000);
		intf.write_data_reg_b(32'h41200000);
		intf.write_csr_in(16'h8010); ////////////////////////
			
		//@(posedge clk); // Resta +inf - +inf = NaN
		intf.write_data_reg_a(32'h7F800000);
		intf.write_data_reg_b(32'h7F800000);
		//intf.write_csr_in(16'h0000); ////////////////////////
		
		//@(posedge clk); // Resta con NaN
		intf.write_data_reg_a(32'h41200000);
		intf.write_data_reg_b(32'h7FC00000);
		//intf.write_csr_in(16'h0000); ////////////////////////
		
		//@(posedge clk); // Resta +0 - 10
		intf.write_data_reg_a(32'h00000000);
		intf.write_data_reg_b(32'h41200000);
		intf.write_csr_in(16'h8010);
		
		//@(posedge clk); // Resta -0 - (-10)
		intf.write_data_reg_a(32'h80000000);
		intf.write_data_reg_b(32'hC1200000);
		intf.write_csr_in(16'h8000);
		 		
		//@(posedge clk); // Resta -0 - (-10)	
		intf.write_data_reg_a(32'h80000000);
		intf.write_data_reg_b(32'hC1200000);
		intf.write_csr_in(16'h0000);
		
		intf.write_data_reg_a(32'h41200000);
		intf.write_data_reg_b(32'h00000000);
		intf.write_csr_in(16'h8010);
		
		//@(posedge clk); // Resta -0 - (-10)
		intf.write_data_reg_a(32'hC1200000);
		intf.write_data_reg_b(32'h80000000);
		intf.write_csr_in(16'h0010);		
		
///////////////////////////////////////////
		intf.write_data_reg_a(32'hc2229268);
		intf.write_data_reg_b(32'h4380126f);
		intf.write_csr_in(16'h8000);

		intf.write_data_reg_a(32'h3f80126f);
		intf.write_data_reg_b(32'hbd7d526f);
		intf.write_csr_in(16'h8010);

		intf.write_data_reg_a(32'h4c95526f);
		intf.write_data_reg_b(32'h4e85520f);
		intf.write_csr_in(16'h8000);

		intf.write_data_reg_a(32'hcef5520f);
		intf.write_data_reg_b(32'hcff55a0f);
		intf.write_csr_in(16'h8010);

    #200;
    $display("Fin del testbench.");
    $finish;
  end

 	initial begin
		$shm_open("shm_db");
		$shm_probe("ASMTR");
  end


endmodule
