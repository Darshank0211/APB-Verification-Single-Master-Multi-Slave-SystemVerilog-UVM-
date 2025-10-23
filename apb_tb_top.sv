module apb_tb_top;
//global signals
bit pclk;
bit presetn;

always #5 pclk=~pclk;

initial begin
   #5 presetn =0;
   presetn=1;
end


//interface calling

apb_intf intf(pclk,presetn);

apb_intf s0_intf(pclk,presetn);
apb_intf s1_intf(pclk,presetn);
apb_intf s2_intf(pclk,presetn);
apb_intf s3_intf(pclk,presetn);

//interconnect -master slave connection

apb_interconnect intc(
        .pclk   (pclk),           //.interconnect(interface)
        .presetn(presetn),

	//to get info of active slave id
	.active_slave_id(intf.active_slave_id),

	//master side interface signals 
        .paddr  (intf.paddr),
        .penable(intf.penable),
        .psel   (intf.psel),
        .pready (intf.pready),
        .pwrite (intf.pwrite),
        .pwdata (intf.pwdata),
        .prdata (intf.prdata),
        .pslverr(intf.pslverr),

        //slave 0 connection
        .psel0     (s0_intf.psel),     //.interconnect(interface)
        .prdata0   (s0_intf.prdata),
        .pready0   (s0_intf.pready),
        .pslverr0  (s0_intf.pslverr),
	.penable0  (s0_intf.penable),
        
        // Slave 1 connections
        .psel1     (s1_intf.psel),
        .prdata1   (s1_intf.prdata),
        .pready1   (s1_intf.pready),
        .pslverr1  (s1_intf.pslverr),
        .penable1  (s1_intf.penable),

        // Slave 2 connections
        .psel2     (s2_intf.psel),     //.interconnect(interface)
        .prdata2   (s2_intf.prdata),
        .pready2   (s2_intf.pready),
        .pslverr2  (s2_intf.pslverr),
        .penable2  (s2_intf.penable),

        // Slave 3 connections
        .psel3     (s3_intf.psel),
        .prdata3   (s3_intf.prdata),
        .pready3   (s3_intf.pready),
        .pslverr3  (s3_intf.pslverr),
        .penable3  (s3_intf.penable)
	);

// Slave 0
apb_dut #(.MAX_WAIT_CYCLES(0)) slave0 (
    .pclk     (pclk),
    .presetn  (presetn), 
    .pwrite   (intf.pwrite),
    .paddr    (intf.paddr) ,   //.dut(interface)
    .pwdata   (intf.pwdata),
    .penable  (s0_intf.penable),
    .psel     (s0_intf.psel),
    .prdata   (s0_intf.prdata),
    .pready   (s0_intf.pready),
    .pslverr  (s0_intf.pslverr)
);

// Slave 1
apb_dut #(.MAX_WAIT_CYCLES(0)) slave1 (
    .pclk     (pclk),
    .presetn  (presetn), 
    .pwrite   (intf.pwrite),
    .paddr    (intf.paddr),
    .pwdata   (intf.pwdata),
    .penable  (s1_intf.penable),
    .psel     (s1_intf.psel),
    .prdata   (s1_intf.prdata),
    .pready   (s1_intf.pready),
    .pslverr  (s1_intf.pslverr)
);

// Slave 2
apb_dut #(.MAX_WAIT_CYCLES(0)) slave2 (
    .pclk     (pclk),
    .presetn  (presetn), 
    .pwrite   (intf.pwrite),
    .paddr    (intf.paddr),
    .pwdata   (intf.pwdata),
    .penable  (s2_intf.penable),
    .psel     (s2_intf.psel),
    .prdata   (s2_intf.prdata),
    .pready   (s2_intf.pready),
    .pslverr  (s2_intf.pslverr)
);

// Slave 3
apb_dut #(.MAX_WAIT_CYCLES(0)) slave3 (
    .pclk     (pclk),
    .presetn  (presetn), 
    .pwrite   (intf.pwrite),
    .paddr    (intf.paddr),
    .pwdata   (intf.pwdata),
    .penable  (s3_intf.penable),
    .psel     (s3_intf.psel),
    .prdata   (s3_intf.prdata),
    .pready   (s3_intf.pready),
    .pslverr  (s3_intf.pslverr)
);

//virtual interface set 

initial begin
	uvm_config_db#(virtual apb_intf)::set(uvm_root::get(),"*","vif",intf);
end

//run_test calling ( includes the termination code internally in library)

initial begin
	run_test("wr_rd_test");
end

endmodule
