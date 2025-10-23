//tb_top
//	test
//		seq
//			seq_item
//		env	
//			scb
//			agent
//					seqr
//					drv
//					mon
//	intf
//	dut
import uvm_pkg::*;         //uvm_pkg importing
`include "uvm_macros.svh"  //uvm_macro inclusion

//independent to dependent order 

`include "apb_intf.sv"
`include "apb_seq_item.sv"
`include "apb_seq.sv"
`include "apb_seqr.sv"
`include "apb_mon.sv"
`include "apb_drv.sv"
`include "apb_scb.sv"
`include "apb_subscriber.sv"
`include "apb_agent.sv"
`include "apb_env.sv"
`include "apb_test.sv"
`include "apb_interconnect.sv"
`include "apb_dut.sv"
`include "apb_tb_top.sv"
		
