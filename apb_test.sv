//---------------------------------------------------------------------------//
//---------------------------apb_base_test-----------------------------------//
//---------------------------------------------------------------------------//

class apb_test extends uvm_test;
`uvm_component_utils(apb_test)

function new(string name="apb_test",uvm_component parent);
	super.new(name,parent);
endfunction

apb_env apb_env_h;


virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	apb_env_h=apb_env::type_id::create("apb_env_h",this);
endfunction

virtual function void end_of_elaboration();
	print();
endfunction

function void report_phase(uvm_phase phase);
   uvm_report_server svr;
   super.report_phase(phase);
   
   svr = uvm_report_server::get_server();
   if(svr.get_severity_count(UVM_FATAL)+svr.get_severity_count(UVM_ERROR)>0) begin
     `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
     `uvm_info(get_type_name(), "----            TEST FAIL          ----", UVM_NONE)
     `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
    end
    else begin
     `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
     `uvm_info(get_type_name(), "----           TEST PASS           ----", UVM_NONE)
     `uvm_info(get_type_name(), "----      Coverage Report Above    ----", UVM_NONE)  
     `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)    
end

  endfunction 


endclass


//---------------------------------------------------------------------------//
//---------------------------write_test--------------------------------------//
//---------------------------------------------------------------------------//
class wr_test extends apb_test;
`uvm_component_utils(wr_test)

function new(string name="wr_test",uvm_component parent);
	super.new(name,parent);
endfunction

wr_seq apb_seq_h;

virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	apb_seq_h=wr_seq::type_id::create("apb_seq_h");
endfunction

task run_phase(uvm_phase phase);

	phase.raise_objection(this);
	apb_seq_h.start(apb_env_h.apb_agent_h.apb_seqr_h);
	phase.drop_objection(this);
endtask

endclass


//---------------------------------------------------------------------------//
//-------------------------------read_test-----------------------------------//
//---------------------------------------------------------------------------//
class rd_test extends apb_test;
`uvm_component_utils(rd_test)

function new(string name="rd_test",uvm_component parent);
	super.new(name,parent);
endfunction

rd_seq apb_seq_h;

virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	apb_seq_h=rd_seq::type_id::create("apb_seq_h");
endfunction

task run_phase(uvm_phase phase);

	phase.raise_objection(this);
	apb_seq_h.start(apb_env_h.apb_agent_h.apb_seqr_h);
	phase.drop_objection(this);
endtask

endclass


//---------------------------------------------------------------------------//
//---------------------------write_read_test---------------------------------//
//---------------------------------------------------------------------------//
class wr_rd_test extends apb_test;
`uvm_component_utils(wr_rd_test)

function new(string name="wr_rd_test",uvm_component parent);
	super.new(name,parent);
endfunction

wr_rd_seq apb_seq_h;

virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	apb_seq_h=wr_rd_seq::type_id::create("apb_seq_h");
endfunction

task run_phase(uvm_phase phase);

	phase.raise_objection(this);
	apb_seq_h.start(apb_env_h.apb_agent_h.apb_seqr_h);
	phase.drop_objection(this);
endtask

endclass
