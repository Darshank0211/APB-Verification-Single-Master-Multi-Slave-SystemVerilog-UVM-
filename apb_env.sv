class apb_env extends uvm_env;
`uvm_component_utils(apb_env)

apb_agent apb_agent_h;
apb_scb apb_scb_h;
apb_subscriber apb_sub_h;

function new(string name="apb_env",uvm_component parent);
	super.new(name,parent);

endfunction

//creating components through build phase

function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	apb_agent_h=apb_agent::type_id::create("apb_agent_h",this);
	apb_scb_h  =apb_scb::type_id::create("apb_scb_h",this);
	apb_sub_h  =apb_subscriber::type_id::create("apb_sub_h",this);
endfunction

//connecting mon-scb and mon-subscriber

function void connect_phase(uvm_phase phase);
	apb_agent_h.apb_mon_h.mon_port.connect(apb_scb_h.scb_port);
	apb_agent_h.apb_mon_h.mon_port.connect(apb_sub_h.analysis_export);
endfunction

endclass
