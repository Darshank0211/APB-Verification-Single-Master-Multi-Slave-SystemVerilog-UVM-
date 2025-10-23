class apb_agent extends uvm_agent;
`uvm_component_utils(apb_agent);

apb_seqr apb_seqr_h;
apb_mon  apb_mon_h;
apb_drv  apb_drv_h;

function new(string name="apb_agent",uvm_component parent);
	super.new(name,parent);
endfunction

//components calling from build phase

function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	apb_seqr_h= apb_seqr::type_id::create("apb_seqr_h",this);
        apb_mon_h = apb_mon::type_id::create("apb_mon_h",this)  ;
        apb_drv_h = apb_drv::type_id::create("apb_drv_h",this)  ;
endfunction

//connect phase drv-seqr

function void connect_phase(uvm_phase phase);
	apb_drv_h.seq_item_port.connect(apb_seqr_h.seq_item_export);
endfunction

endclass
