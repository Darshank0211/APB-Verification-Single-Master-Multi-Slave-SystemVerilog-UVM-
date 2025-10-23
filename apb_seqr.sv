//Everything is pre written in the library
//this file is used for the arbitration and seq-seqr-driver communication
//internally

class apb_seqr extends uvm_sequencer#(apb_seq_item);
`uvm_component_utils(apb_seqr);

function new(string name="apb_seqr",uvm_component parent);
       super.new(name,parent);
endfunction

endclass
