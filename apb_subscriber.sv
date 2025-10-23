class apb_subscriber extends uvm_subscriber#(apb_seq_item);
  `uvm_component_utils(apb_subscriber)

  apb_seq_item tx;
  virtual apb_intf vif;

//covergroup def
//
  covergroup cg with function sample(apb_seq_item tx);

    option.per_instance = 1;

    cp_paddr: coverpoint tx.paddr { bins addr = {[32'h00000000:32'h000000FF]}; }

    cp_penable: coverpoint tx.penable { bins setup={0}; bins access={1}; }

    cp_psel: coverpoint tx.psel { bins aassert={1}; bins deassert={0}; }

    cp_pready: coverpoint tx.pready { bins waitt={0}; bins ready={1}; }

    cp_pwrite: coverpoint tx.pwrite { bins read={0}; bins write={1}; }

    cp_pwdata: coverpoint tx.pwdata iff(tx.pwrite) { bins written_data={[32'h00000001:32'h0000FFFF]};}

    cp_prdata: coverpoint tx.prdata iff(!tx.pwrite) { bins read_data={[32'h00000001:32'h0000FFFF]};}
    
  endgroup

  function new(string name="apb_subscriber", uvm_component parent=null);
    super.new(name,parent);
    cg = new();
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tx = apb_seq_item::type_id::create("tx");
    if (!uvm_config_db#(virtual apb_intf)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface not set for apb_subscriber")
    end
  endfunction

//write function to sample the covergroup

  virtual function void write(apb_seq_item t);
    if(t == null) return;
    tx = t;
    cg.sample(tx);
  endfunction

//coverage report

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("COVERAGE", $sformatf("APB Coverage = %0.2f%%", cg.get_inst_coverage()), UVM_LOW)
  endfunction

endclass

