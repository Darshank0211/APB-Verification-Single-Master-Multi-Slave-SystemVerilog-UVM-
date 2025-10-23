class apb_mon extends uvm_monitor;
  `uvm_component_utils(apb_mon)

  apb_seq_item tx;
  virtual apb_intf mon_intf;
  uvm_analysis_port#(apb_seq_item) mon_port;

  function new(string name="apb_mon", uvm_component parent);
    super.new(name,parent);
  endfunction

//build_phase

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon_port = new("mon_port", this);
    if(!uvm_config_db#(virtual apb_intf)::get(this,"","vif",mon_intf)) begin
      `uvm_fatal("APB_MON","No virtual interface found")
    end
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      @(posedge mon_intf.pclk);

      tx = apb_seq_item::type_id::create("tx");

      // Capture all APB signals
      tx.paddr   = mon_intf.mon_cb.paddr;
      tx.pwrite  = mon_intf.mon_cb.pwrite;
      tx.psel    = mon_intf.mon_cb.psel;
      tx.penable = mon_intf.mon_cb.penable;
      tx.pready  = mon_intf.mon_cb.pready;

      if(tx.pwrite)
        tx.pwdata = mon_intf.mon_cb.pwdata;
      else
        tx.prdata = mon_intf.mon_cb.prdata;

      // Send transaction to subscriber (for coverage)
      mon_port.write(tx);

      $display("[%0t] MON: %s ADDR=0x%08h DATA=0x%08h PEN=%0b PSEL=%0b PRE=%0b",
               $time, tx.pwrite ? "WRITE" : "READ",
               tx.paddr, tx.pwrite ? tx.pwdata : tx.prdata,
               tx.penable, tx.psel, tx.pready);
    end
  endtask

endclass

