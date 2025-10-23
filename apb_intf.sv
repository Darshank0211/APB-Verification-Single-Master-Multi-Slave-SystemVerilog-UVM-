interface apb_intf(input bit pclk, input bit presetn);

  // signals
  logic [1:0] active_slave_id;

  logic [31:0] paddr;
  logic       penable;
  logic       psel;
  logic       pready;
  logic       pwrite;
  logic [31:0] pwdata;
  logic [31:0] prdata;
  logic       pslverr;

  // driver clocking (driver drives outputs, samples inputs)
  clocking drv_cb @(posedge pclk or negedge presetn);
    default input #1 output #1;
    output  paddr;
    output  penable;
    output  psel;
    input   pready;
    output  pwrite;
    output  pwdata;
    input   prdata;
    input   pslverr;
  endclocking

  // monitor clocking (samples signals as seen by DUT/slave)
  clocking mon_cb @(posedge pclk or negedge presetn);
    default input #1 output #1;
    input  paddr;
    input  penable;
    input  psel;
    input  pready;
    input  pwrite;
    input  pwdata;
    input  prdata;
    input  pslverr;
  endclocking

  // modports
  modport driver (clocking drv_cb, input pclk, input presetn);
  modport monitor (clocking mon_cb, input pclk, input presetn);

  // ---------- Assertions on monitor side (slave-facing) ----------

  // 1) penable asserted one clock after psel
  property enable_h_mon;
    @(mon_cb) disable iff(!presetn) $rose(psel) |-> ##1 penable;
  endproperty

  // 2) signals stable during penable assertion (when penable rises)
  property stable_h_mon;
    @(mon_cb) disable iff(!presetn) $rose(penable) |-> ($stable(paddr) && $stable(pwdata) && $stable(pwrite) && $stable(psel));
  endproperty

  // 3) penable deasserted one clock after pready rises
  property de_penable_h_mon;
    @(mon_cb) disable iff(!presetn) $rose(pready) |-> ##1 $fell(penable);
  endproperty

  // Bind assertions
  assert property (enable_h_mon)
    `uvm_info("INTF_ASSERT","enable_h_mon: penable one clock after psel", UVM_DEBUG)
  else
    `uvm_error("INTF_ASSERT","enable_h_mon FAILED: penable not asserted one clock after psel");

  assert property (stable_h_mon)
    `uvm_info("INTF_ASSERT","stable_h_mon: addr/data/control stable during penable", UVM_DEBUG)
  else
    `uvm_error("INTF_ASSERT","stable_h_mon FAILED: signals not stable during penable");

  assert property (de_penable_h_mon)
    `uvm_info("INTF_ASSERT","de_penable_h_mon: penable deasserted one clock after pready", UVM_DEBUG)
  else
    `uvm_error("INTF_ASSERT","de_penable_h_mon FAILED: penable not deasserted one clock after pready");

endinterface

