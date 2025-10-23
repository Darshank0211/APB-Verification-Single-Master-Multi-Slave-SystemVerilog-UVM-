class apb_drv extends uvm_driver#(apb_seq_item);
`uvm_component_utils(apb_drv);

apb_seq_item tx;
virtual apb_intf drv_intf;

function new(string name="apb_drv", uvm_component parent);
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual apb_intf)::get(this, "", "vif", drv_intf)) begin
        `uvm_fatal("DRV","no drv vif found");
    end
endfunction

task run_phase(uvm_phase phase);
    forever begin
        @(posedge drv_intf.pclk);
        tx = apb_seq_item::type_id::create("tx");
        seq_item_port.get_next_item(tx);
        driver_logic(tx);
        seq_item_port.item_done();
    end
endtask

task driver_logic(apb_seq_item tx);
    $display("[%0t] DRIVER: op=%s addr=0x%08h data=0x%08h", $time, tx.op.name(), tx.paddr, tx.pwdata);
    if (tx.op == write) write_w(tx);
    else if (tx.op == read) read_r(tx);
    else if (tx.op == wr_rd) wr_rd(tx);
endtask

// ------------------------- WRITE -------------------------
task write_w(apb_seq_item tx);
    // Setup phase: assert psel and present stable address/data
    @(posedge drv_intf.pclk);
    drv_intf.drv_cb.paddr   <= tx.paddr;
    drv_intf.drv_cb.pwdata  <= tx.pwdata;
    drv_intf.drv_cb.pwrite  <= 1'b1;
    drv_intf.drv_cb.psel    <= 1'b1;
    drv_intf.drv_cb.penable <= 1'b0;
    $display("[%0t] DRIVER: WRITE setup done (psel asserted)", $time);

    // Access phase: assert penable on next posedge
    @(posedge drv_intf.pclk);
    drv_intf.drv_cb.penable <= 1'b1;
    $display("[%0t] DRIVER: WRITE access (penable asserted)", $time);

    // Immediate same-delta sample of DUT-visible nets
    #0;
    $display("[%0t] DRIVER DBG: after #0 intf.pready=%0b intf.prdata=0x%08h", $time, drv_intf.pready, drv_intf.prdata);

    if (drv_intf.pready) begin
        // single-cycle completion: deassert penable/psel on next posedge
        @(posedge drv_intf.pclk);
        drv_intf.drv_cb.penable <= 1'b0;
        drv_intf.drv_cb.psel    <= 1'b0;
        drv_intf.drv_cb.paddr   <= 32'h0;
        drv_intf.drv_cb.pwdata  <= 32'h0;
        drv_intf.drv_cb.pwrite  <= 1'b0;
        $display("[%0t] DRIVER: WRITE single-cycle complete", $time);
    end
    else begin
        // multi-cycle: wait until pready becomes 1 (combinational or on posedge)
        $display("[%0t] DRIVER: WRITE waiting for pready", $time);
        wait (drv_intf.pready == 1'b1);
        #0;
        $display("[%0t] DRIVER DBG: pready observed intf.prdata=0x%08h", $time, drv_intf.prdata);
        @(posedge drv_intf.pclk);
        drv_intf.drv_cb.penable <= 1'b0;
        drv_intf.drv_cb.psel    <= 1'b0;
        drv_intf.drv_cb.paddr   <= 32'h0;
        drv_intf.drv_cb.pwdata  <= 32'h0;
        drv_intf.drv_cb.pwrite  <= 1'b0;
        $display("[%0t] DRIVER: WRITE multi-cycle complete", $time);
    end
endtask

// ------------------------- READ -------------------------
task read_r(apb_seq_item tx);
    // Setup phase: assert psel and present stable address
    @(posedge drv_intf.pclk);
    drv_intf.drv_cb.paddr   <= tx.paddr;
    drv_intf.drv_cb.pwrite  <= 1'b0;
    drv_intf.drv_cb.psel    <= 1'b1;
    drv_intf.drv_cb.penable <= 1'b0;
    $display("[%0t] DRIVER: READ setup done (psel asserted)", $time);

    // Access phase: assert penable on next posedge
    @(posedge drv_intf.pclk);
    drv_intf.drv_cb.penable <= 1'b1;
    $display("[%0t] DRIVER: READ access (penable asserted)", $time);

    // Immediate same-delta sample of DUT-visible nets
    #0;
    $display("[%0t] DRIVER DBG: after #0 intf.pready=%0b intf.prdata=0x%08h", $time, drv_intf.pready, drv_intf.prdata);

    if (drv_intf.pready) begin
        // single-cycle read: capture data and deassert on next posedge
        tx.prdata = drv_intf.prdata;
        $display("[%0t] DRIVER: READ single-cycle data=0x%08h", $time, tx.prdata);
        @(posedge drv_intf.pclk);
        drv_intf.drv_cb.penable <= 1'b0;
        drv_intf.drv_cb.psel    <= 1'b0;
        drv_intf.drv_cb.paddr   <= 32'h0;
        drv_intf.drv_cb.pwrite  <= 1'b0;
        $display("[%0t] DRIVER: READ single-cycle complete", $time);
    end
    else begin
        // multi-cycle: wait until pready becomes 1
        $display("[%0t] DRIVER: READ waiting for pready", $time);
        wait (drv_intf.pready == 1'b1);
        #0;
        tx.prdata = drv_intf.prdata;
        $display("[%0t] DRIVER: READ data after wait=0x%08h", $time, tx.prdata);
        @(posedge drv_intf.pclk);
        drv_intf.drv_cb.penable <= 1'b0;
        drv_intf.drv_cb.psel    <= 1'b0;
        drv_intf.drv_cb.paddr   <= 32'h0;
        drv_intf.drv_cb.pwrite  <= 1'b0;
        $display("[%0t] DRIVER: READ multi-cycle complete", $time);
    end
endtask

// ------------------------- WR_RD -------------------------
task wr_rd(apb_seq_item tx);
    bit [31:0] saved_addr = tx.paddr;
    bit [31:0] saved_data = tx.pwdata;

    write_w(tx);              // write
    tx.paddr = saved_addr;    // restore address for read
    read_r(tx);               // read

    if (tx.prdata !== saved_data) begin
        `uvm_error("DRV","WR_RD mismatch");
    end else begin
        $display("[%0t] DRIVER: WR_RD success data=0x%08h", $time, tx.prdata);
    end
endtask

endclass

