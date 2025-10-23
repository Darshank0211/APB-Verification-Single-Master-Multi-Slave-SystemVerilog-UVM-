class apb_seq extends uvm_sequence#(apb_seq_item);
  `uvm_object_utils(apb_seq)
  apb_seq_item tx;

  function new(string name = "apb_seq");
    super.new(name);
  endfunction

  virtual task body();
    repeat (1000) begin
      tx = apb_seq_item::type_id::create("tx");
      // choose the op (random example) -- ensures driver sees op
      if (!tx.randomize() with { op inside {write, read, wr_rd}; })
        `uvm_error("APB_SEQ", "randomize failed for tx.op");
      start_item(tx);
      finish_item(tx);
    end
  endtask
endclass

//---------------------------------------------------------------------//
//--------------------------write_sequence-----------------------------//
//---------------------------------------------------------------------//

class wr_seq extends uvm_sequence#(apb_seq_item);
  `uvm_object_utils(wr_seq);

   apb_seq_item tx;
  function new(string name="wr_seq"); 
	  super.new(name); 
  endfunction

  virtual task body();
    repeat (1000) begin
      tx = apb_seq_item::type_id::create("tx");
      // force op to write
      tx.op = write;
      // randomize other fields (address/data) with constraint that pwrite bit maybe ignored by driver
      wait_for_grant();
      tx.randomize();
      send_request(tx);
      wait_for_item_done();
          end
  endtask
endclass

//---------------------------------------------------------------------//
//--------------------------read_sequence------------------------------//
//---------------------------------------------------------------------//

class rd_seq extends uvm_sequence#(apb_seq_item);
  `uvm_object_utils(rd_seq);
  apb_seq_item tx;
  function new(string name="rd_seq");
	  super.new(name);
  endfunction

  virtual task body();
    repeat (1000) begin
      tx = apb_seq_item::type_id::create("tx");
      tx.op = read;
      wait_for_grant();
      tx.randomize();
      send_request(tx);
      wait_for_item_done();
         end
  endtask
endclass

//---------------------------------------------------------------------//
//--------------------------write__read_sequence-----------------------//
//---------------------------------------------------------------------//

class wr_rd_seq extends uvm_sequence#(apb_seq_item);
  `uvm_object_utils(wr_rd_seq);
   apb_seq_item tx;
  bit [31:0] last_address;//used to collect the same address from write to read from the same address

  function new(string name="wr_rd_seq"); 
	  super.new(name); 
  endfunction

  virtual task body();
    repeat (1000) begin
	    
	    tx=apb_seq_item::type_id::create("tx");
	    tx.op=wr_rd;
	    wait_for_grant();
	    tx.randomize() with { op==write; };//write operation
	    last_address=tx.paddr;
	    send_request(tx);
	    wait_for_item_done();

	    tx=apb_seq_item::type_id::create("tx");
	    wait_for_grant();
	    tx.randomize() with { op==read; paddr==last_address;};//read operation
	    send_request(tx);
	    wait_for_item_done();


         end
  endtask
endclass
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
//    apb_seq_item tx;
//    bit [31:0] last_written_addr;
//    bit [31:0] last_written_data;
//    bit write_done = 0;
//    
//    function new(string name = "apb_seq");
//        super.new(name);
//    endfunction
//    
//    virtual task body();
//        repeat(10) begin
//            tx = apb_seq_item::type_id::create("tx");
//            
//            if(!write_done) begin
//                // WRITE Transaction
//                start_item(tx);
//                assert(tx.randomize() with {
//                    pwrite == 1;                    // Write operation
//                    paddr inside {[0:31]};          // Address range constraint
//                });
//                last_written_addr = tx.paddr;
//                last_written_data = tx.pwdata;
//                write_done = 1;
//                finish_item(tx);
//                `uvm_info(get_type_name(), 
//                         $sformatf("✅ WRITE: Addr=0x%08h Data=0x%08h", 
//                                  tx.paddr, tx.pwdata), UVM_MEDIUM);
//            end
//            else begin
//                // READ Transaction  
//                start_item(tx);
//                assert(tx.randomize() with {
//                    pwrite == 0;                    // Read operation
//                    paddr == last_written_addr;    // Read from same address
//                });
//                write_done = 0;
//                `uvm_info(get_type_name(), 
//                         $sformatf("✅ READ:  Addr=0x%08h (expecting 0x%08h)", 
//                                  tx.paddr, last_written_data), UVM_MEDIUM);
//                finish_item(tx);
//            end
//        end
//    endtask
//endclass

