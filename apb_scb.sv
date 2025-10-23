class apb_scb extends uvm_scoreboard;
  `uvm_component_utils(apb_scb)

  uvm_analysis_imp #(apb_seq_item,apb_scb) scb_port;

  localparam int mem_depth=1024;//creating a big memory for checking
  bit [31:0] ref_mem [0:mem_depth-1];
  int pass_count=0;
  int fail_count=0;

  function new(string name="apb_scb", uvm_component parent);
    super.new(name,parent);
    foreach(ref_mem[i]) ref_mem[i] = 32'h0;
    $display("Initialized memory");
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    scb_port = new("scb_port", this);
  endfunction

  function void write(apb_seq_item m_tx);

    // Only process completed transactions
    if (!(m_tx.psel && m_tx.penable && m_tx.pready)) return;

    if (m_tx.pwrite) begin
      ref_mem[m_tx.paddr] = m_tx.pwdata;
      $display("[%0t] SCB: WRITE  [0x%08h] <= 0x%08h", $time, m_tx.paddr, m_tx.pwdata);
      pass_count++;
    end else begin
      bit [31:0] expected = ref_mem[m_tx.paddr];
      $display("[%0t] SCB: READ   [0x%08h] exp=0x%08h got=0x%08h", $time, m_tx.paddr, expected, m_tx.prdata);

      if (m_tx.prdata === expected) begin
        $display("[%0t] SCB: ✅ READ PASS", $time);
        pass_count++;
      end else begin
        $display("[%0t] SCB: ❌ READ FAIL", $time);
        fail_count++;
      end
    end

    $display("[%0t] SCB STATS: Pass=%0d Fail=%0d", $time, pass_count, fail_count);
  endfunction

endclass

