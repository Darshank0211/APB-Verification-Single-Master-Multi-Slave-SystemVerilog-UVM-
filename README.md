# APB Verification Single Master-Multi Slave (SV+UVM)

## Project overview
A protocol‑faithful UVM verification framework for APB (Advanced Peripheral Bus). The environment supports a single master routed through an interconnect to multiple slaves, with assertion‑based checks, functional coverage, waveform evidence, and a scoreboard to validate read/write behavior.

## Repository layout
- top.svh
- run.txt
- apb_intf.sv            — APB interface, clocking, modports, and assertions
- apb_seq_item.sv       — randomized sequence item and constraints
- apb_seq.sv            — sequences: apb_seq, wr_seq, rd_seq, wr_rd_seq
- apb_seqr.sv           — sequencer (apb_seqr)
- apb_drv.sv            — protocol‑faithful driver (setup/access, same‑delta probes)
- apb_mon.sv            — monitor sampling interface and forwarding transactions
- apb_agent.sv          — agent bundling seqr/driver/monitor
- apb_env.sv            — environment connecting agent, subscriber, and scoreboard
- apb_scb.sv            — scoreboard with reference memory and validation
- apb_subscriber.sv    — subscriber covergroups for functional coverage
- apb_test.sv           — tests (wr_test, rd_test, wr_rd_test)
- apb_interconnect.sv   — address decode, psel/penable routing, response mux
- apb_dut.sv            — APB slave DUT with configurable wait cycles
- apb_tb_top.sv         — top testbench instantiation and virtual interface setup
- images/               — screenshots and diagrams 

## How to run (example commands — adjust to your simulator)
1. **Clone this repository**  

2. **Tool requirements**  
   - Mentor Questa/ModelSim or other UVM SystemVerilog simulator.

3. **Add top.svh file in Questasim**

4. **Change the run.do file path**
   - Change the path to your downloaded path in run.do file and run the code in Questasim using (do run.do) command. 

## What each file enforces 
- apb_intf.sv
  - Properties implemented: enable_h_mon ($rose(psel) |-> ##1 penable), stable_h_mon (signals stable during penable), de_penable_h_mon ($rose(pready) |-> ##1 $fell(penable)).
  - Matches assertion results images showing zero failures and per‑instance pass counts.
- apb_interconnect.sv
  - Captures paddr at psel, routes psel/penable to the correct slave, and uses captured paddr_r to multiplex prdata/pready/pslverr. Explains per‑slave assertion pass distribution in screenshots.
- apb_drv.sv
  - Implements setup then access phases, waits for pready, uses #0 probes to inspect combinational pready/prdata. Waveform debug prints correspond to displayed DBG lines.
- apb_mon.sv → apb_subscriber.sv
  - Monitor samples transactions each clock and forwards to subscriber; covergroups collect address, penable/psel, pready, pwrite, pwdata/prdata bins — aligns with coverage screenshots showing 100% coverage.
- apb_scb.sv
  - Scoreboard updates reference memory on write and checks reads on completed transactions; pass/fail logs correspond to read/write validation shown in run logs/waveforms.
- apb_dut.sv
  - DUT pready generation (configurable wait cycles) and read/write memory behavior seen in waveform snapshots.

## Results summary 
- Assertion results: all assertions passed with 0 failures; pass counts reflect total transactions at top interface (~1999) and distributed counts per slave (~486–518) ![assertiions](https://github.com/user-attachments/assets/22c6be6e-126f-414d-a14e-631f2382f80c)

- Coverage: covergroups reached 100% for configured coverpoints ![Coverage](https://github.com/user-attachments/assets/08b3fb15-9b42-4bd8-848b-0206e359e91c)

- Waveforms: arbitration req/gnt and APB handshake waveforms show correct req/gnt sequencing and psel → penable → pready/data stability ![waveform](https://github.com/user-attachments/assets/bc35f962-b422-46d0-b61b-480185bb6447)

- Block diagrams: system topology (MASTER → INTERCONNECT → SLAVES) and UVM TB_TOP hierarchy. ![MASTER](https://github.com/user-attachments/assets/4631722e-4423-4038-bf4c-61873130f4bb) and ![uvm_intc_arc](https://github.com/user-attachments/assets/bb848b0e-6ab3-4151-8cc2-ada3fe6ab9a1)

APB Verification Single Master-Multi Slave (SV+UVM): assertion‑driven, scoreboard‑validated verification with full covergroup coverage and waveform evidence.

## Author and technologies
- Author: Darshan K  
- Primary tech: SystemVerilog, UVM; tested with ModelSim/Questa (adjust commands for your toolchain)



