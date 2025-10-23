module apb_dut #(
    parameter int DEPTH = 1024,
    parameter int MAX_WAIT_CYCLES = 0
) (
    input  logic         pclk,
    input  logic         presetn,
    input  logic         psel,
    input  logic         pwrite,
    input  logic         penable,
    input  logic [31:0]  paddr,
    input  logic [31:0]  pwdata,
    output logic [31:0]  prdata,
    output logic         pready,
    output logic         pslverr
);

    // Memory
    logic [31:0] mem [0:DEPTH-1];

    // Internal registers
    int unsigned wait_cnt;
    logic ready_lat;

    // Access phase active
    logic access_phase;
    assign access_phase = psel && penable;

    // Wait counter and ready flag
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            wait_cnt  <= 0;
            ready_lat <= 1'b0;
        end else begin
            if (!access_phase) begin
                wait_cnt  <= 0;
                ready_lat <= 1'b0;
            end else if (MAX_WAIT_CYCLES > 0) begin
                if (!ready_lat) begin
                    if (wait_cnt == MAX_WAIT_CYCLES - 1)
                        ready_lat <= 1'b1;
                    else
                        wait_cnt <= wait_cnt + 1;
                end
            end else begin
                // For 0 wait, we don't rely on ready_lat — handled combinationally
                ready_lat <= 1'b0;
            end
        end
    end

    // Generate pready
    assign pready = (MAX_WAIT_CYCLES == 0) ? access_phase : (access_phase && ready_lat);

    // Read logic
    always_comb begin
        if (pready && !pwrite)
            prdata = mem[paddr[9:0]];
        else
            prdata = 32'h0;
    end

    // Write logic
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            for (int i = 0; i < DEPTH; i++) mem[i] <= 32'h0;
            pslverr <= 1'b0;
        end else begin
            pslverr <= 1'b0;
            if (pready && pwrite)
                mem[paddr[9:0]] <= pwdata;
        end
    end

endmodule

