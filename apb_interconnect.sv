module apb_interconnect(
  input  logic        pclk,
  input  logic        presetn,
  input  logic        psel,
  input  logic        penable,
  input  logic        pwrite,
  input  logic [31:0] paddr,
  input  logic [31:0] pwdata,
  output logic [31:0] prdata,
  output logic       pready,
  output logic       pslverr,

  // slave 0
  output logic        psel0,
  output logic        penable0,
  input  logic [31:0] prdata0,
  input  logic        pready0,
  input  logic        pslverr0,

  // slave 1
  output logic        psel1,
  output logic        penable1,
  input  logic [31:0] prdata1,
  input  logic        pready1,
  input  logic        pslverr1,

  // slave 2
  output logic        psel2,
  output logic        penable2,
  input  logic [31:0] prdata2,
  input  logic        pready2,
  input  logic        pslverr2,

  // slave 3
  output logic        psel3,
  output logic        penable3,
  input  logic [31:0] prdata3,
  input  logic        pready3,
  input  logic        pslverr3,

  output logic [1:0] active_slave_id
);

  logic addr_error;
 
  // single always_comb drives pselX and penableX using current psel/paddr and forwards penable
 
  always_comb begin
    // defaults
    psel0 = 1'b0; penable0 = 1'b0;
    psel1 = 1'b0; penable1 = 1'b0;
    psel2 = 1'b0; penable2 = 1'b0;
    psel3 = 1'b0; penable3 = 1'b0;
    addr_error = 1'b0;
    active_slave_id = 2'bxx;

    if (psel) begin
      unique case (1'b1)
        (paddr >= 32'h00000001 && paddr <= 32'h000000FF): begin
          psel0 = 1'b1;
          penable0 = penable;
          active_slave_id = 2'b00;
        end
        (paddr >= 32'h00000100 && paddr <= 32'h000001FF): begin
          psel1 = 1'b1;
          penable1 = penable;
          active_slave_id = 2'b01;
        end
        (paddr >= 32'h00000200 && paddr <= 32'h000002FF): begin
          psel2 = 1'b1;
          penable2 = penable;
          active_slave_id = 2'b10;
        end
        (paddr >= 32'h00000300 && paddr <= 32'h000003FF): begin
          psel3 = 1'b1;
          penable3 = penable;
          active_slave_id = 2'b11;
        end
        default: begin
          addr_error = 1'b1;
          active_slave_id = 2'bxx;
        end
      endcase
    end
  end

  // response mux: use captured paddr_r for stability of prdata/pready selection
  always_comb begin
    prdata  = 32'h0;
    pready  = 1'b0;
    pslverr = 1'b0;

    if (addr_error) begin
      prdata  = 32'hDEADDEAD;
      pready  = 1'b1;
      pslverr = 1'b1;
    end else begin
      unique case (1'b1)
        (paddr >= 32'h00000001 && paddr <= 32'h000000FF): begin
          prdata = prdata0; pready = pready0; pslverr = pslverr0;
        end
        (paddr >= 32'h00000100 && paddr <= 32'h000001FF): begin
          prdata = prdata1; pready = pready1; pslverr = pslverr1;
        end
        (paddr >= 32'h00000200 && paddr <= 32'h000002FF): begin
          prdata = prdata2; pready = pready2; pslverr = pslverr2;
        end
        (paddr >= 32'h00000300 && paddr <= 32'h000003FF): begin
          prdata = prdata3; pready = pready3; pslverr = pslverr3;
        end
        default: begin
          prdata = 32'h0; pready = 1'b0; pslverr = 1'b0;
        end
      endcase
    end
  end

endmodule

