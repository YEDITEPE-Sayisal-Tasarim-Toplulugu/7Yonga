`ifndef AXI_LITE_IF__SV
`define AXI_LITE_IF__SV

`timescale 1ns/1ns

interface axi_lite_if #(
  parameter int ADDR_WIDTH = 32,
  parameter int DATA_WIDTH = 32
)(input bit pclk);

  // Global signals
  logic                 ACLK;
  logic                 ARESETn;

  // Write address channel
  logic [ADDR_WIDTH-1:0] AWADDR;
  logic                 AWVALID;
  logic                 AWREADY;

  // Write data channel
  logic [DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;
  logic                 WVALID;
  logic                 WREADY;

  // Write response channel
  logic [1:0]           BRESP;
  logic                 BVALID;
  logic                 BREADY;

  // Read address channel
  logic [ADDR_WIDTH-1:0] ARADDR;
  logic                 ARVALID;
  logic                 ARREADY;

  // Read data channel
  logic [DATA_WIDTH-1:0] RDATA;
  logic [1:0]           RRESP;
  logic                 RVALID;
  logic                 RREADY;

  // pasif monitoring
  clocking pck @(posedge pclk);
    input AWADDR, AWVALID, AWREADY;

    input WDATA, WSTRB,WVALID,WREADY;

    input BRESP,BVALID,BREADY;

    input ARADDR,ARVALID,ARREADY;

    input RDATA,RRESP,RVALID,RREADY;
  endclocking

  // aktif monitoring
  clocking mck @(posedge pclk);
    output AWADDR, AWVALID;
    input  AWREADY;

    output WDATA, WSTRB, WVALID;
    input  WREADY;

    input  BRESP, BVALID;
    output BREADY;

    output ARADDR, ARVALID;
    input  ARREADY;

    input  RDATA, RRESP, RVALID;
    output RREADY;
  endclocking

  modport passive(clocking pck);
  //modport master(clocking mck);


endinterface

`endif
