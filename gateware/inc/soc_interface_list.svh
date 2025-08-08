// Copyright 2025 Yeditepe Üniversitesi Sayısal Tasarım Topluluğu.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       M. Furkan UZUN - @mfu                                      //
//                                                                            //
//                                                                            //
// Design Name:    CV32E40P Instruction and Data Memory Interfaces            //
// Project Name:   7Yonga                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    CV32E40P Instruction and Data Memory Interfaces tanımları  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`ifndef __SOC_INTERFACE_LIST_SVH__
`define __SOC_INTERFACE_LIST_SVH__

interface CORE_INST_INF #();
    logic [31:0] instr_addr;
    logic instr_req;
    logic instr_gnt;
    logic instr_rvalid;
    logic [31:0] instr_rdata;
    
  modport Master (
    output instr_addr, instr_req,
    input instr_gnt, instr_rvalid, instr_rdata
  );

  modport Slave (
    output instr_gnt, instr_rvalid, instr_rdata,
    input instr_addr, instr_req
  );

endinterface

interface CORE_DATA_INF #();
    logic [31:0] data_addr;
    logic data_req;
    logic data_we;
    logic [3:0] data_be;
    logic [31:0] data_wdata;
    logic data_gnt;
    logic data_rvalid;
    logic [31:0] data_rdata;
    
  modport Master (
    output data_addr, data_req, data_we, data_be, data_wdata,
    input data_gnt, data_rvalid, data_rdata
  );

  modport Slave (
    output data_gnt, data_rvalid, data_rdata,
    input data_addr, data_req, data_we, data_be, data_wdata
  );

endinterface

interface SOC_PERIPHERAL_INF #();
  logic UART0_rx;
  logic UART0_tx;

  modport Master (
    output UART0_rx,
    input UART0_tx
  );

  modport Slave (
    output UART0_tx,
    input UART0_rx
  );

endinterface
/*
interface AXI_BUS #();
  logic [S_COUNT*S_ID_WIDTH-1:0]    awid;
  logic [S_COUNT*ADDR_WIDTH-1:0]    awaddr;
  logic [S_COUNT*8-1:0]             awlen;
  logic [S_COUNT*3-1:0]             awsize;
  logic [S_COUNT*2-1:0]             awburst;
  logic [S_COUNT-1:0]               awlock;
  logic [S_COUNT*4-1:0]             awcache;
  logic [S_COUNT*3-1:0]             awprot;
  logic [S_COUNT*4-1:0]             awqos;
  logic [S_COUNT*AWUSER_WIDTH-1:0]  awuser;
  logic [S_COUNT-1:0]               awvalid;
  logic [S_COUNT-1:0]               awready;
  logic [S_COUNT*DATA_WIDTH-1:0]    wdata;
  logic [S_COUNT*STRB_WIDTH-1:0]    wstrb;
  logic [S_COUNT-1:0]               wlast;
  logic [S_COUNT*WUSER_WIDTH-1:0]   wuser;
  logic [S_COUNT-1:0]               wvalid;
  logic [S_COUNT-1:0]               wready;
  logic [S_COUNT*S_ID_WIDTH-1:0]    bid;
  logic [S_COUNT*2-1:0]             bresp;
  logic [S_COUNT*BUSER_WIDTH-1:0]   buser;
  logic [S_COUNT-1:0]               bvalid;
  logic [S_COUNT-1:0]               bready;
  logic [S_COUNT*S_ID_WIDTH-1:0]    arid;
  logic [S_COUNT*ADDR_WIDTH-1:0]    araddr;
  logic [S_COUNT*8-1:0]             arlen;
  logic [S_COUNT*3-1:0]             arsize;
  logic [S_COUNT*2-1:0]             arburst;
  logic [S_COUNT-1:0]               arlock;
  logic [S_COUNT*4-1:0]             arcache;
  logic [S_COUNT*3-1:0]             arprot;
  logic [S_COUNT*4-1:0]             arqos;
  logic [S_COUNT*ARUSER_WIDTH-1:0]  aruser;
  logic [S_COUNT-1:0]               arvalid;
  logic [S_COUNT-1:0]               arready;
  logic [S_COUNT*S_ID_WIDTH-1:0]    rid;
  logic [S_COUNT*DATA_WIDTH-1:0]    rdata;
  logic [S_COUNT*2-1:0]             rresp;
  logic [S_COUNT-1:0]               rlast;
  logic [S_COUNT*RUSER_WIDTH-1:0]   ruser;
  logic [S_COUNT-1:0]               rvalid;
  logic [S_COUNT-1:0]               rready;

  modport Master (
    output awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awuser, awvalid,
    input awready,
    output wdata, wstrb, wlast, wuser, wvalid,
    input wready,
    input bid, bresp, buser, bvalid,
    output bready,
    output arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, aruser, arvalid,
    input arready,
    input rid, rdata, rresp, rlast, ruser, rvalid,
    output rready,
  );

  modport Slave (
    input awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awuser, awvalid,
    output awready,
    input wdata, wstrb, wlast, wuser, wvalid,
    output wready,
    output bid, bresp, buser, bvalid,
    input bready,
    input arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, aruser, arvalid,
    output arready,
    output rid, rdata, rresp, rlast, ruser, rvalid,
    input rready,
  );

endinterface
*/

`endif //__SOC_INTERFACE_LIST_SVH__










