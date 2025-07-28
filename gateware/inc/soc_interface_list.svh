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

`endif //__SOC_INTERFACE_LIST_SVH__










