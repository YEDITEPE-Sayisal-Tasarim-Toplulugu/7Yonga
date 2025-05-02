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

typedef struct packed {
    logic [31:0] instr_addr;
    logic instr_req;
} CORE_INST_INF_M2S;

typedef struct packed {
    logic instr_gnt;
    logic instr_rvalid;
    logic [31:0] instr_rdata;
} CORE_INST_INF_S2M;

typedef struct packed {
    CORE_INST_INF_M2S m2s;
    CORE_INST_INF_S2M s2m;
} CORE_INST_INF;

typedef struct packed {
    logic [31:0] data_addr;
    logic data_req;
    logic data_we;
    logic [3:0] data_be;
    logic [31:0] data_wdata;
} CORE_DATA_INF_M2S;

typedef struct packed {
    logic data_gnt;
    logic data_rvalid;
    logic [31:0] data_rdata;
} CORE_DATA_INF_S2M;

typedef struct packed {
    CORE_DATA_INF_M2S m2s;
    CORE_DATA_INF_S2M s2m;
} CORE_DATA_INF;

`endif //__SOC_INTERFACE_LIST_SVH__










