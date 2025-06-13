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
// Design Name:    memory_modules                                             //
// Project Name:   7Yonga                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Mikrodenetleyice kullanılacak belleklerin modullerini      //
//                 içerir                                                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps

`include "soc_configuration.svh"
`include "soc_interface_list.svh"

module inst_memory
    #(parameter 
            SIZE_IN_KB = 8
    )
    (
        input logic clk_i,

        CORE_DATA_INF.Slave cv32_data_inf_i
    );

import soc_config_pkg::*;

if (soc_config_pkg::USE_SOFT_MEMORY_MODULES) begin : SOC_CONFG_SOFT
    memory_model_soft
    #(
        .WORD_SIZE_BYTE(4),
        .SIZE_IN_KB(SIZE_IN_KB)
    )
    INST_MEMORY_SOFT_MODEL
    (
        .clka(clk_i),

        .ena(cv32_data_inf_i.data_req),
        .addra(cv32_data_inf_i.data_addr),

        .wea({(4){cv32_data_inf_i.data_we}} & cv32_data_inf_i.data_be),
        .dina(cv32_data_inf_i.data_wdata),

        .douta(cv32_data_inf_i.data_rdata)
    );

    always_ff @(posedge clk_i) begin
        cv32_data_inf_i.data_gnt <= cv32_data_inf_i.data_req;
        cv32_data_inf_i.data_rvalid <= cv32_data_inf_i.data_req & ~cv32_data_inf_i.data_we;
    end
end

endmodule

module data_memory
    #(parameter 
            SIZE_IN_KB = 8
    )
    (
        input logic clk_i,

        CORE_DATA_INF.Slave cv32_data_inf_i
    );

import soc_config_pkg::*;

if (soc_config_pkg::USE_SOFT_MEMORY_MODULES) begin : SOC_CONFG_SOFT
    memory_model_soft
    #(
        .WORD_SIZE_BYTE(4),
        .SIZE_IN_KB(SIZE_IN_KB)
    )
    DATA_MEMORY_SOFT_MODEL
    (
        .clka(clk_i),

        .ena(cv32_data_inf_i.data_req),
        .addra(cv32_data_inf_i.data_addr),

        .wea({(4){cv32_data_inf_i.data_we}} & cv32_data_inf_i.data_be),
        .dina(cv32_data_inf_i.data_wdata),

        .douta(cv32_data_inf_i.data_rdata)
    );

    always_ff @(posedge clk_i) begin
        cv32_data_inf_i.data_gnt <= cv32_data_inf_i.data_req;
        cv32_data_inf_i.data_rvalid <= cv32_data_inf_i.data_req & ~cv32_data_inf_i.data_we;
    end
end

endmodule

module inst_rom
    #(parameter 
            SIZE_IN_BYTE = 1024
    )
    (
        input logic clk_i,
    
        CORE_INST_INF cv32_inst_inf_i
    );

import soc_config_pkg::*;

if (soc_config_pkg::USE_SOFT_ROM_MODULES) begin : SOC_CONFG_SOFT
    memory_model_rom
    #(
        .WORD_SIZE_BITS(32),
        .SIZE_IN_BYTE(SIZE_IN_BYTE)
    )
    SOFT_ROM
    (
        .clk_i(clk_i),

        .read_addr_i(cv32_inst_inf_i.instr_addr),
        .read_data_o(cv32_inst_inf_i.instr_rdata)
    );

    always_ff @(posedge clk_i) begin
        cv32_inst_inf_i.instr_gnt <= cv32_inst_inf_i.instr_req;
        cv32_inst_inf_i.instr_rvalid <= cv32_inst_inf_i.instr_req;
    end
end

endmodule