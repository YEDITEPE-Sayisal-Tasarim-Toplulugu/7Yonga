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
            SIZE_IN_KB                  = 8,
            ADDR_WIDTH                  = 32,
            DATA_WIDTH                  = 32,
            BE_WIDTH                    = 4
    )
    (
        input logic clk_i, reset_ni,

        input   logic [ADDR_WIDTH-1:0]  data_addr_i,
        input   logic                   data_req_i,
        input   logic                   data_we_i,
        input   logic [BE_WIDTH-1:0]    data_be_i,
        input   logic [DATA_WIDTH-1:0]  data_wdata_i,
        output  logic                   data_gnt_o,
        output  logic                   data_rvalid_o,
        output  logic [DATA_WIDTH-1:0]  data_rdata_o
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

        .ena(data_req_i),
        .addra(data_addr_i[2+:ADDR_WIDTH-2]),

        .wea({(BE_WIDTH){data_we_i}} & data_be_i),
        .dina(data_wdata_i),

        .douta(data_rdata_o)
    );

    assign data_gnt_o = 1'b1;
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            data_rvalid_o  <= 0;
        end else begin
            data_rvalid_o  <= data_req_i;
        end
    end
end else if (soc_config_pkg::USE_BRAM_MEMORY_MODULES) begin
    blk_mem BRAM_MEMORY (
        .clka(clk_i),                                   // input wire clka
        .ena(data_req_i),                               // input wire ena
        .wea({(BE_WIDTH){data_we_i}} & data_be_i),      // input wire [3 : 0] wea
        .addra(data_addr_i[2+:ADDR_WIDTH-2]),           // input wire [12 : 0] addra
        .dina(data_wdata_i),                            // input wire [31 : 0] dina
        .douta(data_rdata_o)                            // output wire [31 : 0] douta
    );
    
    assign data_gnt_o = 1'b1;
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            data_rvalid_o  <= 0;
        end else begin
            data_rvalid_o  <= data_req_i;
        end
    end
end

endmodule

module data_memory
    #(parameter 
            SIZE_IN_KB                  = 8,
            ADDR_WIDTH                  = 32,
            DATA_WIDTH                  = 32,
            BE_WIDTH                    = 4
    )
    (
        input logic clk_i, reset_ni,

        input   logic [ADDR_WIDTH-1:0]  data_addr_i,
        input   logic                   data_req_i,
        input   logic                   data_we_i,
        input   logic [BE_WIDTH-1:0]    data_be_i,
        input   logic [DATA_WIDTH-1:0]  data_wdata_i,
        output  logic                   data_gnt_o,
        output  logic                   data_rvalid_o,
        output  logic [DATA_WIDTH-1:0]  data_rdata_o
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

        .ena(data_req_i),
        .addra(data_addr_i[2+:ADDR_WIDTH-2]),

        .wea({(BE_WIDTH){data_we_i}} & data_be_i),
        .dina(data_wdata_i),

        .douta(data_rdata_o)
    );

    assign data_gnt_o = 1'b1;
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            data_rvalid_o  <= 0;
        end else begin
            data_rvalid_o  <= data_req_i;
        end
    end
end else if (soc_config_pkg::USE_BRAM_MEMORY_MODULES) begin
    blk_mem BRAM_MEMORY (
        .clka(clk_i),                                   // input wire clka
        .ena(data_req_i),                               // input wire ena
        .wea({(BE_WIDTH){data_we_i}} & data_be_i),      // input wire [3 : 0] wea
        .addra(data_addr_i[2+:ADDR_WIDTH-2]),           // input wire [12 : 0] addra
        .dina(data_wdata_i),                            // input wire [31 : 0] dina
        .douta(data_rdata_o)                            // output wire [31 : 0] douta
    );
    
    assign data_gnt_o = 1'b1;
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            data_rvalid_o  <= 0;
        end else begin
            data_rvalid_o  <= data_req_i;
        end
    end
end

endmodule

module inst_rom
    (
        input   logic clk_i, reset_ni,
    
        input   logic [31:0]        instr_addr_i,
        input   logic               instr_req_i,
        output  logic               instr_gnt_o,
        output  logic               instr_rvalid_o,
        output  logic [31:0]        instr_rdata_o
    );

import soc_config_pkg::*;

if (soc_config_pkg::USE_SOFT_ROM_MODULES) begin : SOC_CONFG_SOFT   
    boot_code ROM
    (
        .CLK            ( clk_i                     ),
        .RSTN           ( 1'b1                      ),

        .CSN            ( 1'b0                      ),
        .A              ( instr_addr_i              ),
        .Q              ( instr_rdata_o             )
    );

    assign instr_gnt_o  = 1'b1;
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            instr_rvalid_o  <= 0;
        end else begin
            instr_rvalid_o  <= instr_req_i;
        end
    end
end

endmodule
