`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.04.2025 11:42:14
// Design Name: 
// Module Name: cv32e_inst2data_inf_cvt
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`include "soc_interface_list.svh"

module cv32e_inst2data_inf_cvt
    #(parameter
            CORE_ADDR_WIDTH                 = 32,
            CORE_DATA_WIDTH                 = 32,
            CORE_BE_WIDTH                   = 4
    )
    (
        input   logic [CORE_ADDR_WIDTH-1:0] instr_addr_i,
        input   logic                       instr_req_i,
        output  logic                       instr_gnt_o,
        output  logic                       instr_rvalid_o,
        output  logic [31:0]                instr_rdata_o,
        
        output  logic [CORE_ADDR_WIDTH-1:0] data_addr_o,
        output  logic                       data_req_o,
        output  logic                       data_we_o,
        output  logic [CORE_BE_WIDTH-1:0]   data_be_o,
        output  logic [CORE_DATA_WIDTH-1:0] data_wdata_o,
        input   logic                       data_gnt_i,
        input   logic                       data_rvalid_i,
        input   logic [CORE_DATA_WIDTH-1:0] data_rdata_i
    );
    
    assign data_addr_o      = instr_addr_i;
    assign data_req_o       = instr_req_i;
    assign data_we_o        = 0;
    assign data_be_o        = 0;
    assign data_wdata_o     = 0;
    
    assign instr_gnt_o      = data_gnt_i;
    assign instr_rvalid_o   = data_rvalid_i;
    assign instr_rdata_o    = data_rdata_i;
    
endmodule




















