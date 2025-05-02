`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.04.2025 11:31:22
// Design Name: 
// Module Name: core_instruction_top
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

`include "soc_configuration.svh"
`include "soc_interface_list.svh"

module core_instruction_top
    #(parameter
            ROM_SIZE_IN_BYTE = 1024,
            INST_MEM_SIZE_IN_KB = 8
    )
    (
        input logic clk_i, reset_i,
        
        // Core Intsruction Interface
        input CORE_INST_INF_M2S CORE_inst_inf_m2s,
        output CORE_INST_INF_S2M CORE_inst_inf_s2m
    );
    
    logic INSTRUCTION_intereface_decoder_sel_w;
    logic INSTRUCTION_intereface_arbiter_sel_w;
    
    logic [1:0] INSTRUCTION_intereface_arbiter_valid_list_w;
    
    CORE_INST_INF ROM_inst_inf_w;
    CORE_DATA_INF SRAM_data_inf_w;
    CORE_INST_INF DECODER_port2_inf_w;
    CORE_DATA_INF INF_CVT_inf_w;
    CORE_DATA_INF AXI4_ADAP_inf_w;
    
    cv32e_inst2data_inf_cvt
    INTERFACE_CVT_INST2DATA
    (
        .inst_slave_inf_m2s(DECODER_port2_inf_w.m2s),
        .inst_slave_inf_s2m(DECODER_port2_inf_w.s2m),
        
        .data_master_inf_s2m(INF_CVT_inf_w.s2m),
        .data_master_inf_m2s(INF_CVT_inf_w.m2s)
    );
    
    interface_arbiter
    #(
        .IN_COUNT(2)
    )
    INTERFACE_ARBITER
    (
        .clk_i(clk_i), .reset_i(reset_i),
        
        .valid_list_i(INSTRUCTION_intereface_arbiter_valid_list_w),
        .sel_o(INSTRUCTION_intereface_arbiter_sel_w)
    );
    
    inst_rom
    #( 
        .SIZE_IN_BYTE(ROM_SIZE_IN_BYTE)
    )
    INSTRUCTION_ROM
    (
        .clk_i(clk_i),
        
        .cv32_inst_inf_m2s(ROM_inst_inf_w.m2s),
        .cv32_inst_inf_s2m(ROM_inst_inf_w.s2m)
    );
    
    inst_memory
    #(
        .SIZE_IN_KB(INST_MEM_SIZE_IN_KB)
    )
    INSTRUCTION_MEMORY
    (
        .clk_i(clk_i),
        
        .cv32_data_inf_m2s(SRAM_data_inf_w.m2s),
        .cv32_data_inf_s2m(SRAM_data_inf_w.s2m)
    );
    
    // Interface Decoder Part
    always_comb begin
        ROM_inst_inf_w.m2s.instr_addr = CORE_inst_inf_m2s.instr_addr;
        DECODER_port2_inf_w.m2s.instr_addr = CORE_inst_inf_m2s.instr_addr;
        
        if (INSTRUCTION_intereface_decoder_sel_w) begin
            CORE_inst_inf_s2m.instr_gnt = ROM_inst_inf_w.s2m.instr_gnt;
            CORE_inst_inf_s2m.instr_rvalid = ROM_inst_inf_w.s2m.instr_rvalid;
            CORE_inst_inf_s2m.instr_rdata = ROM_inst_inf_w.s2m.instr_rdata;
        end else begin
            CORE_inst_inf_s2m.instr_gnt = DECODER_port2_inf_w.s2m.instr_gnt;
            CORE_inst_inf_s2m.instr_rvalid = DECODER_port2_inf_w.s2m.instr_rvalid;
            CORE_inst_inf_s2m.instr_rdata = DECODER_port2_inf_w.s2m.instr_rdata;
        end
        
        if (INSTRUCTION_intereface_decoder_sel_w) begin
            ROM_inst_inf_w.m2s.instr_req = CORE_inst_inf_m2s.instr_req;
            DECODER_port2_inf_w.m2s.instr_req = 0;
        end else begin
            ROM_inst_inf_w.m2s.instr_req = 0;
            DECODER_port2_inf_w.m2s.instr_req = CORE_inst_inf_m2s.instr_req;
        end
    end
    
    // Interface Arbiter Part
    always_comb begin
        INSTRUCTION_intereface_arbiter_valid_list_w[0] = INF_CVT_inf_w.m2s.data_req;
        INSTRUCTION_intereface_arbiter_valid_list_w[1] = AXI4_ADAP_inf_w.m2s.data_req;
        
        AXI4_ADAP_inf_w.s2m.data_rdata = SRAM_data_inf_w.s2m.data_rdata;
        INF_CVT_inf_w.s2m.data_rdata = SRAM_data_inf_w.s2m.data_rdata;
        
        if (INSTRUCTION_intereface_arbiter_sel_w) begin
            SRAM_data_inf_w.m2s.data_addr = AXI4_ADAP_inf_w.m2s.data_addr;
            SRAM_data_inf_w.m2s.data_req = AXI4_ADAP_inf_w.m2s.data_req;
            SRAM_data_inf_w.m2s.data_we = AXI4_ADAP_inf_w.m2s.data_we;
            SRAM_data_inf_w.m2s.data_be = AXI4_ADAP_inf_w.m2s.data_be;
            SRAM_data_inf_w.m2s.data_wdata = AXI4_ADAP_inf_w.m2s.data_wdata;
        end else begin
            SRAM_data_inf_w.m2s.data_addr = INF_CVT_inf_w.m2s.data_addr;
            SRAM_data_inf_w.m2s.data_req = INF_CVT_inf_w.m2s.data_req;
            SRAM_data_inf_w.m2s.data_we = INF_CVT_inf_w.m2s.data_we;
            SRAM_data_inf_w.m2s.data_be = INF_CVT_inf_w.m2s.data_be;
            SRAM_data_inf_w.m2s.data_wdata = INF_CVT_inf_w.m2s.data_wdata;
        end
        
        if (INSTRUCTION_intereface_arbiter_sel_w) begin
            AXI4_ADAP_inf_w.s2m.data_gnt = SRAM_data_inf_w.s2m.data_gnt;
            AXI4_ADAP_inf_w.s2m.data_rvalid = SRAM_data_inf_w.s2m.data_rvalid;
            
            INF_CVT_inf_w.s2m.data_gnt = 0;
            INF_CVT_inf_w.s2m.data_rvalid = 0;
        end else begin
            AXI4_ADAP_inf_w.s2m.data_gnt = 0;
            AXI4_ADAP_inf_w.s2m.data_rvalid = 0;
            
            INF_CVT_inf_w.s2m.data_gnt = SRAM_data_inf_w.s2m.data_gnt;
            INF_CVT_inf_w.s2m.data_rvalid = SRAM_data_inf_w.s2m.data_rvalid;
        end
    end
    
endmodule






















