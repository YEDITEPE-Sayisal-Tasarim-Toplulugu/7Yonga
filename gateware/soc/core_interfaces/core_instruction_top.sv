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
`include "soc_addr_rules.svh"

import soc_addr_rules_pkg::*;

module core_instruction_top
    #(parameter
            ROM_SIZE_IN_BYTE = 1024,
            INST_MEM_SIZE_IN_KB = 8,
            
      /// AXI4-Lite address width.
      parameter int unsigned    AxiAddrWidth    = 32'd32,
      /// Data width in bit of the memory request data **and** the Axi4-Lite data channels.
      parameter int unsigned    AxiDataWidth       = 32'd32,
      /// AXI4+ATOP ID width.
      parameter int unsigned AxiID_WIDTH       = 32'd0,
      /// AXI4+ATOP user width.
      parameter int unsigned AxiUSER_WIDTH     = 32'd0
    )
    (
        input logic clk_i, reset_i,
        
        // Core Intsruction Interface
        CORE_INST_INF.Slave CORE_inst_inf_i,
        
        AXI_BUS.Slave slv
    );
    
    logic INST_Intf_decoder_valid_w;
    logic INST_Intf_decoder_error_w;
    logic INST_Intf_decoder_sel_w;
    
    logic [1:0] INST_Intf_arbiter_valid_list_w;
    logic INST_Intf_arbiter_sel_w;
    
    CORE_INST_INF ROM_inst_inf_w();
    CORE_DATA_INF SRAM_data_inf_w();
    CORE_INST_INF DECODER_port2_inf_w();
    CORE_DATA_INF INF_CVT_inf_w();
    CORE_DATA_INF AXI4_ADAP_inf_w();
    
    typedef struct packed {
        int unsigned idx;
        soc_addr_rules_pkg::addr_t       start_addr;
        soc_addr_rules_pkg::addr_t       end_addr;
    } _addr_rule_t;
    
    _addr_rule_t DECODER_ROM_ADDR_RULE = {
        32'd0,
        soc_addr_rules_pkg::ROM_ADDR_RULE.start_addr,
        soc_addr_rules_pkg::ROM_ADDR_RULE.end_addr
    };
    
    _addr_rule_t DECODER_INST_SRAM_ADDR_RULE = {
        32'd1,
        soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.start_addr,
        soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.end_addr
    };
    
    addr_decode #(
      /// Highest index which can happen in a rule.
      .NoIndices(2),
      /// Total number of rules.
      .NoRules(2),
      /// Address type inside the rules and to decode.
      .addr_t(soc_addr_rules_pkg::addr_t),
      /// Rule packed struct type.
      .rule_t(_addr_rule_t),
      // Whether this is a NAPOT (base and mask) or regular range decoder
      .Napot(0)
    )
    CORE_INST_INF_ADDR_DECODER
    (
      /// Address to decode.
      .addr_i(CORE_inst_inf_i.instr_addr),
      /// Address map: rule with the highest array position wins on collision
      .addr_map_i({
      DECODER_ROM_ADDR_RULE,
      DECODER_INST_SRAM_ADDR_RULE
      }),
      /// Decoded index.
      .idx_o(INST_Intf_decoder_sel_w),
      /// Decode is valid.
      .dec_valid_o(INST_Intf_decoder_valid_w),
      /// Decode is not valid, no matching rule found.
      .dec_error_o(INST_Intf_decoder_error_w),
      /// Enable default port mapping.
      ///
      /// When not used, tie to `0`.
      .en_default_idx_i(0),
      /// Default port index.
      ///
      /// When `en_default_idx_i` is `1`, this will be the index when no rule matches.
      ///
      /// When not used, tie to `0`.
      .default_idx_i(0)
    );
    
    cv32e_inst2data_inf_cvt
    INTERFACE_CVT_INST2DATA
    (
        .inst_slave_inf(DECODER_port2_inf_w),
        .data_master_inf(INF_CVT_inf_w)
    );
    
    interface_arbiter
    #(
        .IN_COUNT(2)
    )
    INTERFACE_ARBITER
    (
        .clk_i(clk_i), .reset_i(reset_i),
        
        .valid_list_i(INST_Intf_arbiter_valid_list_w),
        .sel_o(INST_Intf_arbiter_sel_w)
    );
    
    inst_rom
    #( 
        .SIZE_IN_BYTE(ROM_SIZE_IN_BYTE)
    )
    INSTRUCTION_ROM
    (
        .clk_i(clk_i),
        
        .cv32_inst_inf_i(ROM_inst_inf_w)
    );
    
    inst_memory
    #(
        .SIZE_IN_KB(INST_MEM_SIZE_IN_KB)
    )
    INSTRUCTION_MEMORY
    (
        .clk_i(clk_i),
        
        .cv32_data_inf_i(SRAM_data_inf_w)
    );
    
    axi_to_mem_intf #(
      /// See `axi_to_mem`, parameter `AddrWidth`.
      .ADDR_WIDTH     ( AxiAddrWidth),
      /// See `axi_to_mem`, parameter `DataWidth`.
      .DATA_WIDTH     ( AxiDataWidth),
      /// AXI4+ATOP ID width.
      .ID_WIDTH       ( AxiID_WIDTH),
      /// AXI4+ATOP user width.
      .USER_WIDTH     ( AxiUSER_WIDTH),
      /// See `axi_to_mem`, parameter `NumBanks`.
      .NUM_BANKS      ( 32'd1),
      /// See `axi_to_mem`, parameter `BufDepth`.
      .BUF_DEPTH      ( 32'd1),
      /// Hide write requests if the strb == '0
      .HIDE_STRB      ( 1'b0),
      /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
      .OUT_FIFO_DEPTH ( 32'd1)
    )
    AXI4_ADAPTER_AXI4_TO_MEM
    (
      /// Clock input.
      .clk_i(clk_i),
      /// Asynchronous reset, active low.
      .rst_ni(~reset_i),
      /// See `axi_to_mem`, port `busy_o`.
      .busy_o(),
      /// AXI4+ATOP slave interface port.
      .slv(slv),
      /// See `axi_to_mem`, port `mem_req_o`.
      .mem_req_o(AXI4_ADAP_inf_w.data_req),
      /// See `axi_to_mem`, port `mem_gnt_i`.
      .mem_gnt_i(AXI4_ADAP_inf_w.data_gnt),
      /// See `axi_to_mem`, port `mem_addr_o`.
      .mem_addr_o(AXI4_ADAP_inf_w.data_addr),
      /// See `axi_to_mem`, port `mem_wdata_o`.
      .mem_wdata_o(AXI4_ADAP_inf_w.data_wdata),
      /// See `axi_to_mem`, port `mem_strb_o`.
      .mem_strb_o(AXI4_ADAP_inf_w.data_be),
      /// See `axi_to_mem`, port `mem_atop_o`.
      .mem_atop_o(),
      /// See `axi_to_mem`, port `mem_we_o`.
      .mem_we_o(AXI4_ADAP_inf_w.data_we),
      /// See `axi_to_mem`, port `mem_rvalid_i`.
      .mem_rvalid_i(AXI4_ADAP_inf_w.data_rvalid),
      /// See `axi_to_mem`, port `mem_rdata_i`.
      .mem_rdata_i(AXI4_ADAP_inf_w.data_rdata)
    );
    
    // Interface Decoder Part
    always_comb begin
        ROM_inst_inf_w.instr_addr = CORE_inst_inf_i.instr_addr;
        DECODER_port2_inf_w.instr_addr = CORE_inst_inf_i.instr_addr;
        
        if (INST_Intf_decoder_sel_w) begin
            CORE_inst_inf_i.instr_gnt     = ROM_inst_inf_w.instr_gnt;
            CORE_inst_inf_i.instr_rvalid  = ROM_inst_inf_w.instr_rvalid;
            CORE_inst_inf_i.instr_rdata   = ROM_inst_inf_w.instr_rdata;
        end else begin
            CORE_inst_inf_i.instr_gnt     = DECODER_port2_inf_w.instr_gnt;
            CORE_inst_inf_i.instr_rvalid  = DECODER_port2_inf_w.instr_rvalid;
            CORE_inst_inf_i.instr_rdata   = DECODER_port2_inf_w.instr_rdata;
        end
        
        if (INST_Intf_decoder_sel_w) begin
            ROM_inst_inf_w.instr_req = CORE_inst_inf_i.instr_req;
            DECODER_port2_inf_w.instr_req = 0;
        end else begin
            ROM_inst_inf_w.instr_req = 0;
            DECODER_port2_inf_w.instr_req = CORE_inst_inf_i.instr_req;
        end
    end
    
    // Interface Arbiter Part
    always_comb begin
        INST_Intf_arbiter_valid_list_w[0] = INF_CVT_inf_w.data_req;
        INST_Intf_arbiter_valid_list_w[1] = AXI4_ADAP_inf_w.data_req;
        
        AXI4_ADAP_inf_w.data_rdata = SRAM_data_inf_w.data_rdata;
        INF_CVT_inf_w.data_rdata = SRAM_data_inf_w.data_rdata;
        
        if (INST_Intf_arbiter_sel_w) begin
            SRAM_data_inf_w.data_addr   = AXI4_ADAP_inf_w.data_addr;
            SRAM_data_inf_w.data_req    = AXI4_ADAP_inf_w.data_req;
            SRAM_data_inf_w.data_we     = AXI4_ADAP_inf_w.data_we;
            SRAM_data_inf_w.data_be     = AXI4_ADAP_inf_w.data_be;
            SRAM_data_inf_w.data_wdata  = AXI4_ADAP_inf_w.data_wdata;
        end else begin
            SRAM_data_inf_w.data_addr   = INF_CVT_inf_w.data_addr;
            SRAM_data_inf_w.data_req    = INF_CVT_inf_w.data_req;
            SRAM_data_inf_w.data_we     = INF_CVT_inf_w.data_we;
            SRAM_data_inf_w.data_be     = INF_CVT_inf_w.data_be;
            SRAM_data_inf_w.data_wdata  = INF_CVT_inf_w.data_wdata;
        end
        
        if (INST_Intf_arbiter_sel_w) begin
            AXI4_ADAP_inf_w.data_gnt = SRAM_data_inf_w.data_gnt;
            AXI4_ADAP_inf_w.data_rvalid = SRAM_data_inf_w.data_rvalid;
            
            INF_CVT_inf_w.data_gnt = 0;
            INF_CVT_inf_w.data_rvalid = 0;
        end else begin
            AXI4_ADAP_inf_w.data_gnt = 0;
            AXI4_ADAP_inf_w.data_rvalid = 0;
            
            INF_CVT_inf_w.data_gnt = SRAM_data_inf_w.data_gnt;
            INF_CVT_inf_w.data_rvalid = SRAM_data_inf_w.data_rvalid;
        end
    end
    
    ////////////////////////////////////////////////////////////////////////////////////
    //                                   ASSERTIONS                                   //
    ////////////////////////////////////////////////////////////////////////////////////
    property p_instr_req_no_decoder_error;
        @(posedge clk_i)
        disable iff (reset_i)
        CORE_inst_inf_i.instr_req |-> !INST_Intf_decoder_error_w;
    endproperty
    
    assert property (p_instr_req_no_decoder_error)
        else $error("Instruction interface decoder: error occurred during instruction request.");
    
endmodule






















