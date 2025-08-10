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
      parameter int unsigned AxiID_WIDTH       = 32'd8,
      /// AXI4+ATOP user width.
      parameter int unsigned AxiUSER_WIDTH     = 32'd8
    )
    (
        input logic clk_i, reset_i,
        
        // Core Intsruction Interface
        CORE_INST_INF.Slave CORE_inst_inf_i,
        
        AXI_BUS.Slave axi_slv
    );
    
    localparam integer MEM_ADDR_WIDTH = 25;
    
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
        32'd1,
        soc_addr_rules_pkg::ROM_ADDR_RULE.start_addr,
        soc_addr_rules_pkg::ROM_ADDR_RULE.end_addr
    };
    
    _addr_rule_t DECODER_INST_SRAM_ADDR_RULE = {
        32'd0,
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
      DECODER_INST_SRAM_ADDR_RULE,
      DECODER_ROM_ADDR_RULE
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
    
    logic axi_mem_if_SP_i_cen, axi_mem_if_SP_i_wen;
    logic [31:0] axi_mem_if_SP_i_data_addr;
    logic [3:0] axi_mem_if_SP_i_data_be;
    logic [31:0] axi_mem_if_SP_i_data_wdata;
    // logic data_gnt;
    // logic data_rvalid;
    logic [31:0] axi_mem_if_SP_i_data_rdata;

    assign AXI4_ADAP_inf_w.data_req     = ~axi_mem_if_SP_i_cen;
    assign AXI4_ADAP_inf_w.data_we      = ~axi_mem_if_SP_i_wen;
    assign AXI4_ADAP_inf_w.data_addr    = axi_mem_if_SP_i_data_addr;
    assign AXI4_ADAP_inf_w.data_be      = axi_mem_if_SP_i_data_be;
    assign AXI4_ADAP_inf_w.data_wdata   = axi_mem_if_SP_i_data_wdata;
    assign axi_mem_if_SP_i_data_rdata   = AXI4_ADAP_inf_w.data_rdata;
    
    axi_mem_if_SP #(
        .AXI4_ADDRESS_WIDTH ( AxiAddrWidth                      ),
        .AXI4_RDATA_WIDTH   ( AxiDataWidth                      ),
        .AXI4_WDATA_WIDTH   ( AxiDataWidth                      ),
        .AXI4_ID_WIDTH      ( AxiID_WIDTH                       ),
        .AXI4_USER_WIDTH    ( AxiUSER_WIDTH                     ),
        .MEM_ADDR_WIDTH     ( MEM_ADDR_WIDTH                    )
    ) axi_mem_if_SP_i (
        .ACLK               ( clk_i                             ),
        .ARESETn            ( ~reset_i                          ),
        .test_en_i          ( 1'b0                              ),
        
        .AWID_i             ( axi_slv.aw_id                     ),
        .AWADDR_i           ( axi_slv.aw_addr                   ),
        .AWLEN_i            ( axi_slv.aw_len                    ),
        .AWSIZE_i           ( axi_slv.aw_size                   ),
        .AWBURST_i          ( axi_slv.aw_burst                  ),
        .AWLOCK_i           ( axi_slv.aw_lock                   ),
        .AWCACHE_i          ( axi_slv.aw_cache                  ),
        .AWPROT_i           ( axi_slv.aw_prot                   ),
        .AWREGION_i         ( axi_slv.aw_region                 ),
        .AWUSER_i           ( axi_slv.aw_user                   ),
        .AWQOS_i            ( axi_slv.aw_qos                    ),
        .AWVALID_i          ( axi_slv.aw_valid                  ),
        .AWREADY_o          ( axi_slv.aw_ready                  ),
        
        .WDATA_i            ( axi_slv.w_data                    ),
        .WSTRB_i            ( axi_slv.w_strb                    ),
        .WLAST_i            ( axi_slv.w_last                    ),
        .WUSER_i            ( axi_slv.w_user                    ),
        .WVALID_i           ( axi_slv.w_valid                   ),
        .WREADY_o           ( axi_slv.w_ready                   ),
        
        .BID_o              ( axi_slv.b_id                      ),
        .BRESP_o            ( axi_slv.b_resp                    ),
        .BVALID_o           ( axi_slv.b_valid                   ),
        .BUSER_o            ( axi_slv.b_user                    ),
        .BREADY_i           ( axi_slv.b_ready                   ),
        
        .ARID_i             ( axi_slv.ar_id                     ),
        .ARADDR_i           ( axi_slv.ar_addr                   ),
        .ARLEN_i            ( axi_slv.ar_len                    ),
        .ARSIZE_i           ( axi_slv.ar_size                   ),
        .ARBURST_i          ( axi_slv.ar_burst                  ),
        .ARLOCK_i           ( axi_slv.ar_lock                   ),
        .ARCACHE_i          ( axi_slv.ar_cache                  ),
        .ARPROT_i           ( axi_slv.ar_prot                   ),
        .ARREGION_i         ( axi_slv.ar_region                 ),
        .ARUSER_i           ( axi_slv.ar_user                   ),
        .ARQOS_i            ( axi_slv.ar_qos                    ),
        .ARVALID_i          ( axi_slv.ar_valid                  ),
        .ARREADY_o          ( axi_slv.ar_ready                  ),
        
        .RID_o              ( axi_slv.r_id                      ),
        .RDATA_o            ( axi_slv.r_data                    ),
        .RRESP_o            ( axi_slv.r_resp                    ),
        .RLAST_o            ( axi_slv.r_last                    ),
        .RUSER_o            ( axi_slv.r_user                    ),
        .RVALID_o           ( axi_slv.r_valid                   ),
        .RREADY_i           ( axi_slv.r_ready                   ),
        
        .CEN_o              ( axi_mem_if_SP_i_cen               ),
        .WEN_o              ( axi_mem_if_SP_i_wen               ),
        .A_o                ( axi_mem_if_SP_i_data_addr         ),
        .D_o                ( axi_mem_if_SP_i_data_wdata        ),
        .BE_o               ( axi_mem_if_SP_i_data_be           ),
        .Q_i                ( axi_mem_if_SP_i_data_rdata        )
    );
    
    // Interface Decoder Part
    assign ROM_inst_inf_w.instr_addr        = CORE_inst_inf_i.instr_addr;
    assign DECODER_port2_inf_w.instr_addr   = CORE_inst_inf_i.instr_addr;
    
    assign CORE_inst_inf_i.instr_gnt        = (INST_Intf_decoder_sel_w) ? ROM_inst_inf_w.instr_gnt      : DECODER_port2_inf_w.instr_gnt;   
    assign CORE_inst_inf_i.instr_rvalid     = (INST_Intf_decoder_sel_w) ? ROM_inst_inf_w.instr_rvalid   : DECODER_port2_inf_w.instr_rvalid;
    assign CORE_inst_inf_i.instr_rdata      = (INST_Intf_decoder_sel_w) ? ROM_inst_inf_w.instr_rdata    : DECODER_port2_inf_w.instr_rdata; 
    
    assign ROM_inst_inf_w.instr_req         = (INST_Intf_decoder_sel_w) ? CORE_inst_inf_i.instr_req : 0;
    assign DECODER_port2_inf_w.instr_req    = (INST_Intf_decoder_sel_w) ? 0 : CORE_inst_inf_i.instr_req;
    
    // Interface Arbiter Part
    assign INST_Intf_arbiter_valid_list_w[0] = INF_CVT_inf_w.data_req;
    assign INST_Intf_arbiter_valid_list_w[1] = AXI4_ADAP_inf_w.data_req;
    
    assign AXI4_ADAP_inf_w.data_rdata   = SRAM_data_inf_w.data_rdata;
    assign INF_CVT_inf_w.data_rdata     = SRAM_data_inf_w.data_rdata;
    
    assign SRAM_data_inf_w.data_addr    = (INST_Intf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_addr     : INF_CVT_inf_w.data_addr; 
    assign SRAM_data_inf_w.data_req     = (INST_Intf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_req      : INF_CVT_inf_w.data_req;  
    assign SRAM_data_inf_w.data_we      = (INST_Intf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_we       : INF_CVT_inf_w.data_we;   
    assign SRAM_data_inf_w.data_be      = (INST_Intf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_be       : INF_CVT_inf_w.data_be;   
    assign SRAM_data_inf_w.data_wdata   = (INST_Intf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_wdata    : INF_CVT_inf_w.data_wdata;
    
    assign AXI4_ADAP_inf_w.data_gnt     = (INST_Intf_arbiter_sel_w) ? SRAM_data_inf_w.data_gnt      : 0;
    assign AXI4_ADAP_inf_w.data_rvalid  = (INST_Intf_arbiter_sel_w) ? SRAM_data_inf_w.data_rvalid   : 0;
    
    assign INF_CVT_inf_w.data_gnt       = (INST_Intf_arbiter_sel_w) ? 0 : SRAM_data_inf_w.data_gnt;
    assign INF_CVT_inf_w.data_rvalid    = (INST_Intf_arbiter_sel_w) ? 0 : SRAM_data_inf_w.data_rvalid;
    
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






















