`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.04.2025 11:31:22
// Design Name: 
// Module Name: core_data_top
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

module core_data_top
    #(parameter
            DATA_MEM_SIZE_IN_KB = 8,

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
        
        CORE_DATA_INF.Slave CORE_data_inf_i,
        
        AXI_BUS.Master axi_master,
        AXI_BUS.Slave axi_slv
    );
    
    localparam integer MEM_ADDR_WIDTH = 25;
    
    CORE_DATA_INF SRAM_data_inf_w();
    CORE_DATA_INF DECODER_port1_inf_w();
    CORE_DATA_INF DECODER_port2_inf_w();
    CORE_DATA_INF AXI4_ADAP_inf_w();
    
    logic DATA_interface_decoder_sel_w,
            DATA_interface_decoder_valid_w,
            DATA_interface_decoder_error_w;
            
    logic [1:0] DATA_inf_arbiter_valid_list_w;
    logic DATA_inf_arbiter_sel_w;
    
    typedef struct packed {
        int unsigned idx;
        soc_addr_rules_pkg::addr_t       start_addr;
        soc_addr_rules_pkg::addr_t       end_addr;
    } _addr_rule_t;
    
    _addr_rule_t DECODER_DATA_AXI_ADDR_RULE = {
        32'd0,
        soc_addr_rules_pkg::AXI_MASTER_ADDR_RULE.start_addr,
        soc_addr_rules_pkg::AXI_MASTER_ADDR_RULE.end_addr
    };
    
    _addr_rule_t DECODER_DATA_SRAM_ADDR_RULE = {
        32'd1,
        soc_addr_rules_pkg::DATA_SRAM_ADDR_RULE.start_addr,
        soc_addr_rules_pkg::DATA_SRAM_ADDR_RULE.end_addr
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
      .addr_i(CORE_data_inf_i.data_addr),
      /// Address map: rule with the highest array position wins on collision
      .addr_map_i({
            DECODER_DATA_SRAM_ADDR_RULE,
            DECODER_DATA_AXI_ADDR_RULE
      }),
      /// Decoded index.
      .idx_o(DATA_interface_decoder_sel_w),
      /// Decode is valid.
      .dec_valid_o(DATA_interface_decoder_valid_w),
      /// Decode is not valid, no matching rule found.
      .dec_error_o(DATA_interface_decoder_error_w),
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
    
    core2axi #(
        .AXI4_ADDRESS_WIDTH ( AxiAddrWidth                      ),
        .AXI4_RDATA_WIDTH   ( AxiDataWidth                      ),
        .AXI4_WDATA_WIDTH   ( AxiDataWidth                      ),
        .AXI4_ID_WIDTH      ( AxiID_WIDTH                       ),
        .AXI4_USER_WIDTH    ( AxiUSER_WIDTH                     )
    ) core2axi_i (
        .clk_i              ( clk_i                             ),
        .rst_ni             ( ~reset_i                          ),
       
        .data_req_i         ( DECODER_port2_inf_w.data_req      ),
        .data_gnt_o         ( DECODER_port2_inf_w.data_gnt      ),
        .data_rvalid_o      ( DECODER_port2_inf_w.data_rvalid   ),
        .data_addr_i        ( DECODER_port2_inf_w.data_addr     ),
        .data_we_i          ( DECODER_port2_inf_w.data_we       ),
        .data_be_i          ( DECODER_port2_inf_w.data_be       ),
        .data_rdata_o       ( DECODER_port2_inf_w.data_rdata    ),
        .data_wdata_i       ( DECODER_port2_inf_w.data_wdata    ),
       
        .aw_id_o            ( axi_master.aw_id                  ),
        .aw_addr_o          ( axi_master.aw_addr                ),
        .aw_len_o           ( axi_master.aw_len                 ),
        .aw_size_o          ( axi_master.aw_size                ),
        .aw_burst_o         ( axi_master.aw_burst               ),
        .aw_lock_o          ( axi_master.aw_lock                ),
        .aw_cache_o         ( axi_master.aw_cache               ),
        .aw_prot_o          ( axi_master.aw_prot                ),
        .aw_region_o        ( axi_master.aw_region              ),
        .aw_user_o          ( axi_master.aw_user                ),
        .aw_qos_o           ( axi_master.aw_qos                 ),
        .aw_valid_o         ( axi_master.aw_valid               ),
        .aw_ready_i         ( axi_master.aw_ready               ),
       
        .w_data_o           ( axi_master.w_data                 ),
        .w_strb_o           ( axi_master.w_strb                 ),
        .w_last_o           ( axi_master.w_last                 ),
        .w_user_o           ( axi_master.w_user                 ),
        .w_valid_o          ( axi_master.w_valid                ),
        .w_ready_i          ( axi_master.w_ready                ),
       
        .b_id_i             ( axi_master.b_id                   ),
        .b_resp_i           ( axi_master.b_resp                 ),
        .b_valid_i          ( axi_master.b_valid                ),
        .b_user_i           ( axi_master.b_user                 ),
        .b_ready_o          ( axi_master.b_ready                ),
       
        .ar_id_o            ( axi_master.ar_id                  ),
        .ar_addr_o          ( axi_master.ar_addr                ),
        .ar_len_o           ( axi_master.ar_len                 ),
        .ar_size_o          ( axi_master.ar_size                ),
        .ar_burst_o         ( axi_master.ar_burst               ),
        .ar_lock_o          ( axi_master.ar_lock                ),
        .ar_cache_o         ( axi_master.ar_cache               ),
        .ar_prot_o          ( axi_master.ar_prot                ),
        .ar_region_o        ( axi_master.ar_region              ),
        .ar_user_o          ( axi_master.ar_user                ),
        .ar_qos_o           ( axi_master.ar_qos                 ),
        .ar_valid_o         ( axi_master.ar_valid               ),
        .ar_ready_i         ( axi_master.ar_ready               ),
       
        .r_id_i             ( axi_master.r_id                   ),
        .r_data_i           ( axi_master.r_data                 ),
        .r_resp_i           ( axi_master.r_resp                 ),
        .r_last_i           ( axi_master.r_last                 ),
        .r_user_i           ( axi_master.r_user                 ),
        .r_valid_i          ( axi_master.r_valid                ),
        .r_ready_o          ( axi_master.r_ready                )
    );
    
    logic axi_mem_if_SP_i_cen, axi_mem_if_SP_i_wen;
    logic [31:0] axi_mem_if_SP_i_data_addr;
    logic [3:0] axi_mem_if_SP_i_data_be;
    logic [31:0] axi_mem_if_SP_i_data_wdata;
    // logic data_gnt;
    // logic data_rvalid;
    logic [31:0] axi_mem_if_SP_i_data_rdata;

    assign AXI4_ADAP_inf_w.data_req = ~axi_mem_if_SP_i_cen;
    assign AXI4_ADAP_inf_w.data_we = ~axi_mem_if_SP_i_wen;
    assign AXI4_ADAP_inf_w.data_addr = axi_mem_if_SP_i_data_addr;
    assign AXI4_ADAP_inf_w.data_be = axi_mem_if_SP_i_data_be;
    assign AXI4_ADAP_inf_w.data_wdata = axi_mem_if_SP_i_data_wdata;
    assign AXI4_ADAP_inf_w.data_rdata = axi_mem_if_SP_i_data_rdata;
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
    
    interface_arbiter
    #(
        .IN_COUNT(2)
    )
    INTERFACE_ARBITER
    (
        .clk_i(clk_i), .reset_i(reset_i),
        
        .valid_list_i(DATA_inf_arbiter_valid_list_w),
        .sel_o(DATA_inf_arbiter_sel_w)
    );
    
    data_memory
    #(
        .SIZE_IN_KB(DATA_MEM_SIZE_IN_KB)
    )
    DATA_MEMORY
    (
        .clk_i(clk_i),
        .cv32_data_inf_i(SRAM_data_inf_w)
    );
    
    // DATA Decoder Part
    assign DECODER_port1_inf_w.data_addr    = CORE_data_inf_i.data_addr;
    assign DECODER_port1_inf_w.data_we      = CORE_data_inf_i.data_we;
    assign DECODER_port1_inf_w.data_be      = CORE_data_inf_i.data_be;
    assign DECODER_port1_inf_w.data_wdata   = CORE_data_inf_i.data_wdata;
    
    assign DECODER_port2_inf_w.data_addr    = CORE_data_inf_i.data_addr;
    assign DECODER_port2_inf_w.data_we      = CORE_data_inf_i.data_we;
    assign DECODER_port2_inf_w.data_be      = CORE_data_inf_i.data_be;
    assign DECODER_port2_inf_w.data_wdata   = CORE_data_inf_i.data_wdata;
    
    assign CORE_data_inf_i.data_gnt         = (DATA_interface_decoder_sel_w) ? DECODER_port1_inf_w.data_gnt     : DECODER_port2_inf_w.data_gnt;   
    assign CORE_data_inf_i.data_rvalid      = (DATA_interface_decoder_sel_w) ? DECODER_port1_inf_w.data_rvalid  : DECODER_port2_inf_w.data_rvalid;
    assign CORE_data_inf_i.data_rdata       = (DATA_interface_decoder_sel_w) ? DECODER_port1_inf_w.data_rdata   : DECODER_port2_inf_w.data_rdata; 
    
    assign DECODER_port1_inf_w.data_req     = (DATA_interface_decoder_sel_w) ? CORE_data_inf_i.data_req : 0;
    assign DECODER_port2_inf_w.data_req     = (DATA_interface_decoder_sel_w) ? 0 : CORE_data_inf_i.data_req;
    
    // Interface Arbiter Part
    assign DATA_inf_arbiter_valid_list_w[0] = DECODER_port1_inf_w.data_req;
    assign DATA_inf_arbiter_valid_list_w[1] = AXI4_ADAP_inf_w.data_req;
    
    assign DECODER_port1_inf_w.data_rdata   = SRAM_data_inf_w.data_rdata;
    assign AXI4_ADAP_inf_w.data_rdata       = SRAM_data_inf_w.data_rdata;
    
    assign SRAM_data_inf_w.data_addr   = (DATA_inf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_addr  : DECODER_port1_inf_w.data_addr; 
    assign SRAM_data_inf_w.data_req    = (DATA_inf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_req   : DECODER_port1_inf_w.data_req;  
    assign SRAM_data_inf_w.data_we     = (DATA_inf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_we    : DECODER_port1_inf_w.data_we;   
    assign SRAM_data_inf_w.data_be     = (DATA_inf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_be    : DECODER_port1_inf_w.data_be;   
    assign SRAM_data_inf_w.data_wdata  = (DATA_inf_arbiter_sel_w) ? AXI4_ADAP_inf_w.data_wdata : DECODER_port1_inf_w.data_wdata;
    
    assign AXI4_ADAP_inf_w.data_gnt    = (DATA_inf_arbiter_sel_w) ? SRAM_data_inf_w.data_gnt    : 0;
    assign AXI4_ADAP_inf_w.data_rvalid = (DATA_inf_arbiter_sel_w) ? SRAM_data_inf_w.data_rvalid : 0;
    
    assign DECODER_port1_inf_w.data_gnt     = (DATA_inf_arbiter_sel_w) ? 0 : SRAM_data_inf_w.data_gnt;
    assign DECODER_port1_inf_w.data_rvalid  = (DATA_inf_arbiter_sel_w) ? 0 : SRAM_data_inf_w.data_rvalid;
    
    ////////////////////////////////////////////////////////////////////////////////////
    //                                   ASSERTIONS                                   //
    ////////////////////////////////////////////////////////////////////////////////////
    property p_data_req_no_decoder_error;
        @(posedge clk_i)
        disable iff (reset_i)
        CORE_data_inf_i.data_req |-> !DATA_interface_decoder_error_w;
    endproperty
    
    assert property (p_data_req_no_decoder_error)
        else $error("DATA interface decoder: error occurred during data request.");
    
endmodule






















