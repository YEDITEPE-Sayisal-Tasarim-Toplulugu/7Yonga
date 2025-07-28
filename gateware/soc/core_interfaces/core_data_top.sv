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
    
    CORE_DATA_INF SRAM_data_inf_w();
    CORE_DATA_INF DECODER_port1_inf_w();
    CORE_DATA_INF DECODER_port2_inf_w();
    CORE_DATA_INF AXI4_ADAP_inf_w();
    
    logic DATA_interface_decoder_sel_w,
            DATA_interface_decoder_valid_w,
            DATA_interface_decoder_error_w;
            
    logic [1:0] DATA_inf_arbiter_valid_list_w;
    logic DATA_inf_arbiter_sel_w;
    
    typedef logic [AxiID_WIDTH-1:0]         axi_mst_id_t;
    typedef logic [AxiAddrWidth-1:0]        axi_addr_t;
    typedef logic [AxiDataWidth-1:0]        axi_data_t;
    typedef logic [(AxiDataWidth/8)-1:0]    axi_strb_t;
    typedef logic [AxiUSER_WIDTH-1:0]       axi_user_t;
    
    // Structlar Oluşturulur
    `AXI_TYPEDEF_AW_CHAN_T(axi_mst_aw_t, axi_addr_t, axi_mst_id_t, axi_user_t)
    `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
    `AXI_TYPEDEF_B_CHAN_T(axi_mst_b_t, axi_mst_id_t, axi_user_t)
    `AXI_TYPEDEF_AR_CHAN_T(axi_mst_ar_t, axi_addr_t, axi_mst_id_t, axi_user_t)
    `AXI_TYPEDEF_R_CHAN_T(axi_mst_r_t, axi_data_t, axi_mst_id_t, axi_user_t)
    
    `AXI_TYPEDEF_REQ_T(axi_mst_req_t, axi_mst_aw_t, axi_w_t, axi_mst_ar_t)
    `AXI_TYPEDEF_RESP_T(axi_mst_resp_t, axi_mst_b_t, axi_mst_r_t)
    
    // Oluşturulan struct'lar ile bağlantı kabloları oluşturulur.
    // Bu kablolar adaptörün request ve response portlarına bağlanır.
    axi_mst_req_t   axi_mst_req, axi_mst_req2;
    axi_mst_resp_t  axi_mst_resp;
    
    // Yukarıda oluşturulan kablolar ile 
    // modül arayüzünden gelen interface portu bağlantıları sağlanır.
    `AXI_ASSIGN_FROM_REQ(axi_master, axi_mst_req)
    `AXI_ASSIGN_TO_RESP(axi_mst_resp, axi_master)
    
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
    
    axi_from_mem 
    #(
        /// Memory request address width.
        .MemAddrWidth    ( 32'd32),
        /// AXI4-Lite address width.
        .AxiAddrWidth    ( AxiAddrWidth),
        /// Data width in bit of the memory request data **and** the Axi4-Lite data channels.
        .DataWidth       ( AxiDataWidth),
        /// How many requests can be in flight at the same time. (Depth of the response mux FIFO).
        .MaxRequests     ( 32'd3),
        
        /// AXI4 request struct definition.
        .axi_req_t       ( axi_mst_req_t),
        /// AXI4 response struct definition.
        .axi_rsp_t       ( axi_mst_resp_t)
    ) AXI4_ADAPTER_AXI4_FROM_MEM (
        /// Clock input, positive edge triggered.
        .clk_i(clk_i),
        /// Asynchronous reset, active low.
        .rst_ni(~reset_i),
        /// Memory slave port, request is active.
        .mem_req_i(DECODER_port2_inf_w.data_req),
        /// Memory slave port, request address.
        ///
        /// Byte address, will be extended or truncated to match `AxiAddrWidth`.
        .mem_addr_i(DECODER_port2_inf_w.data_addr),
        /// Memory slave port, request is a write.
        ///
        /// `0`: Read request.
        /// `1`: Write request.
        .mem_we_i(DECODER_port2_inf_w.data_we),
        /// Memory salve port, write data for request.
        .mem_wdata_i(DECODER_port2_inf_w.data_wdata),
        /// Memory slave port, write byte enable for request.
        ///
        /// Active high.
        .mem_be_i(DECODER_port2_inf_w.data_be),
        /// Memory request is granted.
        .mem_gnt_o(DECODER_port2_inf_w.data_gnt),
        /// Memory slave port, response is valid. For each request, regardless if read or write,
        /// this will be active once for one cycle.
        .mem_rsp_valid_o(DECODER_port2_inf_w.data_rvalid),
        /// Memory slave port, response read data. This is forwarded directly from the AXI4-Lite
        /// `R` channel. Only valid for responses generated by a read request.
        .mem_rsp_rdata_o(DECODER_port2_inf_w.data_rdata),
        /// Memory request encountered an error. This is forwarded from the AXI4-Lite error response.
        .mem_rsp_error_o(),
        /// AXI4 master port, slave aw cache signal
        .slv_aw_cache_i('0),
        /// AXI4 master port, slave ar cache signal
        .slv_ar_cache_i('0),
        /// AXI4 master port, request output.
        .axi_req_o(axi_mst_req2),
        /// AXI4 master port, response input.
        .axi_rsp_i(axi_mst_resp)
    );
    
    assign axi_mst_req.aw = axi_mst_req2.aw;
    assign axi_mst_req.aw_valid = axi_mst_req2.aw_valid;
    assign axi_mst_req.w.data = axi_mst_req2.w.data;
    assign axi_mst_req.w.strb = axi_mst_req2.w.strb;
    /*
        axi_lite_to_axi modülünün içinde 52. satırda "last: 1'b1,"
        tanımı ile sabit 1 değeri veriliyor. bu sabit bir sinyali diğer
        modüllerde infinite combinational loop hatasına sebep olmaktadır.
        repoya müdahele edilemediği için hata bu şekilde giderilmiştir.
        sabit bir hata sebebi
        sabit sıfır mantık hatası
        bu yüzden yazma anında w_valid anında 1 diğer anlarda 0 yapılır.
    */
    assign axi_mst_req.w.last = '0; //axi_mst_req2.w_valid; //axi_mst_req2.w.last;
    assign axi_mst_req.w.user = axi_mst_req2.w.user;
    assign axi_mst_req.w_valid = axi_mst_req2.w_valid;
    assign axi_mst_req.b_ready = axi_mst_req2.b_ready;
    assign axi_mst_req.ar = axi_mst_req2.ar;
    assign axi_mst_req.r_ready = axi_mst_req2.r_ready;
    
    // axi_to_mem_intf modulü port içindeki struct yapılarında hata vermektedir.
    // tahminen vivado ile alakalı
    /*
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
      .slv(axi_slv),
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
    */

    typedef logic [AxiID_WIDTH-1:0]     id_t;
    typedef logic [AxiDataWidth-1:0]   data_t;
    typedef logic [AxiDataWidth/8-1:0] strb_t;
    typedef logic [AxiUSER_WIDTH-1:0]   user_t;
    
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
    `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
    `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
    
    req_t   req;
    resp_t  resp;
    
    `AXI_ASSIGN_TO_REQ(req, axi_slv)
    `AXI_ASSIGN_FROM_RESP(axi_slv, resp)

    axi_to_detailed_mem #(
        .axi_req_t    ( req_t    ),
        .axi_resp_t   ( resp_t   ),
        .AddrWidth    ( AxiAddrWidth    ),
        .DataWidth    ( AxiDataWidth    ),
        .IdWidth      ( AxiID_WIDTH      ),
        .UserWidth    ( AxiUSER_WIDTH    ),
        .NumBanks     ( 32'd1     ),
        .BufDepth     ( 32'd1     ),
        .HideStrb     (  1'd0     ),
        .OutFifoDepth ( 32'd1     )
    ) i_axi_to_detailed_mem (
        .clk_i(clk_i),
        .rst_ni(~reset_i),
        .busy_o(),
        .axi_req_i    ( req     ),
        .axi_resp_o   ( resp    ),
        .mem_lock_o   (),
        .mem_id_o     (),
        .mem_user_o   (),
        .mem_cache_o  (),
        .mem_prot_o   (),
        .mem_qos_o    (),
        .mem_region_o (),
        .mem_err_i    ('0),
        .mem_exokay_i ('0),
        
        .mem_req_o(AXI4_ADAP_inf_w.data_req),
        /// See `axi_to_mem`, port `mem_gnt_i`.
        .mem_gnt_i('0), //AXI4_ADAP_inf_w.data_gnt),
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
    always_comb begin
        DECODER_port1_inf_w.data_addr = CORE_data_inf_i.data_addr;
        DECODER_port1_inf_w.data_we = CORE_data_inf_i.data_we;
        DECODER_port1_inf_w.data_be = CORE_data_inf_i.data_be;
        DECODER_port1_inf_w.data_wdata = CORE_data_inf_i.data_wdata;
        
        DECODER_port2_inf_w.data_addr = CORE_data_inf_i.data_addr;
        DECODER_port2_inf_w.data_we = CORE_data_inf_i.data_we;
        DECODER_port2_inf_w.data_be = CORE_data_inf_i.data_be;
        DECODER_port2_inf_w.data_wdata = CORE_data_inf_i.data_wdata;
        
        if (DATA_interface_decoder_sel_w) begin
            CORE_data_inf_i.data_gnt = DECODER_port1_inf_w.data_gnt;
            CORE_data_inf_i.data_rvalid = DECODER_port1_inf_w.data_rvalid;
            CORE_data_inf_i.data_rdata = DECODER_port1_inf_w.data_rdata;
        end else begin
            CORE_data_inf_i.data_gnt = DECODER_port2_inf_w.data_gnt;
            CORE_data_inf_i.data_rvalid = DECODER_port2_inf_w.data_rvalid;
            CORE_data_inf_i.data_rdata = DECODER_port2_inf_w.data_rdata;
        end
        
        if (DATA_interface_decoder_sel_w) begin
            DECODER_port1_inf_w.data_req = CORE_data_inf_i.data_req;
            DECODER_port2_inf_w.data_req = 0;
        end else begin
            DECODER_port1_inf_w.data_req = 0;
            DECODER_port2_inf_w.data_req = CORE_data_inf_i.data_req;
        end
    end
    
    // Interface Arbiter Part
    always_comb begin
        DATA_inf_arbiter_valid_list_w[0] = DECODER_port1_inf_w.data_req;
        DATA_inf_arbiter_valid_list_w[1] = AXI4_ADAP_inf_w.data_req;
        
        DECODER_port1_inf_w.data_rdata = SRAM_data_inf_w.data_rdata;
        AXI4_ADAP_inf_w.data_rdata = SRAM_data_inf_w.data_rdata;
        
        if (DATA_inf_arbiter_sel_w) begin
            SRAM_data_inf_w.data_addr   = AXI4_ADAP_inf_w.data_addr;
            SRAM_data_inf_w.data_req    = AXI4_ADAP_inf_w.data_req;
            SRAM_data_inf_w.data_we     = AXI4_ADAP_inf_w.data_we;
            SRAM_data_inf_w.data_be     = AXI4_ADAP_inf_w.data_be;
            SRAM_data_inf_w.data_wdata  = AXI4_ADAP_inf_w.data_wdata;
        end else begin
            SRAM_data_inf_w.data_addr   = DECODER_port1_inf_w.data_addr;
            SRAM_data_inf_w.data_req    = DECODER_port1_inf_w.data_req;
            SRAM_data_inf_w.data_we     = DECODER_port1_inf_w.data_we;
            SRAM_data_inf_w.data_be     = DECODER_port1_inf_w.data_be;
            SRAM_data_inf_w.data_wdata  = DECODER_port1_inf_w.data_wdata;
        end
        
        if (DATA_inf_arbiter_sel_w) begin
            AXI4_ADAP_inf_w.data_gnt    = SRAM_data_inf_w.data_gnt;
            AXI4_ADAP_inf_w.data_rvalid = SRAM_data_inf_w.data_rvalid;
            
            DECODER_port1_inf_w.data_gnt  = 0;
            DECODER_port1_inf_w.data_rvalid = 0;
        end else begin
            AXI4_ADAP_inf_w.data_gnt = 0;
            AXI4_ADAP_inf_w.data_rvalid = 0;
            
            DECODER_port1_inf_w.data_gnt  = SRAM_data_inf_w.data_gnt;
            DECODER_port1_inf_w.data_rvalid = SRAM_data_inf_w.data_rvalid;
        end
    end
    
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






















