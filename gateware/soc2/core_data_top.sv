`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07.08.2025 20:22:24
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

`include "sverilog_utils.svh"
`include "soc_configuration.svh"
`include "soc_addr_rules.svh"

module core_data_top
    import soc_addr_rules_pkg::*;
    #(parameter
            DATA_MEMORY_SIZE_IN_KB          = 8,
            CORE_ADDR_WIDTH                 = 32,
            CORE_DATA_WIDTH                 = 32,
            CORE_BE_WIDTH                   = 4,
            ID_WIDTH                        = 8,
            ADDR_WIDTH                      = 32,
            USER_WIDTH                      = 8,
            M_DATA_WIDTH                    = 32,
            M_STRB_WIDTH                    = 4,
            S_DATA_WIDTH                    = 32,
            S_STRB_WIDTH                    = 4
    )
    (
        input   logic                       clk_i, reset_ni,
        
        input   logic [CORE_ADDR_WIDTH-1:0] core_data_addr_i,
        input   logic                       core_data_req_i,
        input   logic                       core_data_we_i,
        input   logic [CORE_BE_WIDTH-1:0]   core_data_be_i,
        input   logic [CORE_DATA_WIDTH-1:0] core_data_wdata_i,
        output  logic                       core_data_gnt_o,
        output  logic                       core_data_rvalid_o,
        output  logic [CORE_DATA_WIDTH-1:0] core_data_rdata_o,
        
        /*
         * AXI master interface
         */
        output  logic [ID_WIDTH-1:0]        m_axi_awid,
        output  logic [ADDR_WIDTH-1:0]      m_axi_awaddr,
        output  logic [7:0]                 m_axi_awlen,
        output  logic [2:0]                 m_axi_awsize,
        output  logic [1:0]                 m_axi_awburst,
        output  logic                       m_axi_awlock,
        output  logic [3:0]                 m_axi_awcache,
        output  logic [2:0]                 m_axi_awprot,
        output  logic [3:0]                 m_axi_awqos,
        output  logic [3:0]                 m_axi_awregion,
        output  logic [USER_WIDTH-1:0]      m_axi_awuser,
        output  logic                       m_axi_awvalid,
        input   logic                       m_axi_awready,
        output  logic [M_DATA_WIDTH-1:0]    m_axi_wdata,
        output  logic [M_STRB_WIDTH-1:0]    m_axi_wstrb,
        output  logic                       m_axi_wlast,
        output  logic [USER_WIDTH-1:0]      m_axi_wuser,
        output  logic                       m_axi_wvalid,
        input   logic                       m_axi_wready,
        input   logic [ID_WIDTH-1:0]        m_axi_bid,
        input   logic [1:0]                 m_axi_bresp,
        input   logic [USER_WIDTH-1:0]      m_axi_buser,
        input   logic                       m_axi_bvalid,
        output  logic                       m_axi_bready,
        output  logic [ID_WIDTH-1:0]        m_axi_arid,
        output  logic [ADDR_WIDTH-1:0]      m_axi_araddr,
        output  logic [7:0]                 m_axi_arlen,
        output  logic [2:0]                 m_axi_arsize,
        output  logic [1:0]                 m_axi_arburst,
        output  logic                       m_axi_arlock,
        output  logic [3:0]                 m_axi_arcache,
        output  logic [2:0]                 m_axi_arprot,
        output  logic [3:0]                 m_axi_arqos,
        output  logic [3:0]                 m_axi_arregion,
        output  logic [USER_WIDTH-1:0]      m_axi_aruser,
        output  logic                       m_axi_arvalid,
        input   logic                       m_axi_arready,
        input   logic [ID_WIDTH-1:0]        m_axi_rid,
        input   logic [M_DATA_WIDTH-1:0]    m_axi_rdata,
        input   logic [1:0]                 m_axi_rresp,
        input   logic                       m_axi_rlast,
        input   logic [USER_WIDTH-1:0]      m_axi_ruser,
        input   logic                       m_axi_rvalid,
        output  logic                       m_axi_rready,
        
        /*
        * AXI slave interface
        */
        input   logic [ID_WIDTH-1:0]        s_axi_awid,
        input   logic [ADDR_WIDTH-1:0]      s_axi_awaddr,
        input   logic [7:0]                 s_axi_awlen,
        input   logic [2:0]                 s_axi_awsize,
        input   logic [1:0]                 s_axi_awburst,
        input   logic                       s_axi_awlock,
        input   logic [3:0]                 s_axi_awcache,
        input   logic [2:0]                 s_axi_awprot,
        input   logic [3:0]                 s_axi_awqos,
        input   logic [3:0]                 s_axi_awregion,
        input   logic [USER_WIDTH-1:0]      s_axi_awuser,
        input   logic                       s_axi_awvalid,
        output  logic                       s_axi_awready,
        input   logic [S_DATA_WIDTH-1:0]    s_axi_wdata,
        input   logic [S_STRB_WIDTH-1:0]    s_axi_wstrb,
        input   logic                       s_axi_wlast,
        input   logic [USER_WIDTH-1:0]      s_axi_wuser,
        input   logic                       s_axi_wvalid,
        output  logic                       s_axi_wready,
        output  logic [ID_WIDTH-1:0]        s_axi_bid,
        output  logic [1:0]                 s_axi_bresp,
        output  logic [USER_WIDTH-1:0]      s_axi_buser,
        output  logic                       s_axi_bvalid,
        input   logic                       s_axi_bready,
        input   logic [ID_WIDTH-1:0]        s_axi_arid,
        input   logic [ADDR_WIDTH-1:0]      s_axi_araddr,
        input   logic [7:0]                 s_axi_arlen,
        input   logic [2:0]                 s_axi_arsize,
        input   logic [1:0]                 s_axi_arburst,
        input   logic                       s_axi_arlock,
        input   logic [3:0]                 s_axi_arcache,
        input   logic [2:0]                 s_axi_arprot,
        input   logic [3:0]                 s_axi_arqos,
        input   logic [3:0]                 s_axi_arregion,
        input   logic [USER_WIDTH-1:0]      s_axi_aruser,
        input   logic                       s_axi_arvalid,
        output  logic                       s_axi_arready,
        output  logic [ID_WIDTH-1:0]        s_axi_rid,
        output  logic [S_DATA_WIDTH-1:0]    s_axi_rdata,
        output  logic [1:0]                 s_axi_rresp,
        output  logic                       s_axi_rlast,
        output  logic [USER_WIDTH-1:0]      s_axi_ruser,
        output  logic                       s_axi_rvalid,
        input   logic                       s_axi_rready
    );
    
    logic req_valid_w, req_done_w;
    logic decoder_sel_w, decoder_illegal_w, arbiter_sel_w;
    logic [1:0] arbiter_ready_list_w;
    
    logic [CORE_ADDR_WIDTH-1:0] core_data_addr_r,   core_data_addr_w;
    logic                       core_data_req_r,    core_data_req_w;
    logic                       core_data_we_r,     core_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   core_data_be_r,     core_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] core_data_wdata_r,  core_data_wdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] decoder1_data_addr_w;
    logic                       decoder1_data_req_w;
    logic                       decoder1_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   decoder1_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] decoder1_data_wdata_w;
    logic                       decoder1_data_gnt_w;
    logic                       decoder1_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] decoder1_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] decoder2_data_addr_w;
    logic                       decoder2_data_req_w;
    logic                       decoder2_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   decoder2_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] decoder2_data_wdata_w;
    logic                       decoder2_data_gnt_w;
    logic                       decoder2_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] decoder2_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] axi_slave_data_addr_w;
    logic                       axi_slave_data_req_w;
    logic                       axi_slave_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   axi_slave_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] axi_slave_data_wdata_w;
    logic                       axi_slave_data_gnt_w;
    logic                       axi_slave_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] axi_slave_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] sram_data_addr_w;
    logic                       sram_data_req_w;
    logic                       sram_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   sram_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] sram_data_wdata_w;
    logic                       sram_data_gnt_w;
    logic                       sram_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] sram_data_rdata_w;
    
    
    typedef logic decoder_id_t;
    
    typedef struct packed {
        decoder_id_t    id;
        addr_t          start_addr;
        addr_t          end_addr;
    } intf_decoder_addr_rule_t;
    
    intf_decoder_addr_rule_t decoder_addr_rule_w [0:1];
    assign decoder_addr_rule_w[0].id            = 0;
    assign decoder_addr_rule_w[0].start_addr    = soc_addr_rules_pkg::DATA_SRAM_ADDR_RULE.start_addr;
    assign decoder_addr_rule_w[0].end_addr      = soc_addr_rules_pkg::DATA_SRAM_ADDR_RULE.end_addr;
    assign decoder_addr_rule_w[1].id            = 1;
    assign decoder_addr_rule_w[1].start_addr    = soc_addr_rules_pkg::AXI_MASTER_ADDR_RULE.start_addr;
    assign decoder_addr_rule_w[1].end_addr      = soc_addr_rules_pkg::AXI_MASTER_ADDR_RULE.end_addr;
    
    assign decoder1_data_addr_w     = core_data_addr_w    ;
    assign decoder1_data_req_w      = (decoder_sel_w) ? 0 : core_data_req_w;
    assign decoder1_data_we_w       = core_data_we_w      ;
    assign decoder1_data_be_w       = core_data_be_w      ;
    assign decoder1_data_wdata_w    = core_data_wdata_w   ;
    
    assign decoder2_data_addr_w     = core_data_addr_w    ;
    assign decoder2_data_req_w      = (decoder_sel_w) ? core_data_req_w : 0;
    assign decoder2_data_we_w       = core_data_we_w      ;
    assign decoder2_data_be_w       = core_data_be_w      ;
    assign decoder2_data_wdata_w    = core_data_wdata_w   ;
    
    assign core_data_gnt_o          = req_valid_w;
    assign core_data_rvalid_o       = (old_dec_sel_r) ? decoder2_data_rvalid_w  : decoder1_data_rvalid_w;
    assign core_data_rdata_o        = (old_dec_sel_r) ? decoder2_data_rdata_w   : decoder1_data_rdata_w ;
    
    assign arbiter_ready_list_w[0]  = decoder1_data_req_w;
    assign arbiter_ready_list_w[1]  = axi_slave_data_req_w;
    
    assign sram_data_addr_w         = (arbiter_sel_w) ? axi_slave_data_addr_w   : decoder1_data_addr_w    ;
    assign sram_data_req_w          = (arbiter_sel_w) ? axi_slave_data_req_w    : decoder1_data_req_w     ;
    assign sram_data_we_w           = (arbiter_sel_w) ? axi_slave_data_we_w     : decoder1_data_we_w      ;
    assign sram_data_be_w           = (arbiter_sel_w) ? axi_slave_data_be_w     : decoder1_data_be_w      ;
    assign sram_data_wdata_w        = (arbiter_sel_w) ? axi_slave_data_wdata_w  : decoder1_data_wdata_w   ;
    
    assign axi_slave_data_gnt_w     = (arbiter_sel_w) ? sram_data_gnt_w         : 0 ;
    assign axi_slave_data_rvalid_w  = (old_dec_sel_r) ? sram_data_rvalid_w      : 0 ;
    assign axi_slave_data_rdata_w   = sram_data_rdata_w;
    
    assign decoder1_data_gnt_w      = (arbiter_sel_w) ? 0 : sram_data_gnt_w    ;
    assign decoder1_data_rvalid_w   = (old_dec_sel_r) ? 0 : sram_data_rvalid_w ;
    assign decoder1_data_rdata_w    = sram_data_rdata_w;
    
    assign core_data_req_w          = (req_valid_w) ? (core_data_req_i)  : core_data_req_r  ;
    assign core_data_addr_w         = (req_valid_w) ? core_data_addr_i  : core_data_addr_r ;
    assign core_data_we_w           = (req_valid_w) ? core_data_we_i    : core_data_we_r   ;
    assign core_data_be_w           = (req_valid_w) ? core_data_be_i    : core_data_be_r   ;
    assign core_data_wdata_w        = (req_valid_w) ? core_data_wdata_i : core_data_wdata_r;
    
    logic old_dec_sel_r;
    
    assign req_done_w               = (old_dec_sel_r) ? decoder2_data_rvalid_w : decoder1_data_rvalid_w;
    assign req_valid_w              = ~core_data_req_r | req_done_w;
    
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            core_data_req_r     <= 0;
            core_data_addr_r    <= 0;
            core_data_we_r      <= 0;
            core_data_be_r      <= 0;
            core_data_wdata_r   <= 0;
            old_dec_sel_r       <= 0;
        end else begin
            if (req_valid_w) begin
                core_data_req_r     <= core_data_req_i;
                core_data_addr_r    <= core_data_addr_i;
                core_data_we_r      <= core_data_we_i;
                core_data_be_r      <= core_data_be_i;
                core_data_wdata_r   <= core_data_wdata_i;
                old_dec_sel_r       <= decoder_sel_w;
            end else if (core_data_req_r) begin
                if (req_done_w) begin
                    core_data_req_r <= 0;
                end
            end
        end
    end
    
    addr_decode #(
        .ID_TYPE                ( decoder_id_t              ),
        .ADDR_TYPE              ( soc_addr_rules_pkg::addr_t),
        .RULE_TYPE              ( intf_decoder_addr_rule_t  ),
        
        .PORT_COUNT             ( 2                         )
    ) INTERFACE_DECODER (
        .addr_rule_map_i        ( decoder_addr_rule_w       ),
        .addr_i                 ( core_data_addr_w          ),
        .illegal_o              ( decoder_illegal_w         ),
        .selected_id_o          ( decoder_sel_w             )
    );
    
    roundrobin_arbiter #(
        .PORT_COUNT             ( 2                         ),
        .PRIORTY_AT_0           ( 1                         ),
        
        .PORT_ID_WIDTH          ( 1                         )
    ) INTERFACE_ARBITER (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .port_ready_list_i      ( arbiter_ready_list_w      ),
        .port_selected_id_o     ( arbiter_sel_w             )
    ); 
    
    mem2axi #(
        .CORE_ADDR_WIDTH        ( CORE_ADDR_WIDTH           ),
        .CORE_DATA_WIDTH        ( CORE_DATA_WIDTH           ),
        .CORE_BE_WIDTH          ( CORE_BE_WIDTH             ),
        .ID_WIDTH               ( ID_WIDTH                  ),
        .ADDR_WIDTH             ( ADDR_WIDTH                ),
        .USER_WIDTH             ( USER_WIDTH                ),
        .M_DATA_WIDTH           ( M_DATA_WIDTH              ),
        .M_STRB_WIDTH           ( M_STRB_WIDTH              )
    ) MEM2AXI (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .core_data_addr_i       ( decoder2_data_addr_w      ),
        .core_data_req_i        ( decoder2_data_req_w       ),
        .core_data_we_i         ( decoder2_data_we_w        ),
        .core_data_be_i         ( decoder2_data_be_w        ),
        .core_data_wdata_i      ( decoder2_data_wdata_w     ),
        .core_data_gnt_o        ( decoder2_data_gnt_w       ),
        .core_data_rvalid_o     ( decoder2_data_rvalid_w    ),
        .core_data_rdata_o      ( decoder2_data_rdata_w     ),
        
        .m_axi_awid             ( m_axi_awid                ),
        .m_axi_awaddr           ( m_axi_awaddr              ),
        .m_axi_awlen            ( m_axi_awlen               ),
        .m_axi_awsize           ( m_axi_awsize              ),
        .m_axi_awburst          ( m_axi_awburst             ),
        .m_axi_awlock           ( m_axi_awlock              ),
        .m_axi_awcache          ( m_axi_awcache             ),
        .m_axi_awprot           ( m_axi_awprot              ),
        .m_axi_awqos            ( m_axi_awqos               ),
        .m_axi_awregion         ( m_axi_awregion            ),
        .m_axi_awuser           ( m_axi_awuser              ),
        .m_axi_awvalid          ( m_axi_awvalid             ),
        .m_axi_awready          ( m_axi_awready             ),
        .m_axi_wdata            ( m_axi_wdata               ),
        .m_axi_wstrb            ( m_axi_wstrb               ),
        .m_axi_wlast            ( m_axi_wlast               ),
        .m_axi_wuser            ( m_axi_wuser               ),
        .m_axi_wvalid           ( m_axi_wvalid              ),
        .m_axi_wready           ( m_axi_wready              ),
        .m_axi_bid              ( m_axi_bid                 ),
        .m_axi_bresp            ( m_axi_bresp               ),
        .m_axi_buser            ( m_axi_buser               ),
        .m_axi_bvalid           ( m_axi_bvalid              ),
        .m_axi_bready           ( m_axi_bready              ),
        .m_axi_arid             ( m_axi_arid                ),
        .m_axi_araddr           ( m_axi_araddr              ),
        .m_axi_arlen            ( m_axi_arlen               ),
        .m_axi_arsize           ( m_axi_arsize              ),
        .m_axi_arburst          ( m_axi_arburst             ),
        .m_axi_arlock           ( m_axi_arlock              ),
        .m_axi_arcache          ( m_axi_arcache             ),
        .m_axi_arprot           ( m_axi_arprot              ),
        .m_axi_arqos            ( m_axi_arqos               ),
        .m_axi_arregion         ( m_axi_arregion            ),
        .m_axi_aruser           ( m_axi_aruser              ),
        .m_axi_arvalid          ( m_axi_arvalid             ),
        .m_axi_arready          ( m_axi_arready             ),
        .m_axi_rid              ( m_axi_rid                 ),
        .m_axi_rdata            ( m_axi_rdata               ),
        .m_axi_rresp            ( m_axi_rresp               ),
        .m_axi_rlast            ( m_axi_rlast               ),
        .m_axi_ruser            ( m_axi_ruser               ),
        .m_axi_rvalid           ( m_axi_rvalid              ),
        .m_axi_rready           ( m_axi_rready              )
    );
    
    axi2mem #(
        .CORE_ADDR_WIDTH        ( CORE_ADDR_WIDTH           ),
        .CORE_DATA_WIDTH        ( CORE_DATA_WIDTH           ),
        .CORE_BE_WIDTH          ( CORE_BE_WIDTH             ),
        .ID_WIDTH               ( ID_WIDTH                  ),
        .ADDR_WIDTH             ( ADDR_WIDTH                ),
        .USER_WIDTH             ( USER_WIDTH                ),
        .S_DATA_WIDTH           ( S_DATA_WIDTH              ),
        .S_STRB_WIDTH           ( S_STRB_WIDTH              )
    ) AXI2MEM (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .core_data_addr_o       ( axi_slave_data_addr_w     ),
        .core_data_req_o        ( axi_slave_data_req_w      ),
        .core_data_we_o         ( axi_slave_data_we_w       ),
        .core_data_be_o         ( axi_slave_data_be_w       ),
        .core_data_wdata_o      ( axi_slave_data_wdata_w    ),
        .core_data_gnt_i        ( axi_slave_data_gnt_w      ),
        .core_data_rvalid_i     ( axi_slave_data_rvalid_w   ),
        .core_data_rdata_i      ( axi_slave_data_rdata_w    ),
        
        /*
        * AXI slave interface
        */
        .s_axi_awid             ( s_axi_awid                ),
        .s_axi_awaddr           ( s_axi_awaddr              ),
        .s_axi_awlen            ( s_axi_awlen               ),
        .s_axi_awsize           ( s_axi_awsize              ),
        .s_axi_awburst          ( s_axi_awburst             ),
        .s_axi_awlock           ( s_axi_awlock              ),
        .s_axi_awcache          ( s_axi_awcache             ),
        .s_axi_awprot           ( s_axi_awprot              ),
        .s_axi_awqos            ( s_axi_awqos               ),
        .s_axi_awregion         ( s_axi_awregion            ),
        .s_axi_awuser           ( s_axi_awuser              ),
        .s_axi_awvalid          ( s_axi_awvalid             ),
        .s_axi_awready          ( s_axi_awready             ),
        .s_axi_wdata            ( s_axi_wdata               ),
        .s_axi_wstrb            ( s_axi_wstrb               ),
        .s_axi_wlast            ( s_axi_wlast               ),
        .s_axi_wuser            ( s_axi_wuser               ),
        .s_axi_wvalid           ( s_axi_wvalid              ),
        .s_axi_wready           ( s_axi_wready              ),
        .s_axi_bid              ( s_axi_bid                 ),
        .s_axi_bresp            ( s_axi_bresp               ),
        .s_axi_buser            ( s_axi_buser               ),
        .s_axi_bvalid           ( s_axi_bvalid              ),
        .s_axi_bready           ( s_axi_bready              ),
        .s_axi_arid             ( s_axi_arid                ),
        .s_axi_araddr           ( s_axi_araddr              ),
        .s_axi_arlen            ( s_axi_arlen               ),
        .s_axi_arsize           ( s_axi_arsize              ),
        .s_axi_arburst          ( s_axi_arburst             ),
        .s_axi_arlock           ( s_axi_arlock              ),
        .s_axi_arcache          ( s_axi_arcache             ),
        .s_axi_arprot           ( s_axi_arprot              ),
        .s_axi_arqos            ( s_axi_arqos               ),
        .s_axi_arregion         ( s_axi_arregion            ),
        .s_axi_aruser           ( s_axi_aruser              ),
        .s_axi_arvalid          ( s_axi_arvalid             ),
        .s_axi_arready          ( s_axi_arready             ),
        .s_axi_rid              ( s_axi_rid                 ),
        .s_axi_rdata            ( s_axi_rdata               ),
        .s_axi_rresp            ( s_axi_rresp               ),
        .s_axi_rlast            ( s_axi_rlast               ),
        .s_axi_ruser            ( s_axi_ruser               ),
        .s_axi_rvalid           ( s_axi_rvalid              ),
        .s_axi_rready           ( s_axi_rready              )
    );
    
    data_memory #(
        .SIZE_IN_KB             ( DATA_MEMORY_SIZE_IN_KB    ),
        .ADDR_WIDTH             ( CORE_ADDR_WIDTH           ),
        .DATA_WIDTH             ( CORE_DATA_WIDTH           ),
        .BE_WIDTH               ( CORE_BE_WIDTH             )
    ) DATA_MEMORY (
        .clk_i(clk_i), .reset_ni(reset_ni),

        .data_addr_i            ( sram_data_addr_w          ),
        .data_req_i             ( sram_data_req_w           ),
        .data_we_i              ( sram_data_we_w            ),
        .data_be_i              ( sram_data_be_w            ),
        .data_wdata_i           ( sram_data_wdata_w         ),
        .data_gnt_o             ( sram_data_gnt_w           ),
        .data_rvalid_o          ( sram_data_rvalid_w        ),
        .data_rdata_o           ( sram_data_rdata_w         )
    );
    
`ifdef ASSERTIONS
    /////////////////////////////////////////
    // ASSERTIONS
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
        end else begin
            if (core_data_req_w) begin
                `ASSERT((~decoder_illegal_w), 
                    $sformatf("core_data_top.sv: illegal decoded addr, addr data: %h", core_data_addr_w))
            end
        end
    end
    /////////////////////////////////////////
`endif // ASSERTIONS

endmodule


















