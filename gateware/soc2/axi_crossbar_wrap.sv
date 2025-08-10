`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 18:09:44
// Design Name: 
// Module Name: axi_crossbar_wrap
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


module axi_crossbar_wrap
    #(
        // Number of AXI inputs (slave interfaces)
        parameter S_COUNT = 4,
        // Number of AXI outputs (master interfaces)
        parameter M_COUNT = 4,
        // Width of data bus in bits
        parameter DATA_WIDTH = 32,
        // Width of address bus in bits
        parameter ADDR_WIDTH = 32,
        // Width of wstrb (width of data bus in words)
        parameter STRB_WIDTH = (DATA_WIDTH/8),
        // Input ID field width (from AXI masters)
        parameter S_ID_WIDTH = 8,
        // Output ID field width (towards AXI slaves)
        // Additional bits required for response routing
        parameter M_ID_WIDTH = S_ID_WIDTH+$clog2(S_COUNT),
        // Propagate awuser signal
        parameter AWUSER_ENABLE = 0,
        // Width of awuser signal
        parameter AWUSER_WIDTH = 1,
        // Propagate wuser signal
        parameter WUSER_ENABLE = 0,
        // Width of wuser signal
        parameter WUSER_WIDTH = 1,
        // Propagate buser signal
        parameter BUSER_ENABLE = 0,
        // Width of buser signal
        parameter BUSER_WIDTH = 1,
        // Propagate aruser signal
        parameter ARUSER_ENABLE = 0,
        // Width of aruser signal
        parameter ARUSER_WIDTH = 1,
        // Propagate ruser signal
        parameter RUSER_ENABLE = 0,
        // Width of ruser signal
        parameter RUSER_WIDTH = 1,
        // Number of concurrent unique IDs for each slave interface
        // S_COUNT concatenated fields of 32 bits
        parameter S_THREADS = {S_COUNT{32'd2}},
        // Number of concurrent operations for each slave interface
        // S_COUNT concatenated fields of 32 bits
        parameter S_ACCEPT = {S_COUNT{32'd16}},
        // Number of regions per master interface
        parameter M_REGIONS = 1,
        // Master interface base addresses
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of ADDR_WIDTH bits
        // set to zero for default addressing based on M_ADDR_WIDTH
        parameter M_BASE_ADDR = 0,
        // Master interface address widths
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of 32 bits
        parameter M_ADDR_WIDTH = {M_COUNT{{M_REGIONS{32'd24}}}},
        // Read connections between interfaces
        // M_COUNT concatenated fields of S_COUNT bits
        parameter M_CONNECT_READ = {M_COUNT{{S_COUNT{1'b1}}}},
        // Write connections between interfaces
        // M_COUNT concatenated fields of S_COUNT bits
        parameter M_CONNECT_WRITE = {M_COUNT{{S_COUNT{1'b1}}}},
        // Number of concurrent operations for each master interface
        // M_COUNT concatenated fields of 32 bits
        parameter M_ISSUE = {M_COUNT{32'd4}},
        // Secure master (fail operations based on awprot/arprot)
        // M_COUNT bits
        parameter M_SECURE = {M_COUNT{1'b0}},
        // Slave interface AW channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter S_AW_REG_TYPE = {S_COUNT{2'd0}},
        // Slave interface W channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter S_W_REG_TYPE = {S_COUNT{2'd0}},
        // Slave interface B channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter S_B_REG_TYPE = {S_COUNT{2'd1}},
        // Slave interface AR channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter S_AR_REG_TYPE = {S_COUNT{2'd0}},
        // Slave interface R channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter S_R_REG_TYPE = {S_COUNT{2'd2}},
        // Master interface AW channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter M_AW_REG_TYPE = {M_COUNT{2'd1}},
        // Master interface W channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter M_W_REG_TYPE = {M_COUNT{2'd2}},
        // Master interface B channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter M_B_REG_TYPE = {M_COUNT{2'd0}},
        // Master interface AR channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter M_AR_REG_TYPE = {M_COUNT{2'd1}},
        // Master interface R channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        parameter M_R_REG_TYPE = {M_COUNT{2'd0}}
    )
    (
        input  logic                             clk,
        input  logic                             rst,
        
        /*
         * AXI slave interfaces
         */
        input  logic [S_ID_WIDTH-1:0]           s_axi_awid      [0:S_COUNT-1],
        input  logic [ADDR_WIDTH-1:0]           s_axi_awaddr    [0:S_COUNT-1],
        input  logic [7:0]                      s_axi_awlen     [0:S_COUNT-1],
        input  logic [2:0]                      s_axi_awsize    [0:S_COUNT-1],
        input  logic [1:0]                      s_axi_awburst   [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]              s_axi_awlock,
        input  logic [3:0]                      s_axi_awcache   [0:S_COUNT-1],
        input  logic [2:0]                      s_axi_awprot    [0:S_COUNT-1],
        input  logic [3:0]                      s_axi_awqos     [0:S_COUNT-1],
        input  logic [AWUSER_WIDTH-1:0]         s_axi_awuser    [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]              s_axi_awvalid,
        output logic [S_COUNT-1:0]              s_axi_awready,
        input  logic [DATA_WIDTH-1:0]           s_axi_wdata     [0:S_COUNT-1],
        input  logic [STRB_WIDTH-1:0]           s_axi_wstrb     [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]              s_axi_wlast,
        input  logic [WUSER_WIDTH-1:0]          s_axi_wuser     [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]              s_axi_wvalid,
        output logic [S_COUNT-1:0]              s_axi_wready,
        output logic [S_ID_WIDTH-1:0]           s_axi_bid       [0:S_COUNT-1],
        output logic [1:0]                      s_axi_bresp     [0:S_COUNT-1],
        output logic [BUSER_WIDTH-1:0]          s_axi_buser     [0:S_COUNT-1],
        output logic [S_COUNT-1:0]              s_axi_bvalid,
        input  logic [S_COUNT-1:0]              s_axi_bready,
        input  logic [S_ID_WIDTH-1:0]           s_axi_arid      [0:S_COUNT-1],
        input  logic [ADDR_WIDTH-1:0]           s_axi_araddr    [0:S_COUNT-1],
        input  logic [7:0]                      s_axi_arlen     [0:S_COUNT-1],
        input  logic [2:0]                      s_axi_arsize    [0:S_COUNT-1],
        input  logic [1:0]                      s_axi_arburst   [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]              s_axi_arlock,
        input  logic [3:0]                      s_axi_arcache   [0:S_COUNT-1],
        input  logic [2:0]                      s_axi_arprot    [0:S_COUNT-1],
        input  logic [3:0]                      s_axi_arqos     [0:S_COUNT-1],
        input  logic [ARUSER_WIDTH-1:0]         s_axi_aruser    [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]              s_axi_arvalid,
        output logic [S_COUNT-1:0]              s_axi_arready,
        output logic [S_ID_WIDTH-1:0]           s_axi_rid       [0:S_COUNT-1],
        output logic [DATA_WIDTH-1:0]           s_axi_rdata     [0:S_COUNT-1],
        output logic [1:0]                      s_axi_rresp     [0:S_COUNT-1],
        output logic [S_COUNT-1:0]              s_axi_rlast,
        output logic [RUSER_WIDTH-1:0]          s_axi_ruser     [0:S_COUNT-1],
        output logic [S_COUNT-1:0]              s_axi_rvalid,
        input  logic [S_COUNT-1:0]              s_axi_rready,
    
        /*
         * AXI master interfaces
         */
        output logic [M_ID_WIDTH-1:0]           m_axi_awid      [0:M_COUNT-1],
        output logic [ADDR_WIDTH-1:0]           m_axi_awaddr    [0:M_COUNT-1],
        output logic [7:0]                      m_axi_awlen     [0:M_COUNT-1],
        output logic [2:0]                      m_axi_awsize    [0:M_COUNT-1],
        output logic [1:0]                      m_axi_awburst   [0:M_COUNT-1],
        output logic [M_COUNT-1:0]              m_axi_awlock,
        output logic [3:0]                      m_axi_awcache   [0:M_COUNT-1],
        output logic [2:0]                      m_axi_awprot    [0:M_COUNT-1],
        output logic [3:0]                      m_axi_awqos     [0:M_COUNT-1],
        output logic [3:0]                      m_axi_awregion  [0:M_COUNT-1],
        output logic [AWUSER_WIDTH-1:0]         m_axi_awuser    [0:M_COUNT-1],
        output logic [M_COUNT-1:0]              m_axi_awvalid,
        input  logic [M_COUNT-1:0]              m_axi_awready,
        output logic [DATA_WIDTH-1:0]           m_axi_wdata     [0:M_COUNT-1],
        output logic [STRB_WIDTH-1:0]           m_axi_wstrb     [0:M_COUNT-1],
        output logic [M_COUNT-1:0]              m_axi_wlast,
        output logic [WUSER_WIDTH-1:0]          m_axi_wuser     [0:M_COUNT-1],
        output logic [M_COUNT-1:0]              m_axi_wvalid,
        input  logic [M_COUNT-1:0]              m_axi_wready,
        input  logic [M_ID_WIDTH-1:0]           m_axi_bid       [0:M_COUNT-1],
        input  logic [1:0]                      m_axi_bresp     [0:M_COUNT-1],
        input  logic [BUSER_WIDTH-1:0]          m_axi_buser     [0:M_COUNT-1],
        input  logic [M_COUNT-1:0]              m_axi_bvalid,
        output logic [M_COUNT-1:0]              m_axi_bready,
        output logic [M_ID_WIDTH-1:0]           m_axi_arid      [0:M_COUNT-1],
        output logic [ADDR_WIDTH-1:0]           m_axi_araddr    [0:M_COUNT-1],
        output logic [7:0]                      m_axi_arlen     [0:M_COUNT-1],
        output logic [2:0]                      m_axi_arsize    [0:M_COUNT-1],
        output logic [1:0]                      m_axi_arburst   [0:M_COUNT-1],
        output logic [M_COUNT-1:0]              m_axi_arlock,
        output logic [3:0]                      m_axi_arcache   [0:M_COUNT-1],
        output logic [2:0]                      m_axi_arprot    [0:M_COUNT-1],
        output logic [3:0]                      m_axi_arqos     [0:M_COUNT-1],
        output logic [3:0]                      m_axi_arregion  [0:M_COUNT-1],
        output logic [ARUSER_WIDTH-1:0]         m_axi_aruser    [0:M_COUNT-1],
        output logic [M_COUNT-1:0]              m_axi_arvalid,
        input  logic [M_COUNT-1:0]              m_axi_arready,
        input  logic [M_ID_WIDTH-1:0]           m_axi_rid       [0:M_COUNT-1],
        input  logic [DATA_WIDTH-1:0]           m_axi_rdata     [0:M_COUNT-1],
        input  logic [1:0]                      m_axi_rresp     [0:M_COUNT-1],
        input  logic [M_COUNT-1:0]              m_axi_rlast,
        input  logic [RUSER_WIDTH-1:0]          m_axi_ruser     [0:M_COUNT-1],
        input  logic [M_COUNT-1:0]              m_axi_rvalid,
        output logic [M_COUNT-1:0]              m_axi_rready
    );
    
    logic [S_COUNT*S_ID_WIDTH-1:0]    s_axi_awid_p;
    logic [S_COUNT*ADDR_WIDTH-1:0]    s_axi_awaddr_p;
    logic [S_COUNT*8-1:0]             s_axi_awlen_p;
    logic [S_COUNT*3-1:0]             s_axi_awsize_p;
    logic [S_COUNT*2-1:0]             s_axi_awburst_p;
    logic [S_COUNT-1:0]               s_axi_awlock_p;
    logic [S_COUNT*4-1:0]             s_axi_awcache_p;
    logic [S_COUNT*3-1:0]             s_axi_awprot_p;
    logic [S_COUNT*4-1:0]             s_axi_awqos_p;
    logic [S_COUNT*AWUSER_WIDTH-1:0]  s_axi_awuser_p;
    logic [S_COUNT-1:0]               s_axi_awvalid_p;
    logic [S_COUNT-1:0]               s_axi_awready_p;
    logic [S_COUNT*DATA_WIDTH-1:0]    s_axi_wdata_p;
    logic [S_COUNT*STRB_WIDTH-1:0]    s_axi_wstrb_p;
    logic [S_COUNT-1:0]               s_axi_wlast_p;
    logic [S_COUNT*WUSER_WIDTH-1:0]   s_axi_wuser_p;
    logic [S_COUNT-1:0]               s_axi_wvalid_p;
    logic [S_COUNT-1:0]               s_axi_wready_p;
    logic [S_COUNT*S_ID_WIDTH-1:0]    s_axi_bid_p;
    logic [S_COUNT*2-1:0]             s_axi_bresp_p;
    logic [S_COUNT*BUSER_WIDTH-1:0]   s_axi_buser_p;
    logic [S_COUNT-1:0]               s_axi_bvalid_p;
    logic [S_COUNT-1:0]               s_axi_bready_p;
    logic [S_COUNT*S_ID_WIDTH-1:0]    s_axi_arid_p;
    logic [S_COUNT*ADDR_WIDTH-1:0]    s_axi_araddr_p;
    logic [S_COUNT*8-1:0]             s_axi_arlen_p;
    logic [S_COUNT*3-1:0]             s_axi_arsize_p;
    logic [S_COUNT*2-1:0]             s_axi_arburst_p;
    logic [S_COUNT-1:0]               s_axi_arlock_p;
    logic [S_COUNT*4-1:0]             s_axi_arcache_p;
    logic [S_COUNT*3-1:0]             s_axi_arprot_p;
    logic [S_COUNT*4-1:0]             s_axi_arqos_p;
    logic [S_COUNT*ARUSER_WIDTH-1:0]  s_axi_aruser_p;
    logic [S_COUNT-1:0]               s_axi_arvalid_p;
    logic [S_COUNT-1:0]               s_axi_arready_p;
    logic [S_COUNT*S_ID_WIDTH-1:0]    s_axi_rid_p;
    logic [S_COUNT*DATA_WIDTH-1:0]    s_axi_rdata_p;
    logic [S_COUNT*2-1:0]             s_axi_rresp_p;
    logic [S_COUNT-1:0]               s_axi_rlast_p;
    logic [S_COUNT*RUSER_WIDTH-1:0]   s_axi_ruser_p;
    logic [S_COUNT-1:0]               s_axi_rvalid_p;
    logic [S_COUNT-1:0]               s_axi_rready_p;

    /*
     * AXI master interfaces
     */
    logic [M_COUNT*M_ID_WIDTH-1:0]    m_axi_awid_p;
    logic [M_COUNT*ADDR_WIDTH-1:0]    m_axi_awaddr_p;
    logic [M_COUNT*8-1:0]             m_axi_awlen_p;
    logic [M_COUNT*3-1:0]             m_axi_awsize_p;
    logic [M_COUNT*2-1:0]             m_axi_awburst_p;
    logic [M_COUNT-1:0]               m_axi_awlock_p;
    logic [M_COUNT*4-1:0]             m_axi_awcache_p;
    logic [M_COUNT*3-1:0]             m_axi_awprot_p;
    logic [M_COUNT*4-1:0]             m_axi_awqos_p;
    logic [M_COUNT*4-1:0]             m_axi_awregion_p;
    logic [M_COUNT*AWUSER_WIDTH-1:0]  m_axi_awuser_p;
    logic [M_COUNT-1:0]               m_axi_awvalid_p;
    logic [M_COUNT-1:0]               m_axi_awready_p;
    logic [M_COUNT*DATA_WIDTH-1:0]    m_axi_wdata_p;
    logic [M_COUNT*STRB_WIDTH-1:0]    m_axi_wstrb_p;
    logic [M_COUNT-1:0]               m_axi_wlast_p;
    logic [M_COUNT*WUSER_WIDTH-1:0]   m_axi_wuser_p;
    logic [M_COUNT-1:0]               m_axi_wvalid_p;
    logic [M_COUNT-1:0]               m_axi_wready_p;
    logic [M_COUNT*M_ID_WIDTH-1:0]    m_axi_bid_p;
    logic [M_COUNT*2-1:0]             m_axi_bresp_p;
    logic [M_COUNT*BUSER_WIDTH-1:0]   m_axi_buser_p;
    logic [M_COUNT-1:0]               m_axi_bvalid_p;
    logic [M_COUNT-1:0]               m_axi_bready_p;
    logic [M_COUNT*M_ID_WIDTH-1:0]    m_axi_arid_p;
    logic [M_COUNT*ADDR_WIDTH-1:0]    m_axi_araddr_p;
    logic [M_COUNT*8-1:0]             m_axi_arlen_p;
    logic [M_COUNT*3-1:0]             m_axi_arsize_p;
    logic [M_COUNT*2-1:0]             m_axi_arburst_p;
    logic [M_COUNT-1:0]               m_axi_arlock_p;
    logic [M_COUNT*4-1:0]             m_axi_arcache_p;
    logic [M_COUNT*3-1:0]             m_axi_arprot_p;
    logic [M_COUNT*4-1:0]             m_axi_arqos_p;
    logic [M_COUNT*4-1:0]             m_axi_arregion_p;
    logic [M_COUNT*ARUSER_WIDTH-1:0]  m_axi_aruser_p;
    logic [M_COUNT-1:0]               m_axi_arvalid_p;
    logic [M_COUNT-1:0]               m_axi_arready_p;
    logic [M_COUNT*M_ID_WIDTH-1:0]    m_axi_rid_p;
    logic [M_COUNT*DATA_WIDTH-1:0]    m_axi_rdata_p;
    logic [M_COUNT*2-1:0]             m_axi_rresp_p;
    logic [M_COUNT-1:0]               m_axi_rlast_p;
    logic [M_COUNT*RUSER_WIDTH-1:0]   m_axi_ruser_p;
    logic [M_COUNT-1:0]               m_axi_rvalid_p;
    logic [M_COUNT-1:0]               m_axi_rready_p;
    
    generate
        for (genvar k=0; k<S_COUNT; k++) begin
            assign s_axi_awid_p[k*S_ID_WIDTH+:S_ID_WIDTH] = s_axi_awid[k];
            assign s_axi_awaddr_p[k*ADDR_WIDTH+:ADDR_WIDTH] = s_axi_awaddr[k];
            assign s_axi_awlen_p[k*8+:8] = s_axi_awlen[k];
            assign s_axi_awsize_p[k*3+:3] = s_axi_awsize[k];
            assign s_axi_awburst_p[k*2+:2] = s_axi_awburst[k];
            assign s_axi_awlock_p[k] = s_axi_awlock[k];
            assign s_axi_awcache_p[k*4+:4] = s_axi_awcache[k];
            assign s_axi_awprot_p[k*3+:3] = s_axi_awprot[k];
            assign s_axi_awqos_p[k*4+:4] = s_axi_awqos[k];
            assign s_axi_awuser_p[k*AWUSER_WIDTH+:AWUSER_WIDTH] = s_axi_awuser[k];
            assign s_axi_awvalid_p[k] = s_axi_awvalid[k];
            assign s_axi_awready[k] = s_axi_awready_p[k];
            assign s_axi_wdata_p[k*DATA_WIDTH+:DATA_WIDTH] = s_axi_wdata[k];
            assign s_axi_wstrb_p[k*STRB_WIDTH+:STRB_WIDTH] = s_axi_wstrb[k];
            assign s_axi_wlast_p[k] = s_axi_wlast[k];
            assign s_axi_wuser_p[k*WUSER_WIDTH+:WUSER_WIDTH] = s_axi_wuser[k];
            assign s_axi_wvalid_p[k] = s_axi_wvalid[k];
            assign s_axi_wready[k] = s_axi_wready_p[k];
            assign s_axi_bid[k] = s_axi_bid_p[k*S_ID_WIDTH+:S_ID_WIDTH];
            assign s_axi_bresp[k] = s_axi_bresp_p[k*2+:2];
            assign s_axi_buser[k] = s_axi_buser_p[k*BUSER_WIDTH+:BUSER_WIDTH];
            assign s_axi_bvalid[k] = s_axi_bvalid_p[k];
            assign s_axi_bready_p[k] = s_axi_bready[k];
            assign s_axi_arid_p[k*S_ID_WIDTH+:S_ID_WIDTH] = s_axi_arid[k];
            assign s_axi_araddr_p[k*ADDR_WIDTH+:ADDR_WIDTH] = s_axi_araddr[k];
            assign s_axi_arlen_p[k*8+:8] = s_axi_arlen[k];
            assign s_axi_arsize_p[k*3+:3] = s_axi_arsize[k];
            assign s_axi_arburst_p[k*2+:2] = s_axi_arburst[k];
            assign s_axi_arlock_p[k] = s_axi_arlock[k];
            assign s_axi_arcache_p[k*4+:4] = s_axi_arcache[k];
            assign s_axi_arprot_p[k*3+:3] = s_axi_arprot[k];
            assign s_axi_arqos_p[k*4+:4] = s_axi_arqos[k];
            assign s_axi_aruser_p[k*ARUSER_WIDTH+:ARUSER_WIDTH] = s_axi_aruser[k];
            assign s_axi_arvalid_p[k] = s_axi_arvalid[k];
            assign s_axi_arready[k] = s_axi_arready_p[k];
            assign s_axi_rid[k] = s_axi_rid_p[k*S_ID_WIDTH+:S_ID_WIDTH];
            assign s_axi_rdata[k] = s_axi_rdata_p[k*DATA_WIDTH+:DATA_WIDTH];
            assign s_axi_rresp[k] = s_axi_rresp_p[k*2+:2];
            assign s_axi_rlast[k] = s_axi_rlast_p[k];
            assign s_axi_ruser[k] = s_axi_ruser_p[k*RUSER_WIDTH+:RUSER_WIDTH];
            assign s_axi_rvalid[k] = s_axi_rvalid_p[k];
            assign s_axi_rready_p[k] = s_axi_rready[k];
        end
        
        for (genvar k=0; k<M_COUNT; k++) begin
            assign m_axi_awid[k] = m_axi_awid_p[k*M_ID_WIDTH+:M_ID_WIDTH];
            assign m_axi_awaddr[k] = m_axi_awaddr_p[k*ADDR_WIDTH+:ADDR_WIDTH];
            assign m_axi_awlen[k] = m_axi_awlen_p[k*8+:8];
            assign m_axi_awsize[k] = m_axi_awsize_p[k*3+:3];
            assign m_axi_awburst[k] = m_axi_awburst_p[k*2+:2];
            assign m_axi_awlock[k] = m_axi_awlock_p[k];
            assign m_axi_awcache[k] = m_axi_awcache_p[k*4+:4];
            assign m_axi_awprot[k] = m_axi_awprot_p[k*3+:3];
            assign m_axi_awqos[k] = m_axi_awqos_p[k*4+:4];
            assign m_axi_awregion[k] = m_axi_awregion_p[k*4+:4];
            assign m_axi_awuser[k] = m_axi_awuser_p[k*AWUSER_WIDTH+:AWUSER_WIDTH];
            assign m_axi_awvalid[k] = m_axi_awvalid_p[k];
            assign m_axi_awready_p[k] = m_axi_awready[k];
            
            assign m_axi_wdata[k] = m_axi_wdata_p[k*DATA_WIDTH+:DATA_WIDTH];
            assign m_axi_wstrb[k] = m_axi_wstrb_p[k*STRB_WIDTH+:STRB_WIDTH];
            assign m_axi_wlast[k] = m_axi_wlast_p[k];
            assign m_axi_wuser[k] = m_axi_wuser_p[k*WUSER_WIDTH+:WUSER_WIDTH];
            assign m_axi_wvalid[k] = m_axi_wvalid_p[k];
            
            assign m_axi_wready_p[k] = m_axi_wready[k];
            assign m_axi_bid_p[k*M_ID_WIDTH+:M_ID_WIDTH] = m_axi_bid[k];
            assign m_axi_bresp_p[k*2+:2] = m_axi_bresp[k];
            assign m_axi_buser_p[k*BUSER_WIDTH+:BUSER_WIDTH] = m_axi_buser[k];
            assign m_axi_bvalid_p[k] = m_axi_bvalid[k];
            assign m_axi_bready[k] = m_axi_bready_p[k];
            assign m_axi_arid[k] = m_axi_arid_p[k*M_ID_WIDTH+:M_ID_WIDTH];
            assign m_axi_araddr[k] = m_axi_araddr_p[k*ADDR_WIDTH+:ADDR_WIDTH];
            assign m_axi_arlen[k] = m_axi_arlen_p[k*8+:8];
            assign m_axi_arsize[k] = m_axi_arsize_p[k*3+:3];
            assign m_axi_arburst[k] = m_axi_arburst_p[k*2+:2];
            assign m_axi_arlock[k] = m_axi_arlock_p[k];
            assign m_axi_arcache[k] = m_axi_arcache_p[k*4+:4];
            assign m_axi_arprot[k] = m_axi_arprot_p[k*3+:3];
            assign m_axi_arqos[k] = m_axi_arqos_p[k*4+:4];
            assign m_axi_arregion[k] = m_axi_arregion_p[k*4+:4];
            assign m_axi_aruser[k] = m_axi_aruser_p[k*ARUSER_WIDTH+:ARUSER_WIDTH];
            assign m_axi_arvalid[k] = m_axi_arvalid_p[k];
            assign m_axi_arready_p[k] = m_axi_arready[k];
            assign m_axi_rid_p[k*M_ID_WIDTH+:M_ID_WIDTH] = m_axi_rid[k];
            assign m_axi_rdata_p[k*DATA_WIDTH+:DATA_WIDTH] = m_axi_rdata[k];
            assign m_axi_rresp_p[k*2+:2] = m_axi_rresp[k];
            assign m_axi_rlast_p[k] = m_axi_rlast[k];
            assign m_axi_ruser_p[k*RUSER_WIDTH+:RUSER_WIDTH] = m_axi_ruser[k];
            assign m_axi_rvalid_p[k] = m_axi_rvalid[k];
            assign m_axi_rready[k] = m_axi_rready_p[k];
        end
    endgenerate
    
    axi_crossbar #(
        // Number of AXI inputs (slave interfaces)
        .S_COUNT            ( S_COUNT       ),
        // Number of AXI outputs (master interfaces)
        .M_COUNT            ( M_COUNT       ),
        // Width of data bus in bits
        .DATA_WIDTH         ( DATA_WIDTH    ),
        // Width of address bus in bits
        .ADDR_WIDTH         ( ADDR_WIDTH    ),
        // Width of wstrb (width of data bus in words)
        .STRB_WIDTH         ( STRB_WIDTH    ),
        // Input ID field width (from AXI masters)
        .S_ID_WIDTH         ( S_ID_WIDTH    ),
        // Output ID field width (towards AXI slaves)
        // Additional bits required for response routing
        .M_ID_WIDTH         ( M_ID_WIDTH    ),
        // Propagate awuser signal
        .AWUSER_ENABLE      ( AWUSER_ENABLE ),
        // Width of awuser signal
        .AWUSER_WIDTH       ( AWUSER_WIDTH  ),
        // Propagate wuser signal
        .WUSER_ENABLE       ( WUSER_ENABLE  ),
        // Width of wuser signal
        .WUSER_WIDTH        ( WUSER_WIDTH   ),
        // Propagate buser signal
        .BUSER_ENABLE       ( BUSER_ENABLE  ),
        // Width of buser signal
        .BUSER_WIDTH        ( BUSER_WIDTH   ),
        // Propagate aruser signal
        .ARUSER_ENABLE      ( ARUSER_ENABLE ),
        // Width of aruser signal
        .ARUSER_WIDTH       ( ARUSER_WIDTH  ),
        // Propagate ruser signal
        .RUSER_ENABLE       ( RUSER_ENABLE  ),
        // Width of ruser signal
        .RUSER_WIDTH        ( RUSER_WIDTH   ),
        // Number of concurrent unique IDs for each slave interface
        // S_COUNT concatenated fields of 32 bits
        .S_THREADS          ( S_THREADS     ),
        // Number of concurrent operations for each slave interface
        // S_COUNT concatenated fields of 32 bits
        .S_ACCEPT           ( S_ACCEPT      ),
        // Number of regions per master interface
        .M_REGIONS          ( M_REGIONS     ),
        // Master interface base addresses
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of ADDR_WIDTH bits
        // set to zero for default addressing based on M_ADDR_WIDTH
        .M_BASE_ADDR        ( M_BASE_ADDR   ),
        // Master interface address widths
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of 32 bits
        .M_ADDR_WIDTH       ( M_ADDR_WIDTH  ),
        // Read connections between interfaces
        // M_COUNT concatenated fields of S_COUNT bits
        .M_CONNECT_READ     ( M_CONNECT_READ    ),
        // Write connections between interfaces
        // M_COUNT concatenated fields of S_COUNT bits
        .M_CONNECT_WRITE    ( M_CONNECT_WRITE   ),
        // Number of concurrent operations for each master interface
        // M_COUNT concatenated fields of 32 bits
        .M_ISSUE            ( M_ISSUE           ),
        // Secure master (fail operations based on awprot/arprot)
        // M_COUNT bits
        .M_SECURE           ( M_SECURE          ),
        // Slave interface AW channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .S_AW_REG_TYPE      ( S_AW_REG_TYPE     ),
        // Slave interface W channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .S_W_REG_TYPE       ( S_W_REG_TYPE      ),
        // Slave interface B channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .S_B_REG_TYPE       ( S_B_REG_TYPE      ),
        // Slave interface AR channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .S_AR_REG_TYPE      ( S_AR_REG_TYPE     ),
        // Slave interface R channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .S_R_REG_TYPE       ( S_R_REG_TYPE      ),
        // Master interface AW channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .M_AW_REG_TYPE      ( M_AW_REG_TYPE     ),
        // Master interface W channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .M_W_REG_TYPE       ( M_W_REG_TYPE      ),
        // Master interface B channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .M_B_REG_TYPE       ( M_B_REG_TYPE      ),
        // Master interface AR channel register type (output)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .M_AR_REG_TYPE      ( M_AR_REG_TYPE     ),
        // Master interface R channel register type (input)
        // 0 to bypass, 1 for simple buffer, 2 for skid buffer
        .M_R_REG_TYPE       ( M_R_REG_TYPE      )
    ) AXI_CROSSBAR_VERILOG (
        .clk                ( clk                   ),
        .rst                ( rst                   ),
    
        /*
         * AXI slave interfaces
         */
        .s_axi_awid         ( s_axi_awid_p          ),
        .s_axi_awaddr       ( s_axi_awaddr_p        ),
        .s_axi_awlen        ( s_axi_awlen_p         ),
        .s_axi_awsize       ( s_axi_awsize_p        ),
        .s_axi_awburst      ( s_axi_awburst_p       ),
        .s_axi_awlock       ( s_axi_awlock_p        ),
        .s_axi_awcache      ( s_axi_awcache_p       ),
        .s_axi_awprot       ( s_axi_awprot_p        ),
        .s_axi_awqos        ( s_axi_awqos_p         ),
        .s_axi_awuser       ( s_axi_awuser_p        ),
        .s_axi_awvalid      ( s_axi_awvalid_p       ),
        .s_axi_awready      ( s_axi_awready_p       ),
        .s_axi_wdata        ( s_axi_wdata_p         ),
        .s_axi_wstrb        ( s_axi_wstrb_p         ),
        .s_axi_wlast        ( s_axi_wlast_p         ),
        .s_axi_wuser        ( s_axi_wuser_p         ),
        .s_axi_wvalid       ( s_axi_wvalid_p        ),
        .s_axi_wready       ( s_axi_wready_p        ),
        .s_axi_bid          ( s_axi_bid_p           ),
        .s_axi_bresp        ( s_axi_bresp_p         ),
        .s_axi_buser        ( s_axi_buser_p         ),
        .s_axi_bvalid       ( s_axi_bvalid_p        ),
        .s_axi_bready       ( s_axi_bready_p        ),
        .s_axi_arid         ( s_axi_arid_p          ),
        .s_axi_araddr       ( s_axi_araddr_p        ),
        .s_axi_arlen        ( s_axi_arlen_p         ),
        .s_axi_arsize       ( s_axi_arsize_p        ),
        .s_axi_arburst      ( s_axi_arburst_p       ),
        .s_axi_arlock       ( s_axi_arlock_p        ),
        .s_axi_arcache      ( s_axi_arcache_p       ),
        .s_axi_arprot       ( s_axi_arprot_p        ),
        .s_axi_arqos        ( s_axi_arqos_p         ),
        .s_axi_aruser       ( s_axi_aruser_p        ),
        .s_axi_arvalid      ( s_axi_arvalid_p       ),
        .s_axi_arready      ( s_axi_arready_p       ),
        .s_axi_rid          ( s_axi_rid_p           ),
        .s_axi_rdata        ( s_axi_rdata_p         ),
        .s_axi_rresp        ( s_axi_rresp_p         ),
        .s_axi_rlast        ( s_axi_rlast_p         ),
        .s_axi_ruser        ( s_axi_ruser_p         ),
        .s_axi_rvalid       ( s_axi_rvalid_p        ),
        .s_axi_rready       ( s_axi_rready_p        ),
    
        /*
         * AXI master interfaces
         */
        .m_axi_awid         ( m_axi_awid_p          ),
        .m_axi_awaddr       ( m_axi_awaddr_p        ),
        .m_axi_awlen        ( m_axi_awlen_p         ),
        .m_axi_awsize       ( m_axi_awsize_p        ),
        .m_axi_awburst      ( m_axi_awburst_p       ),
        .m_axi_awlock       ( m_axi_awlock_p        ),
        .m_axi_awcache      ( m_axi_awcache_p       ),
        .m_axi_awprot       ( m_axi_awprot_p        ),
        .m_axi_awqos        ( m_axi_awqos_p         ),
        .m_axi_awregion     ( m_axi_awregion_p      ),
        .m_axi_awuser       ( m_axi_awuser_p        ),
        .m_axi_awvalid      ( m_axi_awvalid_p       ),
        .m_axi_awready      ( m_axi_awready_p       ),
        .m_axi_wdata        ( m_axi_wdata_p         ),
        .m_axi_wstrb        ( m_axi_wstrb_p         ),
        .m_axi_wlast        ( m_axi_wlast_p         ),
        .m_axi_wuser        ( m_axi_wuser_p         ),
        .m_axi_wvalid       ( m_axi_wvalid_p        ),
        .m_axi_wready       ( m_axi_wready_p        ),
        .m_axi_bid          ( m_axi_bid_p           ),
        .m_axi_bresp        ( m_axi_bresp_p         ),
        .m_axi_buser        ( m_axi_buser_p         ),
        .m_axi_bvalid       ( m_axi_bvalid_p        ),
        .m_axi_bready       ( m_axi_bready_p        ),
        .m_axi_arid         ( m_axi_arid_p          ),
        .m_axi_araddr       ( m_axi_araddr_p        ),
        .m_axi_arlen        ( m_axi_arlen_p         ),
        .m_axi_arsize       ( m_axi_arsize_p        ),
        .m_axi_arburst      ( m_axi_arburst_p       ),
        .m_axi_arlock       ( m_axi_arlock_p        ),
        .m_axi_arcache      ( m_axi_arcache_p       ),
        .m_axi_arprot       ( m_axi_arprot_p        ),
        .m_axi_arqos        ( m_axi_arqos_p         ),
        .m_axi_arregion     ( m_axi_arregion_p      ),
        .m_axi_aruser       ( m_axi_aruser_p        ),
        .m_axi_arvalid      ( m_axi_arvalid_p       ),
        .m_axi_arready      ( m_axi_arready_p       ),
        .m_axi_rid          ( m_axi_rid_p           ),
        .m_axi_rdata        ( m_axi_rdata_p         ),
        .m_axi_rresp        ( m_axi_rresp_p         ),
        .m_axi_rlast        ( m_axi_rlast_p         ),
        .m_axi_ruser        ( m_axi_ruser_p         ),
        .m_axi_rvalid       ( m_axi_rvalid_p        ),
        .m_axi_rready       ( m_axi_rready_p        )
    );
    
endmodule














