`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10.08.2025 10:45:23
// Design Name: 
// Module Name: axil_interconnect_wrap
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


module axil_interconnect_wrap
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
        // Secure master (fail operations based on awprot/arprot)
        // M_COUNT bits
        parameter M_SECURE = {M_COUNT{1'b0}}
    )
    (
        input   logic                       clk_i, reset_ni,
        
        /*
         * AXI lite slave interfaces
         */
        input  logic [ADDR_WIDTH-1:0]       s_axil_awaddr   [0:S_COUNT-1],
        input  logic [2:0]                  s_axil_awprot   [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]          s_axil_awvalid,
        output logic [S_COUNT-1:0]          s_axil_awready,
        input  logic [DATA_WIDTH-1:0]       s_axil_wdata    [0:S_COUNT-1],
        input  logic [STRB_WIDTH-1:0]       s_axil_wstrb    [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]          s_axil_wvalid,
        output logic [S_COUNT-1:0]          s_axil_wready,
        output logic [1:0]                  s_axil_bresp    [0:S_COUNT-1],
        output logic [S_COUNT-1:0]          s_axil_bvalid,
        input  logic [S_COUNT-1:0]          s_axil_bready,
        input  logic [ADDR_WIDTH-1:0]       s_axil_araddr   [0:S_COUNT-1],
        input  logic [2:0]                  s_axil_arprot   [0:S_COUNT-1],
        input  logic [S_COUNT-1:0]          s_axil_arvalid,
        output logic [S_COUNT-1:0]          s_axil_arready,
        output logic [DATA_WIDTH-1:0]       s_axil_rdata    [0:S_COUNT-1],
        output logic [1:0]                  s_axil_rresp    [0:S_COUNT-1],
        output logic [S_COUNT-1:0]          s_axil_rvalid,
        input  logic [S_COUNT-1:0]          s_axil_rready,
    
        /*
         * AXI lite master interfaces
         */
        output logic [ADDR_WIDTH-1:0]       m_axil_awaddr   [0:M_COUNT-1],
        output logic [2:0]                  m_axil_awprot   [0:M_COUNT-1],
        output logic [M_COUNT-1:0]          m_axil_awvalid,
        input  logic [M_COUNT-1:0]          m_axil_awready,
        output logic [DATA_WIDTH-1:0]       m_axil_wdata    [0:M_COUNT-1],
        output logic [STRB_WIDTH-1:0]       m_axil_wstrb    [0:M_COUNT-1],
        output logic [M_COUNT-1:0]          m_axil_wvalid,
        input  logic [M_COUNT-1:0]          m_axil_wready,
        input  logic [1:0]                  m_axil_bresp    [0:M_COUNT-1],
        input  logic [M_COUNT-1:0]          m_axil_bvalid,
        output logic [M_COUNT-1:0]          m_axil_bready,
        output logic [ADDR_WIDTH-1:0]       m_axil_araddr   [0:M_COUNT-1],
        output logic [2:0]                  m_axil_arprot   [0:M_COUNT-1],
        output logic [M_COUNT-1:0]          m_axil_arvalid,
        input  logic [M_COUNT-1:0]          m_axil_arready,
        input  logic [DATA_WIDTH-1:0]       m_axil_rdata    [0:M_COUNT-1],
        input  logic [1:0]                  m_axil_rresp    [0:M_COUNT-1],
        input  logic [M_COUNT-1:0]          m_axil_rvalid,
        output logic [M_COUNT-1:0]          m_axil_rready
    );
    
    /*
     * AXI lite slave interfaces
     */
    logic [S_COUNT*ADDR_WIDTH-1:0]  s_axil_awaddr_p;
    logic [S_COUNT*3-1:0]           s_axil_awprot_p;
    logic [S_COUNT-1:0]             s_axil_awvalid_p;
    logic [S_COUNT-1:0]             s_axil_awready_p;
    logic [S_COUNT*DATA_WIDTH-1:0]  s_axil_wdata_p;
    logic [S_COUNT*STRB_WIDTH-1:0]  s_axil_wstrb_p;
    logic [S_COUNT-1:0]             s_axil_wvalid_p;
    logic [S_COUNT-1:0]             s_axil_wready_p;
    logic [S_COUNT*2-1:0]           s_axil_bresp_p;
    logic [S_COUNT-1:0]             s_axil_bvalid_p;
    logic [S_COUNT-1:0]             s_axil_bready_p;
    logic [S_COUNT*ADDR_WIDTH-1:0]  s_axil_araddr_p;
    logic [S_COUNT*3-1:0]           s_axil_arprot_p;
    logic [S_COUNT-1:0]             s_axil_arvalid_p;
    logic [S_COUNT-1:0]             s_axil_arready_p;
    logic [S_COUNT*DATA_WIDTH-1:0]  s_axil_rdata_p;
    logic [S_COUNT*2-1:0]           s_axil_rresp_p;
    logic [S_COUNT-1:0]             s_axil_rvalid_p;
    logic [S_COUNT-1:0]             s_axil_rready_p;

    /*
     * AXI lite master interfaces
     */
    logic [M_COUNT*ADDR_WIDTH-1:0]  m_axil_awaddr_p;
    logic [M_COUNT*3-1:0]           m_axil_awprot_p;
    logic [M_COUNT-1:0]             m_axil_awvalid_p;
    logic [M_COUNT-1:0]             m_axil_awready_p;
    logic [M_COUNT*DATA_WIDTH-1:0]  m_axil_wdata_p;
    logic [M_COUNT*STRB_WIDTH-1:0]  m_axil_wstrb_p;
    logic [M_COUNT-1:0]             m_axil_wvalid_p;
    logic [M_COUNT-1:0]             m_axil_wready_p;
    logic [M_COUNT*2-1:0]           m_axil_bresp_p;
    logic [M_COUNT-1:0]             m_axil_bvalid_p;
    logic [M_COUNT-1:0]             m_axil_bready_p;
    logic [M_COUNT*ADDR_WIDTH-1:0]  m_axil_araddr_p;
    logic [M_COUNT*3-1:0]           m_axil_arprot_p;
    logic [M_COUNT-1:0]             m_axil_arvalid_p;
    logic [M_COUNT-1:0]             m_axil_arready_p;
    logic [M_COUNT*DATA_WIDTH-1:0]  m_axil_rdata_p;
    logic [M_COUNT*2-1:0]           m_axil_rresp_p;
    logic [M_COUNT-1:0]             m_axil_rvalid_p;
    logic [M_COUNT-1:0]             m_axil_rready_p;
    
    generate
        for (genvar k=0; k<S_COUNT; k++) begin
            assign s_axil_awready [k]   = s_axil_awready_p [k];
            assign s_axil_wready  [k]   = s_axil_wready_p  [k];
            assign s_axil_bresp   [k]   = s_axil_bresp_p   [k*2+:2];
            assign s_axil_bvalid  [k]   = s_axil_bvalid_p  [k];
            assign s_axil_arready [k]   = s_axil_arready_p [k];
            assign s_axil_rdata   [k]   = s_axil_rdata_p   [k*DATA_WIDTH+:DATA_WIDTH];
            assign s_axil_rresp   [k]   = s_axil_rresp_p   [k*2+:2];
            assign s_axil_rvalid  [k]   = s_axil_rvalid_p  [k];
            
            assign s_axil_awaddr_p[k*ADDR_WIDTH+:ADDR_WIDTH]    = s_axil_awaddr[k]  ;
            assign s_axil_awprot_p[k*3+:3]                      = s_axil_awprot[k]  ;
            assign s_axil_awvalid_p[k]                          = s_axil_awvalid[k] ;
            assign s_axil_wdata_p[k*DATA_WIDTH+:DATA_WIDTH]     = s_axil_wdata[k]   ;
            assign s_axil_wstrb_p[k*STRB_WIDTH+:STRB_WIDTH]     = s_axil_wstrb[k]   ;
            assign s_axil_wvalid_p[k]                           = s_axil_wvalid[k]  ;
            assign s_axil_bready_p[k]                           = s_axil_bready[k]  ;
            assign s_axil_araddr_p[k*ADDR_WIDTH+:ADDR_WIDTH]    = s_axil_araddr[k]  ;
            assign s_axil_arprot_p[k*3+:3]                      = s_axil_arprot[k]  ;
            assign s_axil_arvalid_p[k]                          = s_axil_arvalid[k] ;
            assign s_axil_rready_p[k]                           = s_axil_rready[k]  ;
        end
        
        for (genvar k=0; k<M_COUNT; k++) begin
            assign m_axil_awaddr[k]     = m_axil_awaddr_p[k*ADDR_WIDTH+:ADDR_WIDTH]; 
            assign m_axil_awprot[k]     = m_axil_awprot_p[k*3+:3]; 
            assign m_axil_awvalid[k]    = m_axil_awvalid_p[k];
            assign m_axil_wdata[k]      = m_axil_wdata_p[k*DATA_WIDTH+:DATA_WIDTH];  
            assign m_axil_wstrb[k]      = m_axil_wstrb_p[k*STRB_WIDTH+:STRB_WIDTH];  
            assign m_axil_wvalid[k]     = m_axil_wvalid_p[k]; 
            assign m_axil_bready[k]     = m_axil_bready_p[k]; 
            assign m_axil_araddr[k]     = m_axil_araddr_p[k*ADDR_WIDTH+:ADDR_WIDTH]; 
            assign m_axil_arprot[k]     = m_axil_arprot_p[k*3+:3]; 
            assign m_axil_arvalid[k]    = m_axil_arvalid_p[k];
            assign m_axil_rready[k]     = m_axil_rready_p[k];
            
            assign m_axil_awready_p[k]                          = m_axil_awready[k] ;
            assign m_axil_wready_p[k]                           = m_axil_wready[k]  ;
            assign m_axil_bresp_p[k*2+:2]                       = m_axil_bresp[k]   ;
            assign m_axil_bvalid_p[k]                           = m_axil_bvalid[k]  ;
            assign m_axil_arready_p[k]                          = m_axil_arready[k] ;
            assign m_axil_rdata_p[k*DATA_WIDTH+:DATA_WIDTH]     = m_axil_rdata[k]   ;
            assign m_axil_rresp_p[k*2+:2]                       = m_axil_rresp[k]   ;
            assign m_axil_rvalid_p[k]                           = m_axil_rvalid[k]  ;
        end
    endgenerate
    
    axil_interconnect #(
        // Number of AXI inputs (slave interfaces)
        .S_COUNT                ( S_COUNT           ),
        // Number of AXI outputs (master interfaces)
        .M_COUNT                ( M_COUNT           ),
        // Width of data bus in bits
        .DATA_WIDTH             ( DATA_WIDTH        ),
        // Width of address bus in bits
        .ADDR_WIDTH             ( ADDR_WIDTH        ),
        // Width of wstrb (width of data bus in words)
        .STRB_WIDTH             ( STRB_WIDTH        ),
        // Number of regions per master interface
        .M_REGIONS              ( M_REGIONS         ),
        // Master interface base addresses
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of ADDR_WIDTH bits
        // set to zero for default addressing based on M_ADDR_WIDTH
        .M_BASE_ADDR            ( M_BASE_ADDR       ),
        // Master interface address widths
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of 32 bits
        .M_ADDR_WIDTH           ( M_ADDR_WIDTH      ),
        // Read connections between interfaces
        // M_COUNT concatenated fields of S_COUNT bits
        .M_CONNECT_READ         ( M_CONNECT_READ    ),
        // Write connections between interfaces
        // M_COUNT concatenated fields of S_COUNT bits
        .M_CONNECT_WRITE        ( M_CONNECT_WRITE   ),
        // Secure master (fail operations based on awprot/arprot)
        // M_COUNT bits
        .M_SECURE               ( M_SECURE          )
    ) AXIL_INTERCONNECT (
        .clk                    ( clk_i             ),
        .rst                    ( ~reset_ni         ),
    
        /*
         * AXI lite slave interfaces
         */
        .s_axil_awaddr          ( s_axil_awaddr_p   ),
        .s_axil_awprot          ( s_axil_awprot_p   ),
        .s_axil_awvalid         ( s_axil_awvalid_p  ),
        .s_axil_awready         ( s_axil_awready_p  ),
        .s_axil_wdata           ( s_axil_wdata_p    ),
        .s_axil_wstrb           ( s_axil_wstrb_p    ),
        .s_axil_wvalid          ( s_axil_wvalid_p   ),
        .s_axil_wready          ( s_axil_wready_p   ),
        .s_axil_bresp           ( s_axil_bresp_p    ),
        .s_axil_bvalid          ( s_axil_bvalid_p   ),
        .s_axil_bready          ( s_axil_bready_p   ),
        .s_axil_araddr          ( s_axil_araddr_p   ),
        .s_axil_arprot          ( s_axil_arprot_p   ),
        .s_axil_arvalid         ( s_axil_arvalid_p  ),
        .s_axil_arready         ( s_axil_arready_p  ),
        .s_axil_rdata           ( s_axil_rdata_p    ),
        .s_axil_rresp           ( s_axil_rresp_p    ),
        .s_axil_rvalid          ( s_axil_rvalid_p   ),
        .s_axil_rready          ( s_axil_rready_p   ),
    
        /*
         * AXI lite master interfaces
         */
        .m_axil_awaddr          ( m_axil_awaddr_p   ),
        .m_axil_awprot          ( m_axil_awprot_p   ),
        .m_axil_awvalid         ( m_axil_awvalid_p  ),
        .m_axil_awready         ( m_axil_awready_p  ),
        .m_axil_wdata           ( m_axil_wdata_p    ),
        .m_axil_wstrb           ( m_axil_wstrb_p    ),
        .m_axil_wvalid          ( m_axil_wvalid_p   ),
        .m_axil_wready          ( m_axil_wready_p   ),
        .m_axil_bresp           ( m_axil_bresp_p    ),
        .m_axil_bvalid          ( m_axil_bvalid_p   ),
        .m_axil_bready          ( m_axil_bready_p   ),
        .m_axil_araddr          ( m_axil_araddr_p   ),
        .m_axil_arprot          ( m_axil_arprot_p   ),
        .m_axil_arvalid         ( m_axil_arvalid_p  ),
        .m_axil_arready         ( m_axil_arready_p  ),
        .m_axil_rdata           ( m_axil_rdata_p    ),
        .m_axil_rresp           ( m_axil_rresp_p    ),
        .m_axil_rvalid          ( m_axil_rvalid_p   ),
        .m_axil_rready          ( m_axil_rready_p   )
    );
    
endmodule
















