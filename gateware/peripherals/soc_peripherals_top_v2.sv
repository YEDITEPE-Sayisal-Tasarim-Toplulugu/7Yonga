`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10.08.2025 10:27:49
// Design Name: 
// Module Name: soc_peripherals_top_v2
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
`include "soc_addr_rules.svh"

module soc_peripherals_top_v2
    import soc_addr_rules_pkg::*;
    #(parameter
            AXI_ID_WIDTH                    = 8,
            AXI_ADDR_WIDTH                  = 32,
            AXI_USER_WIDTH                  = 8,
            AXI_S_DATA_WIDTH                = 32,
            AXI_S_STRB_WIDTH                = 4,
            
            AXIL_ADDR_WIDTH                 = 20,
            AXIL_DATA_WIDTH                 = 32,
            AXIL_STRB_WIDTH                 = 4
    )
    (
        input   logic                       clk_i, reset_ni,
        
        // UART Interface
        output  logic                       peripheral_uart_tx_o, 
        input   logic                       peripheral_uart_rx_i,
        
        // QSPI Interface
        output logic                        qspi_sclk_o,
        output logic                        qspi_cs_no,
        output logic [3:0]                  qspi_data_o,
        input  logic [3:0]                  qspi_data_i,
        output logic [3:0]                  qspi_data_oen,   // Output enable (0: output, 1: input)
        
        /*
        * AXI slave interface
        */
        input   logic [AXI_ID_WIDTH-1:0]    s_axi_awid,
        input   logic [AXI_ADDR_WIDTH-1:0]  s_axi_awaddr,
        input   logic [7:0]                 s_axi_awlen,
        input   logic [2:0]                 s_axi_awsize,
        input   logic [1:0]                 s_axi_awburst,
        input   logic                       s_axi_awlock,
        input   logic [3:0]                 s_axi_awcache,
        input   logic [2:0]                 s_axi_awprot,
        input   logic [3:0]                 s_axi_awqos,
        input   logic [3:0]                 s_axi_awregion,
        input   logic [AXI_USER_WIDTH-1:0]  s_axi_awuser,
        input   logic                       s_axi_awvalid,
        output  logic                       s_axi_awready,
        input   logic [AXI_S_DATA_WIDTH-1:0]s_axi_wdata,
        input   logic [AXI_S_STRB_WIDTH-1:0]s_axi_wstrb,
        input   logic                       s_axi_wlast,
        input   logic [AXI_USER_WIDTH-1:0]  s_axi_wuser,
        input   logic                       s_axi_wvalid,
        output  logic                       s_axi_wready,
        output  logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
        output  logic [1:0]                 s_axi_bresp,
        output  logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
        output  logic                       s_axi_bvalid,
        input   logic                       s_axi_bready,
        input   logic [AXI_ID_WIDTH-1:0]    s_axi_arid,
        input   logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
        input   logic [7:0]                 s_axi_arlen,
        input   logic [2:0]                 s_axi_arsize,
        input   logic [1:0]                 s_axi_arburst,
        input   logic                       s_axi_arlock,
        input   logic [3:0]                 s_axi_arcache,
        input   logic [2:0]                 s_axi_arprot,
        input   logic [3:0]                 s_axi_arqos,
        input   logic [3:0]                 s_axi_arregion,
        input   logic [AXI_USER_WIDTH-1:0]  s_axi_aruser,
        input   logic                       s_axi_arvalid,
        output  logic                       s_axi_arready,
        output  logic [AXI_ID_WIDTH-1:0]    s_axi_rid,
        output  logic [AXI_S_DATA_WIDTH-1:0]s_axi_rdata,
        output  logic [1:0]                 s_axi_rresp,
        output  logic                       s_axi_rlast,
        output  logic [AXI_USER_WIDTH-1:0]  s_axi_ruser,
        output  logic                       s_axi_rvalid,
        input   logic                       s_axi_rready
    );
    
    localparam integer AXIL_MASTER_COUNT    = 1;
    localparam integer AXIL_SLAVE_COUNT     = 2;
    
    localparam integer AXIL_UART_PORT       = 0;
    localparam integer AXIL_QSPI_PORT       = 1;
    
    localparam AXIL_ADDR_DECODE_POINT       = 32'd16;
    
    /*
     * AXI lite slave interfaces
     */
    logic [AXIL_ADDR_WIDTH-1:0]         s_axil_awaddr   [0:AXIL_MASTER_COUNT-1];
    logic [2:0]                         s_axil_awprot   [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_awvalid;
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_awready;
    logic [AXIL_DATA_WIDTH-1:0]         s_axil_wdata    [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_STRB_WIDTH-1:0]         s_axil_wstrb    [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_wvalid;
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_wready;
    logic [1:0]                         s_axil_bresp    [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_bvalid;
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_bready;
    logic [AXIL_ADDR_WIDTH-1:0]         s_axil_araddr   [0:AXIL_MASTER_COUNT-1];
    logic [2:0]                         s_axil_arprot   [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_arvalid;
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_arready;
    logic [AXIL_DATA_WIDTH-1:0]         s_axil_rdata    [0:AXIL_MASTER_COUNT-1];
    logic [1:0]                         s_axil_rresp    [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_rvalid;
    logic [AXIL_MASTER_COUNT-1:0]       s_axil_rready;

    /*
     * AXI lite master interfaces
     */
    logic [AXIL_ADDR_WIDTH-1:0]         m_axil_awaddr   [0:AXIL_SLAVE_COUNT-1];
    logic [2:0]                         m_axil_awprot   [0:AXIL_SLAVE_COUNT-1];
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_awvalid;
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_awready;
    logic [AXIL_DATA_WIDTH-1:0]         m_axil_wdata    [0:AXIL_SLAVE_COUNT-1];
    logic [AXIL_STRB_WIDTH-1:0]         m_axil_wstrb    [0:AXIL_SLAVE_COUNT-1];
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_wvalid;
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_wready;
    logic [1:0]                         m_axil_bresp    [0:AXIL_SLAVE_COUNT-1];
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_bvalid;
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_bready;
    logic [AXIL_ADDR_WIDTH-1:0]         m_axil_araddr   [0:AXIL_SLAVE_COUNT-1];
    logic [2:0]                         m_axil_arprot   [0:AXIL_SLAVE_COUNT-1];
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_arvalid;
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_arready;
    logic [AXIL_DATA_WIDTH-1:0]         m_axil_rdata    [0:AXIL_SLAVE_COUNT-1];
    logic [1:0]                         m_axil_rresp    [0:AXIL_SLAVE_COUNT-1];
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_rvalid;
    logic [AXIL_SLAVE_COUNT-1:0]        m_axil_rready;
    
    logic [AXIL_ADDR_WIDTH-1:0]         s_axil_awaddr_dec   [0:AXIL_MASTER_COUNT-1];
    logic [AXIL_ADDR_WIDTH-1:0]         s_axil_araddr_dec   [0:AXIL_MASTER_COUNT-1];
    
    generate
        for (genvar k=0; k<AXIL_MASTER_COUNT; k++) begin
            assign s_axil_awaddr_dec[k] = s_axil_awaddr[k] - (1 << AXIL_ADDR_DECODE_POINT);
            assign s_axil_araddr_dec[k] = s_axil_araddr[k] - (1 << AXIL_ADDR_DECODE_POINT);
        end
    endgenerate
    
    uart UART (
        // Clock and reset signals
        .s_axi_aclk             ( clk_i                             ),
        .s_axi_aresetn          ( reset_ni                          ),
        
        // AXI4-Lite Slave Arayüzü
        // Write Address Channel
        .s_axi_awaddr           ( m_axil_awaddr[AXIL_UART_PORT]     ),
        .s_axi_awvalid          ( m_axil_awvalid[AXIL_UART_PORT]    ),
        .s_axi_awready          ( m_axil_awready[AXIL_UART_PORT]    ),
        
        // Write Data Channel
        .s_axi_wdata            ( m_axil_wdata[AXIL_UART_PORT]      ),
        .s_axi_wstrb            ( m_axil_wstrb[AXIL_UART_PORT]      ),
        .s_axi_wvalid           ( m_axil_wvalid[AXIL_UART_PORT]     ),
        .s_axi_wready           ( m_axil_wready[AXIL_UART_PORT]     ),
        
        // Write Response Channel
        .s_axi_bresp            ( m_axil_bresp[AXIL_UART_PORT]      ),
        .s_axi_bvalid           ( m_axil_bvalid[AXIL_UART_PORT]     ),
        .s_axi_bready           ( m_axil_bready[AXIL_UART_PORT]     ),
        
        // Read Address Channel
        .s_axi_araddr           ( m_axil_araddr[AXIL_UART_PORT]     ),
        .s_axi_arvalid          ( m_axil_arvalid[AXIL_UART_PORT]    ),
        .s_axi_arready          ( m_axil_arready[AXIL_UART_PORT]    ),
        
        // Read Data Channel
        .s_axi_rdata            ( m_axil_rdata[AXIL_UART_PORT]      ),
        .s_axi_rresp            ( m_axil_rresp[AXIL_UART_PORT]      ),
        .s_axi_rvalid           ( m_axil_rvalid[AXIL_UART_PORT]     ),
        .s_axi_rready           ( m_axil_rready[AXIL_UART_PORT]     ),
        
        // UART pins
        .uart_rx                ( peripheral_uart_rx_i              ),
        .uart_tx                ( peripheral_uart_tx_o              )
    );
    
    qspi_master #(
        .AXI_ADDR_WIDTH         ( AXIL_ADDR_WIDTH                   ),
        .AXI_DATA_WIDTH         ( AXIL_DATA_WIDTH                   )
    ) QSPI (
        // Sistem sinyalleri
        .clk_i                  ( clk_i                             ),
        .rst_ni                 ( reset_ni                          ),
        
        // AXI4-Lite Slave Arayüzü
        // Write Address Channel
        .s_axi_awaddr           ( m_axil_awaddr[AXIL_QSPI_PORT]     ),
        .s_axi_awvalid          ( m_axil_awvalid[AXIL_QSPI_PORT]    ),
        .s_axi_awready          ( m_axil_awready[AXIL_QSPI_PORT]    ),
        
        // Write Data Channel
        .s_axi_wdata            ( m_axil_wdata[AXIL_QSPI_PORT]      ),
        .s_axi_wstrb            ( m_axil_wstrb[AXIL_QSPI_PORT]      ),
        .s_axi_wvalid           ( m_axil_wvalid[AXIL_QSPI_PORT]     ),
        .s_axi_wready           ( m_axil_wready[AXIL_QSPI_PORT]     ),
        
        // Write Response Channel
        .s_axi_bresp            ( m_axil_bresp[AXIL_QSPI_PORT]      ),
        .s_axi_bvalid           ( m_axil_bvalid[AXIL_QSPI_PORT]     ),
        .s_axi_bready           ( m_axil_bready[AXIL_QSPI_PORT]     ),
        
        // Read Address Channel
        .s_axi_araddr           ( m_axil_araddr[AXIL_QSPI_PORT]     ),
        .s_axi_arvalid          ( m_axil_arvalid[AXIL_QSPI_PORT]    ),
        .s_axi_arready          ( m_axil_arready[AXIL_QSPI_PORT]    ),
        
        // Read Data Channel
        .s_axi_rdata            ( m_axil_rdata[AXIL_QSPI_PORT]      ),
        .s_axi_rresp            ( m_axil_rresp[AXIL_QSPI_PORT]      ),
        .s_axi_rvalid           ( m_axil_rvalid[AXIL_QSPI_PORT]     ),
        .s_axi_rready           ( m_axil_rready[AXIL_QSPI_PORT]     ),
        
        // QSPI Interface
        .qspi_sclk_o            ( qspi_sclk_o                       ),
        .qspi_cs_no             ( qspi_cs_no                        ),
        .qspi_data_o            ( qspi_data_o                       ),
        .qspi_data_i            ( qspi_data_i                       ),
        .qspi_data_oen          ( qspi_data_oen                     )
    );
    
    axi_axil_adapter #(
        // Width of address bus in bits
        .ADDR_WIDTH             ( AXIL_ADDR_WIDTH   ),
        // Width of input (slave) AXI interface data bus in bits
        .AXI_DATA_WIDTH         ( AXI_S_DATA_WIDTH  ),
        // Width of AXI ID signal
        .AXI_ID_WIDTH           ( AXI_ID_WIDTH      ),
        // Width of output (master) AXI lite interface data bus in bits
        .AXIL_DATA_WIDTH        ( AXIL_DATA_WIDTH   ),
        // When adapting to a wider bus, re-pack full-width burst instead of passing through narrow burst if possible
        .CONVERT_BURST          ( 1                 ),
        // When adapting to a wider bus, re-pack all bursts instead of passing through narrow burst if possible
        .CONVERT_NARROW_BURST   ( 0                 )
    ) AXI4_TO_AXI4LITE (
        .clk                    ( clk_i             ),
        .rst                    ( ~reset_ni         ),
    
        /*
         * AXI slave interface
         */
        .s_axi_awid             ( s_axi_awid        ),
        .s_axi_awaddr           ( s_axi_awaddr[AXIL_ADDR_WIDTH-1:0]),
        .s_axi_awlen            ( s_axi_awlen       ),
        .s_axi_awsize           ( s_axi_awsize      ),
        .s_axi_awburst          ( s_axi_awburst     ),
        .s_axi_awlock           ( s_axi_awlock      ),
        .s_axi_awcache          ( s_axi_awcache     ),
        .s_axi_awprot           ( s_axi_awprot      ),
        .s_axi_awvalid          ( s_axi_awvalid     ),
        .s_axi_awready          ( s_axi_awready     ),
        .s_axi_wdata            ( s_axi_wdata       ),
        .s_axi_wstrb            ( s_axi_wstrb       ),
        .s_axi_wlast            ( s_axi_wlast       ),
        .s_axi_wvalid           ( s_axi_wvalid      ),
        .s_axi_wready           ( s_axi_wready      ),
        .s_axi_bid              ( s_axi_bid         ),
        .s_axi_bresp            ( s_axi_bresp       ),
        .s_axi_bvalid           ( s_axi_bvalid      ),
        .s_axi_bready           ( s_axi_bready      ),
        .s_axi_arid             ( s_axi_arid        ),
        .s_axi_araddr           ( s_axi_araddr[AXIL_ADDR_WIDTH-1:0]),
        .s_axi_arlen            ( s_axi_arlen       ),
        .s_axi_arsize           ( s_axi_arsize      ),
        .s_axi_arburst          ( s_axi_arburst     ),
        .s_axi_arlock           ( s_axi_arlock      ),
        .s_axi_arcache          ( s_axi_arcache     ),
        .s_axi_arprot           ( s_axi_arprot      ),
        .s_axi_arvalid          ( s_axi_arvalid     ),
        .s_axi_arready          ( s_axi_arready     ),
        .s_axi_rid              ( s_axi_rid         ),
        .s_axi_rdata            ( s_axi_rdata       ),
        .s_axi_rresp            ( s_axi_rresp       ),
        .s_axi_rlast            ( s_axi_rlast       ),
        .s_axi_rvalid           ( s_axi_rvalid      ),
        .s_axi_rready           ( s_axi_rready      ),
    
        /*
         * AXI lite master interface
         */
        .m_axil_awaddr          ( s_axil_awaddr  [0]),
        .m_axil_awprot          ( s_axil_awprot  [0]),
        .m_axil_awvalid         ( s_axil_awvalid [0]),
        .m_axil_awready         ( s_axil_awready [0]),
        .m_axil_wdata           ( s_axil_wdata   [0]),
        .m_axil_wstrb           ( s_axil_wstrb   [0]),
        .m_axil_wvalid          ( s_axil_wvalid  [0]),
        .m_axil_wready          ( s_axil_wready  [0]),
        .m_axil_bresp           ( s_axil_bresp   [0]),
        .m_axil_bvalid          ( s_axil_bvalid  [0]),
        .m_axil_bready          ( s_axil_bready  [0]),
        .m_axil_araddr          ( s_axil_araddr  [0]),
        .m_axil_arprot          ( s_axil_arprot  [0]),
        .m_axil_arvalid         ( s_axil_arvalid [0]),
        .m_axil_arready         ( s_axil_arready [0]),
        .m_axil_rdata           ( s_axil_rdata   [0]),
        .m_axil_rresp           ( s_axil_rresp   [0]),
        .m_axil_rvalid          ( s_axil_rvalid  [0]),
        .m_axil_rready          ( s_axil_rready  [0])
    );
    
    //////////////////////////////////////////////////
    assign s_axi_ruser = 0;
    assign s_axi_buser = 0;
    //////////////////////////////////////////////////
    
    axil_interconnect_wrap #(
        // Number of AXI inputs (slave interfaces)
        .S_COUNT            ( AXIL_MASTER_COUNT ),
        // Number of AXI outputs (master interfaces)
        .M_COUNT            ( AXIL_SLAVE_COUNT  ),
        // Width of data bus in bits
        .DATA_WIDTH         ( AXIL_DATA_WIDTH   ),
        // Width of address bus in bits
        .ADDR_WIDTH         ( AXIL_ADDR_WIDTH   ),
        // Number of regions per master interface
        .M_REGIONS          ( 1                 ),
        // Master interface address widths
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of 32 bits
        // parameter M_ADDR_WIDTH = {M_COUNT{{M_REGIONS{32'd24}}}},
        .M_ADDR_WIDTH       ({AXIL_SLAVE_COUNT{{1{AXIL_ADDR_DECODE_POINT}}}})
    ) PERIPHERAL_BUS (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        /*
         * AXI lite slave interfaces
         */
        .s_axil_awaddr      ( s_axil_awaddr_dec ),
        .s_axil_awprot      ( s_axil_awprot     ),
        .s_axil_awvalid     ( s_axil_awvalid    ),
        .s_axil_awready     ( s_axil_awready    ),
        .s_axil_wdata       ( s_axil_wdata      ),
        .s_axil_wstrb       ( s_axil_wstrb      ),
        .s_axil_wvalid      ( s_axil_wvalid     ),
        .s_axil_wready      ( s_axil_wready     ),
        .s_axil_bresp       ( s_axil_bresp      ),
        .s_axil_bvalid      ( s_axil_bvalid     ),
        .s_axil_bready      ( s_axil_bready     ),
        .s_axil_araddr      ( s_axil_araddr_dec ),
        .s_axil_arprot      ( s_axil_arprot     ),
        .s_axil_arvalid     ( s_axil_arvalid    ),
        .s_axil_arready     ( s_axil_arready    ),
        .s_axil_rdata       ( s_axil_rdata      ),
        .s_axil_rresp       ( s_axil_rresp      ),
        .s_axil_rvalid      ( s_axil_rvalid     ),
        .s_axil_rready      ( s_axil_rready     ),
    
        /*
         * AXI lite master interfaces
         */
        .m_axil_awaddr      ( m_axil_awaddr     ),
        .m_axil_awprot      ( m_axil_awprot     ),
        .m_axil_awvalid     ( m_axil_awvalid    ),
        .m_axil_awready     ( m_axil_awready    ),
        .m_axil_wdata       ( m_axil_wdata      ),
        .m_axil_wstrb       ( m_axil_wstrb      ),
        .m_axil_wvalid      ( m_axil_wvalid     ),
        .m_axil_wready      ( m_axil_wready     ),
        .m_axil_bresp       ( m_axil_bresp      ),
        .m_axil_bvalid      ( m_axil_bvalid     ),
        .m_axil_bready      ( m_axil_bready     ),
        .m_axil_araddr      ( m_axil_araddr     ),
        .m_axil_arprot      ( m_axil_arprot     ),
        .m_axil_arvalid     ( m_axil_arvalid    ),
        .m_axil_arready     ( m_axil_arready    ),
        .m_axil_rdata       ( m_axil_rdata      ),
        .m_axil_rresp       ( m_axil_rresp      ),
        .m_axil_rvalid      ( m_axil_rvalid     ),
        .m_axil_rready      ( m_axil_rready     )
    );
    
endmodule

















