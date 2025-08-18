`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 17:59:50
// Design Name: 
// Module Name: soc_top
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

module soc_top
    import soc_addr_rules_pkg::*;
    import soc_config_pkg::*; 
    (
        input   logic clk_i, reset_ni,
        
        // UART Programmmer
        input   logic programmer_reset_ni,
        input   logic programmer_enable_i,
        input   logic programmer_rx,
        
        // UART Interface
        output  logic                       peripheral_uart_tx_o, 
        input   logic                       peripheral_uart_rx_i,
        
        // QSPI Interface
        output  logic                        peripheral_qspi_sclk_o,
        output  logic                        peripheral_qspi_cs_no,
        output  logic [3:0]                  peripheral_qspi_data_o,
        input   logic [3:0]                  peripheral_qspi_data_i,
        output  logic [3:0]                  peripheral_qspi_data_oen   // Output enable (0: output, 1: input)
    );
    
    localparam integer INST_MEMORY_SIZE_IN_KB   = 8;
    localparam integer DATA_MEMORY_SIZE_IN_KB   = 8;
    
    localparam integer CORE_ADDR_WIDTH          = 32;
    localparam integer CORE_DATA_WIDTH          = 32;
    localparam integer CORE_BE_WIDTH            = 4;
    
    localparam integer AXI_MASTER_COUNT         = 1;
    localparam integer AXI_SLAVE_COUNT          = 3;
    
    localparam integer AXI_ADDR_WIDTH           = 32;
    localparam integer AXI_DATA_WIDTH           = 32;
    localparam integer AXI_M_ID_WIDTH           = 8;
    localparam integer AXI_S_ID_WIDTH           = AXI_M_ID_WIDTH+$clog2(AXI_MASTER_COUNT);
    localparam integer AXI_USER_WIDTH           = 1;
    localparam integer AXI_STRB_WIDTH           = (AXI_DATA_WIDTH/8);
    
    localparam integer AXI_INST_TOP_ID          = 0;
    localparam integer AXI_PERIPHERAL_TOP_ID    = 1;
    localparam integer AXI_DATA_TOP_ID          = 2;
    
    localparam integer AXIL_ADDR_WIDTH          = 20;
    localparam integer AXIL_DATA_WIDTH          = 32;
    localparam integer AXIL_STRB_WIDTH          = AXIL_DATA_WIDTH/8;
    
    logic [31:0] CORE_boot_addr_w, CORE_mtvec_addr_w, CORE_dm_halt_addr_w, CORE_hart_id_w, CORE_dm_exception_addr_w;
    assign CORE_boot_addr_w           = soc_config_pkg::CORE_BOOT_ADDR;
    assign CORE_mtvec_addr_w          = soc_config_pkg::CORE_MTVEC_ADDR;
    assign CORE_dm_halt_addr_w        = soc_config_pkg::CORE_DM_HALT_ADDR;
    assign CORE_hart_id_w             = soc_config_pkg::CORE_HART_ID;
    assign CORE_dm_exception_addr_w   = soc_config_pkg::CORE_DM_EXCEPTION_ADDR;
    
    logic [CORE_ADDR_WIDTH-1:0]             core_instr_addr_w;
    logic                                   core_instr_req_w;
    logic                                   core_instr_gnt_w;
    logic                                   core_instr_rvalid_w;
    logic [31:0]                            core_instr_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0]             core_data_addr_w;
    logic                                   core_data_req_w;
    logic                                   core_data_we_w;
    logic [CORE_BE_WIDTH-1:0]               core_data_be_w;
    logic [CORE_DATA_WIDTH-1:0]             core_data_wdata_w;
    logic                                   core_data_gnt_w;
    logic                                   core_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0]             core_data_rdata_w;
    
    /*
     * AXI slave interfaces
     */
    logic [AXI_M_ID_WIDTH-1:0]              s_axi_awid      [0:AXI_MASTER_COUNT-1];
    logic [AXI_ADDR_WIDTH-1:0]              s_axi_awaddr    [0:AXI_MASTER_COUNT-1];
    logic [7:0]                             s_axi_awlen     [0:AXI_MASTER_COUNT-1];
    logic [2:0]                             s_axi_awsize    [0:AXI_MASTER_COUNT-1];
    logic [1:0]                             s_axi_awburst   [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_awlock;
    logic [3:0]                             s_axi_awcache   [0:AXI_MASTER_COUNT-1];
    logic [2:0]                             s_axi_awprot    [0:AXI_MASTER_COUNT-1];
    logic [3:0]                             s_axi_awqos     [0:AXI_MASTER_COUNT-1];
    logic [AXI_USER_WIDTH-1:0]              s_axi_awuser    [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_awvalid;
    logic [AXI_MASTER_COUNT-1:0]            s_axi_awready;
    logic [AXI_DATA_WIDTH-1:0]              s_axi_wdata     [0:AXI_MASTER_COUNT-1];
    logic [AXI_STRB_WIDTH-1:0]              s_axi_wstrb     [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]              s_axi_wuser     [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_wvalid;
    logic [AXI_MASTER_COUNT-1:0]            s_axi_wready;
    logic [AXI_M_ID_WIDTH-1:0]              s_axi_bid       [0:AXI_MASTER_COUNT-1];
    logic [1:0]                             s_axi_bresp     [0:AXI_MASTER_COUNT-1];
    logic [AXI_USER_WIDTH-1:0]              s_axi_buser     [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_bvalid;
    logic [AXI_MASTER_COUNT-1:0]            s_axi_bready;
    logic [AXI_M_ID_WIDTH-1:0]              s_axi_arid      [0:AXI_MASTER_COUNT-1];
    logic [AXI_ADDR_WIDTH-1:0]              s_axi_araddr    [0:AXI_MASTER_COUNT-1];
    logic [7:0]                             s_axi_arlen     [0:AXI_MASTER_COUNT-1];
    logic [2:0]                             s_axi_arsize    [0:AXI_MASTER_COUNT-1];
    logic [1:0]                             s_axi_arburst   [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_arlock;
    logic [3:0]                             s_axi_arcache   [0:AXI_MASTER_COUNT-1];
    logic [2:0]                             s_axi_arprot    [0:AXI_MASTER_COUNT-1];
    logic [3:0]                             s_axi_arqos     [0:AXI_MASTER_COUNT-1];
    logic [AXI_USER_WIDTH-1:0]              s_axi_aruser    [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_arvalid;
    logic [AXI_MASTER_COUNT-1:0]            s_axi_arready;
    logic [AXI_M_ID_WIDTH-1:0]              s_axi_rid       [0:AXI_MASTER_COUNT-1];
    logic [AXI_DATA_WIDTH-1:0]              s_axi_rdata     [0:AXI_MASTER_COUNT-1];
    logic [1:0]                             s_axi_rresp     [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]              s_axi_ruser     [0:AXI_MASTER_COUNT-1];
    logic [AXI_MASTER_COUNT-1:0]            s_axi_rvalid;
    logic [AXI_MASTER_COUNT-1:0]            s_axi_rready;
    
    /*
    * AXI master interfaces
    */
    logic [AXI_S_ID_WIDTH-1:0]              m_axi_awid      [0:AXI_SLAVE_COUNT-1];
    logic [AXI_ADDR_WIDTH-1:0]              m_axi_awaddr    [0:AXI_SLAVE_COUNT-1];
    logic [7:0]                             m_axi_awlen     [0:AXI_SLAVE_COUNT-1];
    logic [2:0]                             m_axi_awsize    [0:AXI_SLAVE_COUNT-1];
    logic [1:0]                             m_axi_awburst   [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_awlock;
    logic [3:0]                             m_axi_awcache   [0:AXI_SLAVE_COUNT-1];
    logic [2:0]                             m_axi_awprot    [0:AXI_SLAVE_COUNT-1];
    logic [3:0]                             m_axi_awqos     [0:AXI_SLAVE_COUNT-1];
    logic [3:0]                             m_axi_awregion  [0:AXI_SLAVE_COUNT-1];
    logic [AXI_USER_WIDTH-1:0]              m_axi_awuser    [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_awvalid;
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_awready;
    logic [AXI_DATA_WIDTH-1:0]              m_axi_wdata     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_STRB_WIDTH-1:0]              m_axi_wstrb     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]              m_axi_wuser     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_wvalid;
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_wready;
    logic [AXI_S_ID_WIDTH-1:0]              m_axi_bid       [0:AXI_SLAVE_COUNT-1];
    logic [1:0]                             m_axi_bresp     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_USER_WIDTH-1:0]              m_axi_buser     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_bvalid;
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_bready;
    logic [AXI_S_ID_WIDTH-1:0]              m_axi_arid      [0:AXI_SLAVE_COUNT-1];
    logic [AXI_ADDR_WIDTH-1:0]              m_axi_araddr    [0:AXI_SLAVE_COUNT-1];
    logic [7:0]                             m_axi_arlen     [0:AXI_SLAVE_COUNT-1];
    logic [2:0]                             m_axi_arsize    [0:AXI_SLAVE_COUNT-1];
    logic [1:0]                             m_axi_arburst   [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_arlock;
    logic [3:0]                             m_axi_arcache   [0:AXI_SLAVE_COUNT-1];
    logic [2:0]                             m_axi_arprot    [0:AXI_SLAVE_COUNT-1];
    logic [3:0]                             m_axi_arqos     [0:AXI_SLAVE_COUNT-1];
    logic [3:0]                             m_axi_arregion  [0:AXI_SLAVE_COUNT-1];
    logic [AXI_USER_WIDTH-1:0]              m_axi_aruser    [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_arvalid;
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_arready;
    logic [AXI_S_ID_WIDTH-1:0]              m_axi_rid       [0:AXI_SLAVE_COUNT-1];
    logic [AXI_DATA_WIDTH-1:0]              m_axi_rdata     [0:AXI_SLAVE_COUNT-1];
    logic [1:0]                             m_axi_rresp     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]              m_axi_ruser     [0:AXI_SLAVE_COUNT-1];
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_rvalid;
    logic [AXI_SLAVE_COUNT-1:0]             m_axi_rready;
    
    logic mem_write_enable_w;
    logic [31:0] mem_write_addr_w;
    logic [31:0] mem_write_data_w;
    
generate
    if (soc_config_pkg::UART_PROGRAMMER_EXISTS) begin : UART_PROGRAMMER
        uart_programmer_top
        #( 
            .FREQ_HZ                    ( soc_config_pkg::SOC_FREQUENCY_HZ                      ),
            .PROGRAMMER_BAUDE_RATE      ( soc_config_pkg::UART_PROGRAMMER_BAUDE_RATE            ),
            .MEM_START_ADDR             ( soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.start_addr    ),
            .MEM_INC_COUNT              ( 4                                                     )
        ) PROGRAMMER_MODULE (
            .clk_i                      ( clk_i                             ),
            .reset_ni                   ( programmer_reset_ni               ),
            
            .programmer_enable_i        ( programmer_enable_i               ),
            .programmer_rx              ( programmer_rx                     ),
            
            .mem_write_enable_o         ( mem_write_enable_w                ),
            .mem_write_addr_o           ( mem_write_addr_w                  ),
            .mem_write_data_o           ( mem_write_data_w                  )
        );
    end else begin
        assign mem_write_enable_w   = 0;
        assign mem_write_addr_w     = 0;
        assign mem_write_data_w     = 0;
    end
endgenerate
    
    cv32e40p_top #(
        .COREV_PULP         (soc_config_pkg::CORE_CONF_COREV_PULP),  // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. cv.elw)
        .COREV_CLUSTER      (soc_config_pkg::CORE_CONF_COREV_CLUSTER),  // PULP Cluster interface (incl. cv.elw)
        .FPU                (soc_config_pkg::CORE_CONF_FPU),  // Floating Point Unit (interfaced via APU interface)
        .FPU_ADDMUL_LAT     (soc_config_pkg::CORE_CONF_FPU_ADDMUL_LAT),  // Floating-Point ADDition/MULtiplication computing lane pipeline registers number
        .FPU_OTHERS_LAT     (soc_config_pkg::CORE_CONF_FPU_OTHERS_LAT),  // Floating-Point COMParison/CONVersion computing lanes pipeline registers number
        .ZFINX              (soc_config_pkg::CORE_CONF_ZFINX),  // Float-in-General Purpose registers
        .NUM_MHPMCOUNTERS   (soc_config_pkg::CORE_CONF_NUM_MHPMCOUNTERS)
    ) CORE_CV32E40P (
        // Clock and Reset
        .clk_i                  ( clk_i                         ),
        .rst_ni                 ( reset_ni                      ),
        
        // PULP clock enable (only used if COREV_CLUSTER = 1)
        .pulp_clock_en_i        ( 1'b0),
        // Enable all clock gates for testing
        .scan_cg_en_i           ( 1'b0),  
        
        // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
        .boot_addr_i            ( CORE_boot_addr_w              ),
        .mtvec_addr_i           ( CORE_mtvec_addr_w             ),
        .dm_halt_addr_i         ( CORE_dm_halt_addr_w           ),
        .hart_id_i              ( CORE_hart_id_w                ),
        .dm_exception_addr_i    ( CORE_dm_exception_addr_w      ),
        
        // Instruction memory interface
        .instr_req_o            ( core_instr_req_w              ),
        .instr_gnt_i            ( core_instr_gnt_w              ),
        .instr_rvalid_i         ( core_instr_rvalid_w           ),
        .instr_addr_o           ( core_instr_addr_w             ),
        .instr_rdata_i          ( core_instr_rdata_w            ),
        
        // Data memory interface
        .data_req_o             ( core_data_req_w               ),
        .data_gnt_i             ( core_data_gnt_w               ),
        .data_rvalid_i          ( core_data_rvalid_w            ),
        .data_we_o              ( core_data_we_w                ),
        .data_be_o              ( core_data_be_w                ),
        .data_addr_o            ( core_data_addr_w              ),
        .data_wdata_o           ( core_data_wdata_w             ),
        .data_rdata_i           ( core_data_rdata_w             ),
        
        // Interrupt inputs
        // CLINT interrupts + CLINT extension interrupts
        .irq_i                  ( 'd0),
        .irq_ack_o              (),
        .irq_id_o               (),
        
        // Debug Interface
        .debug_req_i            ( 1'b0),
        .debug_havereset_o      (),
        .debug_running_o        (),
        .debug_halted_o         (),
        
        // CPU Control Signals
        .fetch_enable_i         (1'b1),
        .core_sleep_o           ()
    );
    
    core_inst_top_v2 #(
        .INST_MEMORY_SIZE_IN_KB         ( INST_MEMORY_SIZE_IN_KB    ),
        .CORE_ADDR_WIDTH                ( CORE_ADDR_WIDTH           ),
        .CORE_DATA_WIDTH                ( CORE_DATA_WIDTH           ),
        .CORE_BE_WIDTH                  ( CORE_BE_WIDTH             ),
        .ID_WIDTH                       ( AXI_S_ID_WIDTH            ),
        .ADDR_WIDTH                     ( AXI_ADDR_WIDTH            ),
        .USER_WIDTH                     ( AXI_USER_WIDTH            ),
        .S_DATA_WIDTH                   ( AXI_DATA_WIDTH            ),
        .S_STRB_WIDTH                   ( AXI_STRB_WIDTH            )
    ) CORE_INSTRUCTION_TOP (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        // programmer_port
        .programmer_mem_write_enable_i  ( mem_write_enable_w    ),
        .programmer_mem_write_addr_i    ( mem_write_addr_w      ),
        .programmer_mem_write_data_i    ( mem_write_data_w      ),
        
        .core_instr_addr_i              ( core_instr_addr_w     ),
        .core_instr_req_i               ( core_instr_req_w      ),
        .core_instr_gnt_o               ( core_instr_gnt_w      ),
        .core_instr_rvalid_o            ( core_instr_rvalid_w   ),
        .core_instr_rdata_o             ( core_instr_rdata_w    ),
        
        /*
        * AXI slave interface
        */
        .s_axi_awid             ( m_axi_awid    [AXI_INST_TOP_ID]),
        .s_axi_awaddr           ( m_axi_awaddr  [AXI_INST_TOP_ID]),
        .s_axi_awlen            ( m_axi_awlen   [AXI_INST_TOP_ID]),
        .s_axi_awsize           ( m_axi_awsize  [AXI_INST_TOP_ID]),
        .s_axi_awburst          ( m_axi_awburst [AXI_INST_TOP_ID]),
        .s_axi_awlock           ( m_axi_awlock  [AXI_INST_TOP_ID]),
        .s_axi_awcache          ( m_axi_awcache [AXI_INST_TOP_ID]),
        .s_axi_awprot           ( m_axi_awprot  [AXI_INST_TOP_ID]),
        .s_axi_awqos            ( m_axi_awqos   [AXI_INST_TOP_ID]),
        .s_axi_awregion         ( m_axi_awregion[AXI_INST_TOP_ID]),
        .s_axi_awuser           ( m_axi_awuser  [AXI_INST_TOP_ID]),
        .s_axi_awvalid          ( m_axi_awvalid [AXI_INST_TOP_ID]),
        .s_axi_awready          ( m_axi_awready [AXI_INST_TOP_ID]),
        .s_axi_wdata            ( m_axi_wdata   [AXI_INST_TOP_ID]),
        .s_axi_wstrb            ( m_axi_wstrb   [AXI_INST_TOP_ID]),
        .s_axi_wlast            ( m_axi_wlast   [AXI_INST_TOP_ID]),
        .s_axi_wuser            ( m_axi_wuser   [AXI_INST_TOP_ID]),
        .s_axi_wvalid           ( m_axi_wvalid  [AXI_INST_TOP_ID]),
        .s_axi_wready           ( m_axi_wready  [AXI_INST_TOP_ID]),
        .s_axi_bid              ( m_axi_bid     [AXI_INST_TOP_ID]),
        .s_axi_bresp            ( m_axi_bresp   [AXI_INST_TOP_ID]),
        .s_axi_buser            ( m_axi_buser   [AXI_INST_TOP_ID]),
        .s_axi_bvalid           ( m_axi_bvalid  [AXI_INST_TOP_ID]),
        .s_axi_bready           ( m_axi_bready  [AXI_INST_TOP_ID]),
        .s_axi_arid             ( m_axi_arid    [AXI_INST_TOP_ID]),
        .s_axi_araddr           ( m_axi_araddr  [AXI_INST_TOP_ID]),
        .s_axi_arlen            ( m_axi_arlen   [AXI_INST_TOP_ID]),
        .s_axi_arsize           ( m_axi_arsize  [AXI_INST_TOP_ID]),
        .s_axi_arburst          ( m_axi_arburst [AXI_INST_TOP_ID]),
        .s_axi_arlock           ( m_axi_arlock  [AXI_INST_TOP_ID]),
        .s_axi_arcache          ( m_axi_arcache [AXI_INST_TOP_ID]),
        .s_axi_arprot           ( m_axi_arprot  [AXI_INST_TOP_ID]),
        .s_axi_arqos            ( m_axi_arqos   [AXI_INST_TOP_ID]),
        .s_axi_arregion         ( m_axi_arregion[AXI_INST_TOP_ID]),
        .s_axi_aruser           ( m_axi_aruser  [AXI_INST_TOP_ID]),
        .s_axi_arvalid          ( m_axi_arvalid [AXI_INST_TOP_ID]),
        .s_axi_arready          ( m_axi_arready [AXI_INST_TOP_ID]),
        .s_axi_rid              ( m_axi_rid     [AXI_INST_TOP_ID]),
        .s_axi_rdata            ( m_axi_rdata   [AXI_INST_TOP_ID]),
        .s_axi_rresp            ( m_axi_rresp   [AXI_INST_TOP_ID]),
        .s_axi_rlast            ( m_axi_rlast   [AXI_INST_TOP_ID]),
        .s_axi_ruser            ( m_axi_ruser   [AXI_INST_TOP_ID]),
        .s_axi_rvalid           ( m_axi_rvalid  [AXI_INST_TOP_ID]),
        .s_axi_rready           ( m_axi_rready  [AXI_INST_TOP_ID])
    );
    
    core_data_top #(
        .DATA_MEMORY_SIZE_IN_KB ( DATA_MEMORY_SIZE_IN_KB        ),
        .CORE_ADDR_WIDTH        ( CORE_ADDR_WIDTH               ),
        .CORE_DATA_WIDTH        ( CORE_DATA_WIDTH               ),
        .CORE_BE_WIDTH          ( CORE_BE_WIDTH                 ),
        .ID_WIDTH               ( AXI_S_ID_WIDTH                ),
        .ADDR_WIDTH             ( AXI_ADDR_WIDTH                ),
        .USER_WIDTH             ( AXI_USER_WIDTH                ),
        .M_DATA_WIDTH           ( AXI_DATA_WIDTH                ),
        .M_STRB_WIDTH           ( AXI_STRB_WIDTH                ),
        .S_DATA_WIDTH           ( AXI_DATA_WIDTH                ),
        .S_STRB_WIDTH           ( AXI_STRB_WIDTH                )
    ) CORE_DATA_TOP (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .core_data_addr_i       ( core_data_addr_w              ),
        .core_data_req_i        ( core_data_req_w               ),
        .core_data_we_i         ( core_data_we_w                ),
        .core_data_be_i         ( core_data_be_w                ),
        .core_data_wdata_i      ( core_data_wdata_w             ),
        .core_data_gnt_o        ( core_data_gnt_w               ),
        .core_data_rvalid_o     ( core_data_rvalid_w            ),
        .core_data_rdata_o      ( core_data_rdata_w             ),
        
        /*
         * AXI master interface
         */
        .m_axi_awid             ( s_axi_awid   [0]),
        .m_axi_awaddr           ( s_axi_awaddr [0]),
        .m_axi_awlen            ( s_axi_awlen  [0]),
        .m_axi_awsize           ( s_axi_awsize [0]),
        .m_axi_awburst          ( s_axi_awburst[0]),
        .m_axi_awlock           ( s_axi_awlock [0]),
        .m_axi_awcache          ( s_axi_awcache[0]),
        .m_axi_awprot           ( s_axi_awprot [0]),
        .m_axi_awqos            ( s_axi_awqos  [0]),
        .m_axi_awregion         ( ),
        .m_axi_awuser           ( s_axi_awuser [0]),
        .m_axi_awvalid          ( s_axi_awvalid[0]),
        .m_axi_awready          ( s_axi_awready[0]),
        .m_axi_wdata            ( s_axi_wdata  [0]),
        .m_axi_wstrb            ( s_axi_wstrb  [0]),
        .m_axi_wlast            ( s_axi_wlast  [0]),
        .m_axi_wuser            ( s_axi_wuser  [0]),
        .m_axi_wvalid           ( s_axi_wvalid [0]),
        .m_axi_wready           ( s_axi_wready [0]),
        .m_axi_bid              ( s_axi_bid    [0]),
        .m_axi_bresp            ( s_axi_bresp  [0]),
        .m_axi_buser            ( s_axi_buser  [0]),
        .m_axi_bvalid           ( s_axi_bvalid [0]),
        .m_axi_bready           ( s_axi_bready [0]),
        .m_axi_arid             ( s_axi_arid   [0]),
        .m_axi_araddr           ( s_axi_araddr [0]),
        .m_axi_arlen            ( s_axi_arlen  [0]),
        .m_axi_arsize           ( s_axi_arsize [0]),
        .m_axi_arburst          ( s_axi_arburst[0]),
        .m_axi_arlock           ( s_axi_arlock [0]),
        .m_axi_arcache          ( s_axi_arcache[0]),
        .m_axi_arprot           ( s_axi_arprot [0]),
        .m_axi_arqos            ( s_axi_arqos  [0]),
        .m_axi_arregion         ( ),
        .m_axi_aruser           ( s_axi_aruser [0]),
        .m_axi_arvalid          ( s_axi_arvalid[0]),
        .m_axi_arready          ( s_axi_arready[0]),
        .m_axi_rid              ( s_axi_rid    [0]),
        .m_axi_rdata            ( s_axi_rdata  [0]),
        .m_axi_rresp            ( s_axi_rresp  [0]),
        .m_axi_rlast            ( s_axi_rlast  [0]),
        .m_axi_ruser            ( s_axi_ruser  [0]),
        .m_axi_rvalid           ( s_axi_rvalid [0]),
        .m_axi_rready           ( s_axi_rready [0]),
        
        /*
        * AXI slave interface
        */
        .s_axi_awid             ( m_axi_awid    [AXI_DATA_TOP_ID]),
        .s_axi_awaddr           ( m_axi_awaddr  [AXI_DATA_TOP_ID]),
        .s_axi_awlen            ( m_axi_awlen   [AXI_DATA_TOP_ID]),
        .s_axi_awsize           ( m_axi_awsize  [AXI_DATA_TOP_ID]),
        .s_axi_awburst          ( m_axi_awburst [AXI_DATA_TOP_ID]),
        .s_axi_awlock           ( m_axi_awlock  [AXI_DATA_TOP_ID]),
        .s_axi_awcache          ( m_axi_awcache [AXI_DATA_TOP_ID]),
        .s_axi_awprot           ( m_axi_awprot  [AXI_DATA_TOP_ID]),
        .s_axi_awqos            ( m_axi_awqos   [AXI_DATA_TOP_ID]),
        .s_axi_awregion         ( m_axi_awregion[AXI_DATA_TOP_ID]),
        .s_axi_awuser           ( m_axi_awuser  [AXI_DATA_TOP_ID]),
        .s_axi_awvalid          ( m_axi_awvalid [AXI_DATA_TOP_ID]),
        .s_axi_awready          ( m_axi_awready [AXI_DATA_TOP_ID]),
        .s_axi_wdata            ( m_axi_wdata   [AXI_DATA_TOP_ID]),
        .s_axi_wstrb            ( m_axi_wstrb   [AXI_DATA_TOP_ID]),
        .s_axi_wlast            ( m_axi_wlast   [AXI_DATA_TOP_ID]),
        .s_axi_wuser            ( m_axi_wuser   [AXI_DATA_TOP_ID]),
        .s_axi_wvalid           ( m_axi_wvalid  [AXI_DATA_TOP_ID]),
        .s_axi_wready           ( m_axi_wready  [AXI_DATA_TOP_ID]),
        .s_axi_bid              ( m_axi_bid     [AXI_DATA_TOP_ID]),
        .s_axi_bresp            ( m_axi_bresp   [AXI_DATA_TOP_ID]),
        .s_axi_buser            ( m_axi_buser   [AXI_DATA_TOP_ID]),
        .s_axi_bvalid           ( m_axi_bvalid  [AXI_DATA_TOP_ID]),
        .s_axi_bready           ( m_axi_bready  [AXI_DATA_TOP_ID]),
        .s_axi_arid             ( m_axi_arid    [AXI_DATA_TOP_ID]),
        .s_axi_araddr           ( m_axi_araddr  [AXI_DATA_TOP_ID]),
        .s_axi_arlen            ( m_axi_arlen   [AXI_DATA_TOP_ID]),
        .s_axi_arsize           ( m_axi_arsize  [AXI_DATA_TOP_ID]),
        .s_axi_arburst          ( m_axi_arburst [AXI_DATA_TOP_ID]),
        .s_axi_arlock           ( m_axi_arlock  [AXI_DATA_TOP_ID]),
        .s_axi_arcache          ( m_axi_arcache [AXI_DATA_TOP_ID]),
        .s_axi_arprot           ( m_axi_arprot  [AXI_DATA_TOP_ID]),
        .s_axi_arqos            ( m_axi_arqos   [AXI_DATA_TOP_ID]),
        .s_axi_arregion         ( m_axi_arregion[AXI_DATA_TOP_ID]),
        .s_axi_aruser           ( m_axi_aruser  [AXI_DATA_TOP_ID]),
        .s_axi_arvalid          ( m_axi_arvalid [AXI_DATA_TOP_ID]),
        .s_axi_arready          ( m_axi_arready [AXI_DATA_TOP_ID]),
        .s_axi_rid              ( m_axi_rid     [AXI_DATA_TOP_ID]),
        .s_axi_rdata            ( m_axi_rdata   [AXI_DATA_TOP_ID]),
        .s_axi_rresp            ( m_axi_rresp   [AXI_DATA_TOP_ID]),
        .s_axi_rlast            ( m_axi_rlast   [AXI_DATA_TOP_ID]),
        .s_axi_ruser            ( m_axi_ruser   [AXI_DATA_TOP_ID]),
        .s_axi_rvalid           ( m_axi_rvalid  [AXI_DATA_TOP_ID]),
        .s_axi_rready           ( m_axi_rready  [AXI_DATA_TOP_ID])
    );
    
    soc_peripherals_top_v2 #(
        .AXI_ID_WIDTH           ( AXI_S_ID_WIDTH            ),
        .AXI_ADDR_WIDTH         ( AXI_ADDR_WIDTH            ),
        .AXI_USER_WIDTH         ( AXI_USER_WIDTH            ),
        .AXI_S_DATA_WIDTH       ( AXI_DATA_WIDTH            ),
        .AXI_S_STRB_WIDTH       ( AXI_STRB_WIDTH            ),
       
        .AXIL_ADDR_WIDTH        ( AXIL_ADDR_WIDTH           ),
        .AXIL_DATA_WIDTH        ( AXIL_DATA_WIDTH           ),
        .AXIL_STRB_WIDTH        ( AXIL_STRB_WIDTH           )
    ) PERIPHERAL_TOP (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .peripheral_uart_tx_o   ( peripheral_uart_tx_o      ),
        .peripheral_uart_rx_i   ( peripheral_uart_rx_i      ),
        
        // QSPI Interface
        .qspi_sclk_o            ( peripheral_qspi_sclk_o    ),
        .qspi_cs_no             ( peripheral_qspi_cs_no     ),
        .qspi_data_o            ( peripheral_qspi_data_o    ),
        .qspi_data_i            ( peripheral_qspi_data_i    ),
        .qspi_data_oen          ( peripheral_qspi_data_oen  ),
        
        /*
        * AXI slave interface
        */
        .s_axi_awid             ( m_axi_awid    [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awaddr           ( m_axi_awaddr  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awlen            ( m_axi_awlen   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awsize           ( m_axi_awsize  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awburst          ( m_axi_awburst [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awlock           ( m_axi_awlock  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awcache          ( m_axi_awcache [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awprot           ( m_axi_awprot  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awqos            ( m_axi_awqos   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awregion         ( m_axi_awregion[AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awuser           ( m_axi_awuser  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awvalid          ( m_axi_awvalid [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_awready          ( m_axi_awready [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_wdata            ( m_axi_wdata   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_wstrb            ( m_axi_wstrb   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_wlast            ( m_axi_wlast   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_wuser            ( m_axi_wuser   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_wvalid           ( m_axi_wvalid  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_wready           ( m_axi_wready  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_bid              ( m_axi_bid     [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_bresp            ( m_axi_bresp   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_buser            ( m_axi_buser   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_bvalid           ( m_axi_bvalid  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_bready           ( m_axi_bready  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arid             ( m_axi_arid    [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_araddr           ( m_axi_araddr  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arlen            ( m_axi_arlen   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arsize           ( m_axi_arsize  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arburst          ( m_axi_arburst [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arlock           ( m_axi_arlock  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arcache          ( m_axi_arcache [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arprot           ( m_axi_arprot  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arqos            ( m_axi_arqos   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arregion         ( m_axi_arregion[AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_aruser           ( m_axi_aruser  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arvalid          ( m_axi_arvalid [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_arready          ( m_axi_arready [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_rid              ( m_axi_rid     [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_rdata            ( m_axi_rdata   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_rresp            ( m_axi_rresp   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_rlast            ( m_axi_rlast   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_ruser            ( m_axi_ruser   [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_rvalid           ( m_axi_rvalid  [AXI_PERIPHERAL_TOP_ID] ),
        .s_axi_rready           ( m_axi_rready  [AXI_PERIPHERAL_TOP_ID] )
    );
    
    axi_crossbar_wrap #(
        // Number of AXI inputs (slave interfaces)
        .S_COUNT                ( AXI_MASTER_COUNT              ),
        // Number of AXI outputs (master interfaces)
        .M_COUNT                ( AXI_SLAVE_COUNT               ),
        // Width of data bus in bits
        .DATA_WIDTH             ( AXI_ADDR_WIDTH                ),
        // Width of address bus in bits
        .ADDR_WIDTH             ( AXI_DATA_WIDTH                ),
        // Input ID field width ( from AXI masters)
        .S_ID_WIDTH             ( AXI_M_ID_WIDTH                ),
        // Number of concurrent operations for each slave interface
        // S_COUNT concatenated fields of 32 bits
        .S_ACCEPT               ( {AXI_MASTER_COUNT{32'd16}}    ),
        // Number of regions per master interface
        .M_REGIONS              ( 1                             ),
        // Master interface base addresses
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of ADDR_WIDTH bits
        // set to zero for default addressing based on M_ADDR_WIDTH
        .M_BASE_ADDR            ( 0                             ),
        // Master interface address widths
        // M_COUNT concatenated fields of M_REGIONS concatenated fields of 32 bits
        .M_ADDR_WIDTH           ( {AXI_SLAVE_COUNT{{1{32'd28}}}})
    ) SYSTEM_BUS (
        .clk(clk_i), .rst(~reset_ni),
        
        /*
         * AXI slave interfaces
         */
        .s_axi_awid             ( s_axi_awid       ),
        .s_axi_awaddr           ( s_axi_awaddr     ),
        .s_axi_awlen            ( s_axi_awlen      ),
        .s_axi_awsize           ( s_axi_awsize     ),
        .s_axi_awburst          ( s_axi_awburst    ),
        .s_axi_awlock           ( s_axi_awlock     ),
        .s_axi_awcache          ( s_axi_awcache    ),
        .s_axi_awprot           ( s_axi_awprot     ),
        .s_axi_awqos            ( s_axi_awqos      ),
        .s_axi_awuser           ( s_axi_awuser     ),
        .s_axi_awvalid          ( s_axi_awvalid    ),
        .s_axi_awready          ( s_axi_awready    ),
        .s_axi_wdata            ( s_axi_wdata      ),
        .s_axi_wstrb            ( s_axi_wstrb      ),
        .s_axi_wlast            ( s_axi_wlast      ),
        .s_axi_wuser            ( s_axi_wuser      ),
        .s_axi_wvalid           ( s_axi_wvalid     ),
        .s_axi_wready           ( s_axi_wready     ),
        .s_axi_bid              ( s_axi_bid        ),
        .s_axi_bresp            ( s_axi_bresp      ),
        .s_axi_buser            ( s_axi_buser      ),
        .s_axi_bvalid           ( s_axi_bvalid     ),
        .s_axi_bready           ( s_axi_bready     ),
        .s_axi_arid             ( s_axi_arid       ),
        .s_axi_araddr           ( s_axi_araddr     ),
        .s_axi_arlen            ( s_axi_arlen      ),
        .s_axi_arsize           ( s_axi_arsize     ),
        .s_axi_arburst          ( s_axi_arburst    ),
        .s_axi_arlock           ( s_axi_arlock     ),
        .s_axi_arcache          ( s_axi_arcache    ),
        .s_axi_arprot           ( s_axi_arprot     ),
        .s_axi_arqos            ( s_axi_arqos      ),
        .s_axi_aruser           ( s_axi_aruser     ),
        .s_axi_arvalid          ( s_axi_arvalid    ),
        .s_axi_arready          ( s_axi_arready    ),
        .s_axi_rid              ( s_axi_rid        ),
        .s_axi_rdata            ( s_axi_rdata      ),
        .s_axi_rresp            ( s_axi_rresp      ),
        .s_axi_rlast            ( s_axi_rlast      ),
        .s_axi_ruser            ( s_axi_ruser      ),
        .s_axi_rvalid           ( s_axi_rvalid     ),
        .s_axi_rready           ( s_axi_rready     ),
    
        /*
         * AXI master interfaces
         */
        .m_axi_awid             ( m_axi_awid       ),
        .m_axi_awaddr           ( m_axi_awaddr     ),
        .m_axi_awlen            ( m_axi_awlen      ),
        .m_axi_awsize           ( m_axi_awsize     ),
        .m_axi_awburst          ( m_axi_awburst    ),
        .m_axi_awlock           ( m_axi_awlock     ),
        .m_axi_awcache          ( m_axi_awcache    ),
        .m_axi_awprot           ( m_axi_awprot     ),
        .m_axi_awqos            ( m_axi_awqos      ),
        .m_axi_awregion         ( m_axi_awregion   ),
        .m_axi_awuser           ( m_axi_awuser     ),
        .m_axi_awvalid          ( m_axi_awvalid    ),
        .m_axi_awready          ( m_axi_awready    ),
        .m_axi_wdata            ( m_axi_wdata      ),
        .m_axi_wstrb            ( m_axi_wstrb      ),
        .m_axi_wlast            ( m_axi_wlast      ),
        .m_axi_wuser            ( m_axi_wuser      ),
        .m_axi_wvalid           ( m_axi_wvalid     ),
        .m_axi_wready           ( m_axi_wready     ),
        .m_axi_bid              ( m_axi_bid        ),
        .m_axi_bresp            ( m_axi_bresp      ),
        .m_axi_buser            ( m_axi_buser      ),
        .m_axi_bvalid           ( m_axi_bvalid     ),
        .m_axi_bready           ( m_axi_bready     ),
        .m_axi_arid             ( m_axi_arid       ),
        .m_axi_araddr           ( m_axi_araddr     ),
        .m_axi_arlen            ( m_axi_arlen      ),
        .m_axi_arsize           ( m_axi_arsize     ),
        .m_axi_arburst          ( m_axi_arburst    ),
        .m_axi_arlock           ( m_axi_arlock     ),
        .m_axi_arcache          ( m_axi_arcache    ),
        .m_axi_arprot           ( m_axi_arprot     ),
        .m_axi_arqos            ( m_axi_arqos      ),
        .m_axi_arregion         ( m_axi_arregion   ),
        .m_axi_aruser           ( m_axi_aruser     ),
        .m_axi_arvalid          ( m_axi_arvalid    ),
        .m_axi_arready          ( m_axi_arready    ),
        .m_axi_rid              ( m_axi_rid        ),
        .m_axi_rdata            ( m_axi_rdata      ),
        .m_axi_rresp            ( m_axi_rresp      ),
        .m_axi_rlast            ( m_axi_rlast      ),
        .m_axi_ruser            ( m_axi_ruser      ),
        .m_axi_rvalid           ( m_axi_rvalid     ),
        .m_axi_rready           ( m_axi_rready      )
    );
    
endmodule



















