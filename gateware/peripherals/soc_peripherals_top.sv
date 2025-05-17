`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 16.05.2025 21:10:25
// Design Name: 
// Module Name: soc_peripherals_top
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
`include "soc_interface_list.svh"

import soc_addr_rules_pkg::*;
import soc_config_pkg::*;
import axi_pkg::*;

module soc_peripherals_top
    #(
        parameter int unsigned AXI_ADDR_WIDTH     = 32'd32,
        parameter int unsigned AXI_DATA_WIDTH     = 32'd32,
        parameter int unsigned AXI_ID_WIDTH       = 32'd8,
        parameter int unsigned AXI_USER_WIDTH     = 32'd8,
        parameter int unsigned AXI_STRB_WIDTH     = (AXI_DATA_WIDTH/8)
    )
    (
        input logic clk_i, reset_i,
        
        input logic UART0_rx_i,
        output logic UART0_tx_o,
        
        AXI_BUS.Slave              AXI4_slave
    );
    
    typedef logic [AXI_ADDR_WIDTH-1:0]      addr_t;
    typedef axi_pkg::xbar_rule_32_t         rule_t; // Has to be the same width as axi addr
    typedef logic [AXI_DATA_WIDTH-1:0]      data_t;
    typedef logic [AXI_STRB_WIDTH-1:0]      strb_t;
    
    localparam int unsigned PERIPHERAL_BUS_MASTER_COUNT     = 32'd1;
    localparam int unsigned PERIPHERAL_BUS_SLAVE_COUNT      = 32'd1;
    
    localparam int unsigned AXI4L_SLAVE_UART_ID             = 32'd0;
    
    localparam rule_t [PERIPHERAL_BUS_SLAVE_COUNT-1:0] AXI4L_AddrMap = '{
        // AXIL_UART_ADDR_RULE
        '{
            idx:        AXI4L_SLAVE_UART_ID,
            start_addr: soc_addr_rules_pkg::AXIL_UART_ADDR_RULE.start_addr,
            end_addr:   soc_addr_rules_pkg::AXIL_UART_ADDR_RULE.end_addr
        }
    };
    
    AXI_LITE#(
        .AXI_ADDR_WIDTH (   AXI_ADDR_WIDTH    ),
        .AXI_DATA_WIDTH (   AXI_DATA_WIDTH    )
    ) AXI4L_Slaves[PERIPHERAL_BUS_MASTER_COUNT]();
    
    AXI_LITE#(
        .AXI_ADDR_WIDTH (   AXI_ADDR_WIDTH    ),
        .AXI_DATA_WIDTH (   AXI_DATA_WIDTH    )
    ) AXI4L_Masters[PERIPHERAL_BUS_SLAVE_COUNT]();
    
    uart
    PERIPHERAL_UART 
    (
        // Clock and reset signals
        .s_axi_aclk(clk_i),
        .s_axi_aresetn(~reset_i),
        
        // AXI4-Lite Slave Arayüzü
        // Write Address Channel
        .s_axi_awaddr   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].aw_addr  ),
        .s_axi_awvalid  (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].aw_valid ),
        .s_axi_awready  (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].aw_ready ),
        
        // Write Data Channel
        .s_axi_wdata    (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].w_data   ),
        .s_axi_wstrb    (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].w_strb   ),
        .s_axi_wvalid   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].w_valid  ),
        .s_axi_wready   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].w_ready  ),
        
        // Write Response Channel
        .s_axi_bresp    (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].b_resp   ),
        .s_axi_bvalid   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].b_valid  ),
        .s_axi_bready   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].b_ready  ),
        
        // Read Address Channel
        .s_axi_araddr   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].ar_addr  ),
        .s_axi_arvalid  (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].ar_valid ),
        .s_axi_arready  (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].ar_ready ),
        
        // Read Data Channel
        .s_axi_rdata    (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].r_data   ),
        .s_axi_rresp    (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].r_resp   ),
        .s_axi_rvalid   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].r_valid  ),
        .s_axi_rready   (AXI4L_Slaves[AXI4L_SLAVE_UART_ID].r_ready  ),
        
        // UART pins
        .uart_rx        (UART0_rx_i),
        .uart_tx        (UART0_tx_o)
    );
    
    /// Configuration for `axi_xbar`.
    localparam axi_pkg::xbar_cfg_t SOC_PeripheralBus_xbar_cfg = '{
        /// Number of slave ports of the crossbar.
        /// This many master modules are connected to it.
        // int unsigned   NoSlvPorts;
        NoSlvPorts:         PERIPHERAL_BUS_MASTER_COUNT,
        /// Number of master ports of the crossbar.
        /// This many slave modules are connected to it.
        // int unsigned   NoMstPorts;
        NoMstPorts:         PERIPHERAL_BUS_SLAVE_COUNT,
        /// Maximum number of open transactions each master connected to the crossbar can have in
        /// flight at the same time.
        // int unsigned   MaxMstTrans;
        MaxMstTrans:        PERIPHERAL_BUS_SLAVE_COUNT,
        /// Maximum number of open transactions each slave connected to the crossbar can have in
        /// flight at the same time.
        // int unsigned   MaxSlvTrans;
        MaxSlvTrans:        PERIPHERAL_BUS_MASTER_COUNT,
        /// Determine if the internal FIFOs of the crossbar are instantiated in fallthrough mode.
        /// 0: No fallthrough
        /// 1: Fallthrough
        // bit            FallThrough;
        FallThrough:        1'b0,
        /// The Latency mode of the xbar. This determines if the channels on the ports have
        /// a spill register instantiated.
        /// Example configurations are provided with the enum `xbar_latency_e`.
        // bit [9:0]      LatencyMode;
        LatencyMode:        axi_pkg::CUT_ALL_AX,
        /// AXI4+ATOP address field width.
        // int unsigned   AxiAddrWidth;
        AxiAddrWidth:       soc_config_pkg::AXI4L_CONF_ADDR_WIDTH,
        /// AXI4+ATOP data field width.
        // int unsigned   AxiDataWidth;
        AxiDataWidth:       soc_config_pkg::AXI4L_CONF_DATA_WIDTH,
        /// The number of address rules defined for routing of the transactions.
        /// Each master port can have multiple rules, should have however at least one.
        /// If a transaction can not be routed the xbar will answer with an `axi_pkg::RESP_DECERR`.
        // int unsigned   NoAddrRules;
        NoAddrRules:        PERIPHERAL_BUS_SLAVE_COUNT,
        default:            '0
    };
    
    axi_to_axi_lite_intf #(
        /// AXI bus parameters
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH  ),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        /// Maximum number of outstanding writes.
        .AXI_MAX_WRITE_TXNS (32'd1),
        /// Maximum number of outstanding reads.
        .AXI_MAX_READ_TXNS  (32'd1),
        .FALL_THROUGH       (1'b1),
        .FULL_BW            (0)
    ) AXI4_TO_AXI4LITE_ADAPTER (
        .clk_i          (clk_i),
        .rst_ni         (~reset_i),
        .testmode_i     (1'b0),
        
        .slv            (AXI4_slave),
        .mst            (AXI4L_Masters[0])
    );
    
    axi_lite_xbar_intf #(
        .Cfg(SOC_PeripheralBus_xbar_cfg)
    ) PERIPHERAL_BUS (
        .clk_i          (clk_i),
        .rst_ni         (~reset_i),
        .test_i         (1'b0),
        
        .slv_ports(AXI4L_Masters),
        .mst_ports(AXI4L_Slaves),
        
        .addr_map_i(AXI4L_AddrMap),
        
        .en_default_mst_port_i  ('0),
        .default_mst_port_i     ('0)
    );
    
endmodule













