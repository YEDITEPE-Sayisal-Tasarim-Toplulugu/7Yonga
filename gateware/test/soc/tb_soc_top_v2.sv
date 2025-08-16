`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 22:14:29
// Design Name: 
// Module Name: tb_soc_top_v2
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

`include "tb_common.svh"

module tb_soc_top_v2();

    `SIM_CLK_RST(20, 5, 500)
    
    logic uart0_tx, uart0_rx;
    
    logic       qspi_sclk_w;
    logic       qspi_cs_nw;
    logic [3:0] qspi_do_w;
    logic [3:0] qspi_di_w;
    logic       qspi_data_oen;
    
    soc_top DUT
    (
        .clk_i(`CLK), .reset_ni(`RST),
        
        .peripheral_uart_tx_o       ( uart0_tx      ),
        .peripheral_uart_rx_i       ( uart0_rx      ),
        
        .peripheral_qspi_sclk_o     ( qspi_sclk_w   ),
        .peripheral_qspi_cs_no      ( qspi_cs_nw    ),
        .peripheral_qspi_data_o     ( qspi_do_w     ),
        .peripheral_qspi_data_i     ( qspi_di_w     ),
        .peripheral_qspi_data_oen   ( qspi_data_oen )   // Output enable (0: output, 1: input)
    );
    
    assign uart0_rx = 1'b1;
    
    uart_monitor #(
        .CLK_FREQ_HZ                ( 1_000_000*50  ),
        .BAUD_RATE                  ( 9600          )
    ) UART_MONITOR (
        .clk                        ( `CLK          ),
        .rst_n                      ( `RST          ),
        .uart_line                  ( uart0_tx      )
    );
    
    // QSPI interface + monitor
    qspi_if qif (
        .clk(`CLK), .rst_n(`RST),
        .peripheral_qspi_sclk_o     ( qspi_sclk_w   ),
        .peripheral_qspi_cs_no      ( qspi_cs_nw    ),
        .peripheral_qspi_data_o     ( qspi_do_w     ),
        .peripheral_qspi_data_i     ( qspi_di_w     ),
        .peripheral_qspi_data_oen   ( qspi_data_oen )
    );

    // Mode0 izleme, ayrıntılı log=1
    qspi_monitor #(.CPOL(1'b0), .CPHA(1'b0), .LOG_LEVEL(1)) mon (.bus(qif));
    
endmodule











