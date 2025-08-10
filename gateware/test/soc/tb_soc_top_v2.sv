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

    `SIM_CLK_RST(10, 5, 5000000)
    
    logic uart0_tx, uart0_rx;
    
    soc_top DUT
    (
        .clk_i(`CLK), .reset_ni(`RST),
        
        .peripheral_uart_tx_o       ( uart0_tx      ),
        .peripheral_uart_rx_i       ( uart0_rx      )
    );
    
    assign uart0_rx = 1'b1;
    
    uart_monitor #(
        .CLK_FREQ_HZ    ( 1_000_000*100 ),
        .BAUD_RATE      ( 9600          )
    ) UART_MONITOR (
        .clk            ( `CLK          ),
        .rst_n          ( `RST          ),
        .uart_line      ( uart0_tx      )
    );    

endmodule











