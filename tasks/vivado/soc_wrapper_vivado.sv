`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10.08.2025 13:06:05
// Design Name: 
// Module Name: soc_wrapper_vivado
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


module soc_wrapper_vivado
    (
        input wire clk,
        input wire resetn,
        input wire rx,
        output wire tx
    );
    
    logic clk_gen_w;
    
    clk_gen CLOCK_GENERATOR
    (
        // Clock out ports
        .clk_o                  ( clk_gen_w     ),     // output clk_o
        // Clock in ports
        .clk_i                  ( clk           )      // input clk_i
    );
    
    soc_top SOC (
        .clk_i                  ( clk_gen_w     ),
        .reset_ni               ( resetn        ),
        
        .peripheral_uart_tx_o   ( tx            ), 
        .peripheral_uart_rx_i   ( rx            )
    );
    
endmodule

















