`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.07.2025 12:24:04
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
        input clk, resetn, rx,
        output tx
    );
    
    SOC_PERIPHERAL_INF PERIPHERAL_INTF();
    
    logic clk_cpu, reset;
    
    clk_wiz CLOCK_GENERATOR
    (
        // Clock out ports
        .clk_o(clk_cpu),     // output clk_o
        // Clock in ports
        .clk_i(clk)      // input clk_i
    );
    
    soc_top SOC
    (
        .clk_i(clk_cpu),
        .reset_i(reset),
        
        .PERIPHERAL_INTF(PERIPHERAL_INTF)
    );
    
    assign reset = ~resetn;
    
    assign PERIPHERAL_INTF.UART0_rx = rx;
    assign tx = PERIPHERAL_INTF.UART0_tx;
    
endmodule















