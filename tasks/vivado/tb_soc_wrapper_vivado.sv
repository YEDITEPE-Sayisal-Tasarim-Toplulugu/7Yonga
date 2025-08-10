`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10.08.2025 13:13:41
// Design Name: 
// Module Name: tb_soc_wrapper_vivado
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

module tb_soc_wrapper_vivado();

    `SIM_CLK_RST(10, 5, 500_000)
    
    logic uart0_rx, uart0_tx;
    
    soc_wrapper_vivado DUT
    (
        .clk            ( `CLK          ),
        .resetn         ( `RST          ),
        .rx             ( uart0_rx      ),
        .tx             ( uart0_tx      )
    );
    
    assign uart0_rx = 1'b1;
    
endmodule















