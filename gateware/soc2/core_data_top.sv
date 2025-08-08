`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07.08.2025 20:22:24
// Design Name: 
// Module Name: core_data_top
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
`include "soc_interface_list.svh"
`include "soc_addr_rules.svh"

module core_data_top
    (
        input logic clk_i, reset_i,
        
        CORE_DATA_INF.Slave     CORE_data_inf_i,
        
        AXI_BUS.Master          axi_master,
        AXI_BUS.Slave           axi_slv
    );
    
    CORE_DATA_INF SRAM_data_inf_w();
    CORE_DATA_INF DECODER_port1_inf_w();
    CORE_DATA_INF DECODER_port2_inf_w();
    CORE_DATA_INF AXI4_ADAP_inf_w();
    
    
    
endmodule


















