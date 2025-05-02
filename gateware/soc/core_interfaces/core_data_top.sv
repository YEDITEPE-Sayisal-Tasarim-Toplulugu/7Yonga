`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.04.2025 11:31:22
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


module core_data_top
    #(parameter
            DATA_MEM_SIZE_IN_KB = 8
    )
    (
        input logic clk_i, reset_i,
        
        CV32E_DATA_INF.SLAVE data_inf_i
    );
    
    CV32E_DATA_INF.SLAVE SRAM_data_inf_w;
    CV32E_DATA_INF.SLAVE DECODER_port1_inf_w;
    CV32E_DATA_INF.SLAVE DECODER_port2_inf_w;
    CV32E_DATA_INF.MASTER AXI4_ADAP_inf_w;
    
    interface_arbiter
    #(
        .IN_COUNT(2)
    )
    INTERFACE_ARBITER
    (
        .clk_i(clk_i), .reset_i(reset_i),
        
        .valid_list_i(INSTRUCTION_intereface_arbiter_valid_list_w),
        .sel_o(INSTRUCTION_intereface_arbiter_sel_w)
    );
    
    data_memory
    #(
        .SIZE_IN_KB(DATA_MEM_SIZE_IN_KB)
    )
    DATA_MEMORY
    (
        .clk_i(clk_i),
        .cv32_data_inf(SRAM_data_inf_w)
    );
    
endmodule






















