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
        output wire tx,
        output wire qspi_sclk_out,
        output wire qspi_cs_n_out,
        inout wire [3:0] qspi_data
    );
    
    logic clk_gen_w;
    
    clk_gen CLOCK_GENERATOR
    (
        // Clock out ports
        .clk_o                      ( clk_gen_w     ),     // output clk_o
        // Clock in ports
        .clk_i                      ( clk           )      // input clk_i
    );
    
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) logic [3:0] qspi_do_w;
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) logic [3:0] qspi_di_w;
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) logic [3:0] qspi_data_oen;
    
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) wire qspi_sclk;
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) wire qspi_cs_n;

    
    assign qspi_sclk_out = qspi_sclk;
    assign qspi_cs_n_out = qspi_cs_n;
    
    soc_top SOC (
        .clk_i                      ( clk_gen_w     ),
        .reset_ni                   ( resetn        ),
        
        .peripheral_uart_tx_o       ( tx            ), 
        .peripheral_uart_rx_i       ( rx            ),
        
        // QSPI Interface
        .peripheral_qspi_sclk_o     ( qspi_sclk     ),
        .peripheral_qspi_cs_no      ( qspi_cs_n     ),
        .peripheral_qspi_data_o     ( qspi_do_w     ),
        .peripheral_qspi_data_i     ( qspi_di_w     ),
        .peripheral_qspi_data_oen   ( qspi_data_oen )
    );
    
    generate
        for (genvar k=0; k<4; k++) begin : IOBUFF
            vivado_iobuf VIVADO_IOBUFF (
                .I      ( qspi_do_w[k]      ),
                .T      ( qspi_data_oen[k]  ), // 3-state enable input, high=input, low=output
                .O      ( qspi_di_w[k]      ),
                .IO     ( qspi_data[k]      )
            );
        end
    endgenerate
    
endmodule

















