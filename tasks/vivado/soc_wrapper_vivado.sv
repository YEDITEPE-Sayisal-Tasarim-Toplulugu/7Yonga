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
    #(parameter 
            CLOCK_GENERATER_ENABLE = 1
    )
    (
        input wire clk,
        input wire resetn,
        input wire rx,
        output wire tx,
        output wire qspi_sclk_out,
        output wire qspi_cs_n_out,
        inout wire [3:0] qspi_data,
        input wire programmer_mode
        //, output wire clk_o
    );
    
    logic reset_ni;
    logic clk_gen_w;
    logic core_rx, programmer_rx;

generate
    if (CLOCK_GENERATER_ENABLE) begin : CLOCK_GEN
        clk_gen CLOCK_GENERATOR
        (
            // Clock out ports
            .clk_o                      ( clk_gen_w     ),     // output clk_o
            // Clock in ports
            .clk_i                      ( clk           )      // input clk_i
        );
    end else begin : CLOCK_BYPASS
        assign clk_gen_w = clk;
    end
endgenerate
    
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) logic [3:0] qspi_do_w;
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) logic [3:0] qspi_di_w;
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) logic [3:0] qspi_data_oen;
    
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) wire qspi_sclk;
    (* DONT_TOUCH="TRUE", MARK_DEBUG="TRUE" *) wire qspi_cs_n;

    assign clk_o            = clk_gen_w;
    
    assign qspi_sclk_out    = qspi_sclk;
    assign qspi_cs_n_out    = qspi_cs_n;
    
    assign core_rx          = (programmer_mode) ? 1'b1 : rx;
    assign programmer_rx    = (programmer_mode) ? rx : 1'b1;
    
    assign reset_ni = (~programmer_mode) & resetn;
    
    soc_top SOC (
        .clk_i                      ( clk_gen_w         ),
        .reset_ni                   ( reset_ni          ),
        
        // UART Programmmer
        .programmer_reset_ni        ( resetn            ),
        .programmer_enable_i        ( programmer_mode   ),
        .programmer_rx              ( programmer_rx     ),
        
        .peripheral_uart_tx_o       ( tx                ), 
        .peripheral_uart_rx_i       ( core_rx           ),
        
        // QSPI Interface
        .peripheral_qspi_sclk_o     ( qspi_sclk         ),
        .peripheral_qspi_cs_no      ( qspi_cs_n         ),
        .peripheral_qspi_data_o     ( qspi_do_w         ),
        .peripheral_qspi_data_i     ( qspi_di_w         ),
        .peripheral_qspi_data_oen   ( qspi_data_oen     )
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

















