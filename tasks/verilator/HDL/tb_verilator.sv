`timescale 1ns / 1ps

module tb_verilator ();

    localparam integer T=10;
    localparam integer RESET_CYCLE=2;
    localparam integer PROGRAM_CYCLE=100;

    SOC_PERIPHERAL_INF PERIPHERAL_INTF();

    logic clk, resetn;
    logic tx, rx;

    soc_top SOC
    (
        .clk_i                      ( clk                   ),
        .reset_ni                   ( resetn                ),
        
        // UART Interface
        .peripheral_uart_tx_o       ( ), 
        .peripheral_uart_rx_i       ( 1),

        // QSPI Interface
        .peripheral_qspi_sclk_o     ( ),
        .peripheral_qspi_cs_no      ( ),
        .peripheral_qspi_data_o     ( ),
        .peripheral_qspi_data_i     ( 0),
        .peripheral_qspi_data_oen   ( )
    );

    always #(T/2) clk=~clk;
    initial begin
        clk=1'b0;
        resetn=1'b0;
        repeat (RESET_CYCLE) @(posedge clk);
        resetn=1'b1;
        repeat (PROGRAM_CYCLE-RESET_CYCLE) @(posedge clk);
        $display("[SIM] done.");
        $finish;
    end

    assign PERIPHERAL_INTF.UART0_rx = rx;
    assign tx = PERIPHERAL_INTF.UART0_tx;
    
endmodule