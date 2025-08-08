`timescale 1ns / 1ps

module tb_verilator ();

    localparam integer T=10;
    localparam integer RESET_CYCLE=2;
    localparam integer PROGRAM_CYCLE=100;

    SOC_PERIPHERAL_INF PERIPHERAL_INTF();

    logic clk, reset;
    logic tx, rx;

    soc_top SOC
    (
        .clk_i              ( clk               ),
        .reset_i            ( reset             ),
        
        .PERIPHERAL_INTF    ( PERIPHERAL_INTF   )
    );

    always #(T/2) clk=~clk;
    initial begin
        clk=1'b0;
        reset=1'b1;
        repeat (RESET_CYCLE) @(posedge clk);
        reset=1'b0;
        repeat (PROGRAM_CYCLE-RESET_CYCLE) @(posedge clk);
        $display("[SIM] done.");
        $finish;
    end

    assign PERIPHERAL_INTF.UART0_rx = rx;
    assign tx = PERIPHERAL_INTF.UART0_tx;
    
endmodule