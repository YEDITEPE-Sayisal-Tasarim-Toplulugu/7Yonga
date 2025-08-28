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

    `SIM_CLK_RST(10, 5, 500_000_000)
    
    localparam FREQ_HZ                     = 1_000_000 * 50;
    localparam PROGRAMMER_BAUDE_RATE       = 9600;
    
    localparam PROGRAMMER_CPB_DATA          = FREQ_HZ/PROGRAMMER_BAUDE_RATE;
    
    logic uart0_rx, uart0_tx;
    logic clk_w;
    
    logic programmer_mode;
    
    integer program_counter;
    integer program_length;
    
    logic TEST_data_tx_start_i;
    logic [7:0] TEST_uart_tx_data_i;
    logic TEST_data_sent_o;
    
    soc_wrapper_vivado 
    #(
        .CLOCK_GENERATER_ENABLE ( 0                 ),
        .QSPI_HARDWARED_TO_0    ( 1                 )
    )DUT (
        .clk                    ( `CLK              ),
        .resetn                 ( `RST              ),
        .rx                     ( uart0_rx          ),
        .tx                     ( uart0_tx          ),
        
        .qspi_sclk_out          ( ),
        .qspi_cs_n_out          ( ),
        .qspi_data              ( ),
        .programmer_mode        ( programmer_mode   )
    );
    
    uart_monitor #(
        .CLK_FREQ_HZ        ( 1_000_000*50  ),
        .BAUD_RATE          ( 9600          )
    ) UART_MONITOR (
        .clk                ( `CLK         ),
        .rst_n              ( `RST          ),
        .uart_line          ( uart0_tx      )
    );
    
    uart_engine TRANSMITER_UART (
        // Clock and reset signals
        .aclk                       ( `CLK                     ),
        .aresetn                    ( `RST                      ),
    
        .uart_cpb_reg               ( PROGRAMMER_CPB_DATA       ),  // Clock-per-bit register
        .uart_stp_reg               ( 0                         ),  // Stop-bit register
    
        .data_tx_start_i            ( TEST_data_tx_start_i      ),
        .uart_tx_data_i             ( TEST_uart_tx_data_i       ),  // Transmit data
        .data_sent_o                ( TEST_data_sent_o          ),
    
        .rx_received_o              (                           ),
        .rx_received_data_o         (                           ),
    
        // UART pins
        .uart_rx                    ( 1'b1                      ),
        .uart_tx                    ( uart0_rx                  )
    );
    
    localparam PROGRAM_DEPTH = 0;
    logic [31:0] program_data [0:PROGRAM_DEPTH-1];
    logic [7:0] test_program [$];
    
    initial begin
        $readmemh("C:/Users/mhfur/Desktop/github_cloneS/7Yonga/firmware/program1_basic/BUILD/program.mem", program_data);
        for (integer i=0; i<PROGRAM_DEPTH; i++) begin
            for (integer j=0; j<4; j++) begin
                test_program.push_back(program_data[i][j*8+:8]);
            end
        end
    end
    
    always begin
        #(1ps);
        if (programmer_mode) begin
            TEST_data_tx_start_i = 1'b1;
            TEST_uart_tx_data_i = test_program[program_counter];
            wait (TEST_data_sent_o == 1'b1);
            @(posedge `CLK);
            #(1ps);
            program_counter++;
        end
    end
    
    initial begin
        TEST_data_tx_start_i = 1'b0;
        
        program_length = test_program.size();
        program_counter=0;
        
        programmer_mode = 1;
        
        $display("[SIM] waiting for transmit...");
        wait (program_counter == program_length);
        $display("[SIM] transmit done.");
        
        `RST = 0;
        programmer_mode = 0;
        TEST_data_tx_start_i = 1'b0;
        @(posedge `CLK);
        `RST = 1;
        
        repeat (50000000) @(posedge `CLK);
        
        $display("[SIM] done.");
        $finish;
    end
    
endmodule















