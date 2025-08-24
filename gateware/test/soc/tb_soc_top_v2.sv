`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 22:14:29
// Design Name: 
// Module Name: tb_soc_top_v2
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

module tb_soc_top_v2();

    `SIM_CLK_RST(20, 5, 500)
    
    localparam FREQ_HZ                     = 1_000_000 * 50;
    localparam PROGRAMMER_BAUDE_RATE       = 9600;
    
    localparam PROGRAMMER_CPB_DATA          = FREQ_HZ/PROGRAMMER_BAUDE_RATE;
    
    logic programmer_mode;
    
    logic uart0_tx, uart0_rx;
    
    logic       qspi_sclk_w;
    logic       qspi_cs_nw;
    logic [3:0] qspi_do_w;
    logic [3:0] qspi_di_w;
    logic       qspi_data_oen;
    
    logic TEST_data_tx_start_i;
    logic [7:0] TEST_uart_tx_data_i;
    logic TEST_data_sent_o;
    
    assign core_rx          = (programmer_mode) ? 1'b1 : uart0_rx;
    assign programmer_rx    = (programmer_mode) ? uart0_rx : 1'b1;
    assign reset_ni = (~programmer_mode) & `RST;
    
    soc_top DUT
    (
        .clk_i(`CLK), .reset_ni(reset_ni),
        
        .programmer_reset_ni        ( `RST          ),
        .programmer_enable_i        ( programmer_mode   ),
        .programmer_rx              ( programmer_rx ),
        
        .peripheral_uart_tx_o       ( uart0_tx      ),
        .peripheral_uart_rx_i       ( core_rx       ),
        
        .peripheral_qspi_sclk_o     ( qspi_sclk_w   ),
        .peripheral_qspi_cs_no      ( qspi_cs_nw    ),
        .peripheral_qspi_data_o     ( qspi_do_w     ),
        .peripheral_qspi_data_i     ( qspi_di_w     ),
        .peripheral_qspi_data_oen   ( qspi_data_oen )   // Output enable (0: output, 1: input)
    );
    
    uart_engine TRANSMITER_UART (
        // Clock and reset signals
        .aclk                       ( `CLK                      ),
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
    
    assign qspi_di_w = 0;
    
    uart_monitor #(
        .CLK_FREQ_HZ                ( 1_000_000*50  ),
        .BAUD_RATE                  ( 9600          )
    ) UART_MONITOR (
        .clk                        ( `CLK          ),
        .rst_n                      ( `RST          ),
        .uart_line                  ( uart0_tx      )
    );
    
    // QSPI interface + monitor
    qspi_if qif (
        .clk(`CLK), .rst_n(`RST),
        .peripheral_qspi_sclk_o     ( qspi_sclk_w   ),
        .peripheral_qspi_cs_no      ( qspi_cs_nw    ),
        .peripheral_qspi_data_o     ( qspi_do_w     ),
        .peripheral_qspi_data_i     ( qspi_di_w     ),
        .peripheral_qspi_data_oen   ( qspi_data_oen )
    );

    // Mode0 izleme, ayrıntılı log=1
    // qspi_monitor #(.CPOL(1'b0), .CPHA(1'b0), .LOG_LEVEL(1)) mon (.bus(qif));
    
    localparam PROGRAM_DEPTH = 80;
    logic [31:0] program_data [0:PROGRAM_DEPTH-1];
    logic [7:0] test_program [$];
    
    integer program_counter;
    integer program_length;
        
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
        TEST_data_tx_start_i = 1'b1;
        TEST_uart_tx_data_i = test_program[program_counter];
        wait (TEST_data_sent_o == 1'b1);
        @(posedge `CLK);
        #(1ps);
        program_counter++;
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











