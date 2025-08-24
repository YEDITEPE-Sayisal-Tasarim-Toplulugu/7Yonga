`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 18.08.2025 18:47:14
// Design Name: 
// Module Name: tb_programmer_top
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

module tb_programmer_top();

    `SIM_CLK_RST(20, 5, 10_000_000)
    
    localparam FREQ_HZ                     = 1_000_000 * 50;
    localparam PROGRAMMER_BAUDE_RATE       = 9600;
    localparam PROGRAMMER_START_ADDR       = 32'h0000_0800;
    
    localparam PROGRAMMER_CPB_DATA          = FREQ_HZ/PROGRAMMER_BAUDE_RATE;
    
    logic [7:0] test_program [$] = {
        // 0x33221100
        8'h00,
        8'h11,
        8'h22,
        8'h33,
        
        // 0x77665544
        8'h44,
        8'h55,
        8'h66,
        8'h77,
        
        // 0xbbaa9988
        8'h88,
        8'h99,
        8'haa,
        8'hbb,
        
        // 0xdeadbeaf
        8'haf,
        8'hbe,
        8'had,
        8'hde
    };
    
    integer program_counter;
    integer program_length;
    
    logic [31:0] test_program_rx_data [$];
    logic [31:0] test_program_rx_addr [$];
    
    logic programmer_enable_i;
    logic programmer_rx;
    
    logic mem_write_enable_o;
    logic [31:0] mem_write_addr_o;
    logic [31:0] mem_write_data_o;
    
    logic TEST_data_tx_start_i;
    logic [7:0] TEST_uart_tx_data_i;
    logic TEST_data_sent_o;
    
    uart_programmer_top
    #( 
        .FREQ_HZ                    ( FREQ_HZ                   ),
        .PROGRAMMER_BAUDE_RATE      ( PROGRAMMER_BAUDE_RATE     ),
        .PROGRAMMER_START_ADDR      ( PROGRAMMER_START_ADDR     )
    ) DUT (
        .clk_i                      ( `CLK                      ),
        .reset_ni                   ( `RST                      ),
        
        .programmer_enable_i        ( programmer_enable_i       ),
        .programmer_rx              ( programmer_rx             ),
        
        .mem_write_enable_o         ( mem_write_enable_o        ),
        .mem_write_addr_o           ( mem_write_addr_o          ),
        .mem_write_data_o           ( mem_write_data_o          )
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
        .uart_tx                    ( programmer_rx             )
    );
    
    initial begin
        programmer_enable_i = 1;
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
        program_length = test_program.size();
        program_counter=0;
        $display("[SIM] waiting for transmit...");
        wait (program_counter == program_length);
        $display("[SIM] transmit done.");
        $display("[SIM] waiting for rx...");
        repeat (10) @(posedge `CLK);
        foreach (test_program_rx_data[i]) begin
            for (integer j=0; j<4; j++) begin
                `COMPARE((test_program_rx_data[i][j*8+:8] == test_program[i*4+j]), 
                    $sformatf("[SIM] rx data error, index: %0d, offset: %0d, rx_data: %0h, test: %0h",
                        i,
                        j,
                        test_program_rx_data[i][j*8+:8],
                        test_program[i*4+j]
                    ))
            end
            `COMPARE((test_program_rx_addr[i] == (PROGRAMMER_START_ADDR+i*4)), 
                $sformatf("[SIM] rx addr error, index: %0d, rx_addr: %0h, test: %0h",
                    i,
                    test_program_rx_addr[i],
                    (PROGRAMMER_START_ADDR+i*4)
                ))
        end
        $display("[SIM] done.");
        $finish;
    end
    
    always begin
        #(1ps);
        wait (mem_write_enable_o == 1'b1);
        #(1ps);
        test_program_rx_data.push_back(mem_write_data_o);
        test_program_rx_addr.push_back(mem_write_addr_o);
        @(posedge `CLK);
        #(1ps);
    end

endmodule



















