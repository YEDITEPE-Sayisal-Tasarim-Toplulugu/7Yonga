`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10.08.2025 12:55:46
// Design Name: 
// Module Name: uart_monitor
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


// Basit UART Monitor
module uart_monitor #(
    parameter CLK_FREQ_HZ = 50_000_000, // Sistem clock frekansı
    parameter BAUD_RATE   = 115200
)(
    input  logic clk,
    input  logic rst_n,
    input  logic uart_line // tx veya rx hattı olabilir
);

    localparam integer CLKS_PER_BIT = CLK_FREQ_HZ / BAUD_RATE;

    typedef enum logic [1:0] {
        IDLE,
        START,
        DATA,
        STOP
    } state_t;

    state_t state;
    int bit_idx;
    int clk_count;
    byte data_byte;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state     <= IDLE;
            bit_idx   <= 0;
            clk_count <= 0;
            data_byte <= 0;
        end
        else begin
            case (state)
                IDLE: begin
                    if (uart_line == 1'b0) begin // start bit algılandı
                        state     <= START;
                        clk_count <= CLKS_PER_BIT/2; // ortadan örnekle
                    end
                end

                START: begin
                    if (clk_count == 0) begin
                        state     <= DATA;
                        bit_idx   <= 0;
                        clk_count <= CLKS_PER_BIT - 1;
                    end
                    else
                        clk_count <= clk_count - 1;
                end

                DATA: begin
                    if (clk_count == 0) begin
                        data_byte[bit_idx] <= uart_line;
                        bit_idx <= bit_idx + 1;

                        if (bit_idx == 7) begin
                            state <= STOP;
                        end

                        clk_count <= CLKS_PER_BIT - 1;
                    end
                    else
                        clk_count <= clk_count - 1;
                end

                STOP: begin
                    if (clk_count == 0) begin
                        // Karakter alındı, ekrana yaz
                        $display("[%0t] UART MONITOR: 0x%02h (%s)",
                                 $time, data_byte, 
                                 (data_byte >= 32 && data_byte < 127) ? {data_byte} : ".");
                        state <= IDLE;
                    end
                    else
                        clk_count <= clk_count - 1;
                end
            endcase
        end
    end

endmodule

