`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 18.08.2025 18:33:39
// Design Name: 
// Module Name: uart_programmer_top
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

module uart_programmer_top
    #(parameter 
            FREQ_HZ                     = 1_000_000 * 50,
            PROGRAMMER_BAUDE_RATE       = 9600,
            MEM_START_ADDR              = 32'h0000_0800,
            MEM_INC_COUNT               = 4
    )
    (
        input  logic clk_i, reset_ni,
        
        input  logic programmer_enable_i,
        input  logic programmer_rx,
        
        output logic mem_write_enable_o,
        output logic [31:0] mem_write_addr_o,
        output logic [31:0] mem_write_data_o
    );
    
    localparam PROGRAMMER_CPB_DATA = FREQ_HZ/PROGRAMMER_BAUDE_RATE;
    
    // UART RX interface
    logic        uart_data_valid_w;
    logic [7:0]  uart_data_w;
    logic [31:0] mem_write_addr_r;
    logic        data_shift_done_r;
    logic [31:0] data_shift_r;
    logic [1:0]  byte_count_r;
    
    // default outputs
    assign mem_write_addr_o   = mem_write_addr_r;
    assign mem_write_data_o   = data_shift_r;
    assign mem_write_enable_o = programmer_enable_i & data_shift_done_r;
    
    uart_engine COMMUNICATION_ENGINE (
        .aclk               ( clk_i                 ),
        .aresetn            ( reset_ni              ),
    
        .uart_cpb_reg       ( PROGRAMMER_CPB_DATA   ),
        .uart_stp_reg       ( 0                     ),
    
        .data_tx_start_i    ( 0                     ),
        .uart_tx_data_i     ( 0                     ),
        .data_sent_o        (                       ),
    
        .rx_received_o      ( uart_data_valid_w     ),
        .rx_received_data_o ( uart_data_w           ),
    
        .uart_rx            ( programmer_rx         ),
        .uart_tx            (                       )
    );
    
    always_ff @(posedge clk_i or negedge reset_ni) begin
        if (!reset_ni) begin
            mem_write_addr_r <= MEM_START_ADDR;
            data_shift_r     <= 32'd0;
            byte_count_r     <= 2'd0;
            data_shift_done_r <= 1'b0;
        end else begin
            data_shift_done_r <= 1'b0;
            
            if (uart_data_valid_w && programmer_enable_i) begin
                // Shift gelen byte'ı alta ekle
                data_shift_r <= {uart_data_w, data_shift_r[31:8]};
                byte_count_r <= byte_count_r + 1'b1;
                
                // 4 byte tamamlandığında adresi arttır
                if (byte_count_r == 2'd3) begin
                    byte_count_r     <= 2'd0;   // reset counter
                    data_shift_done_r <= 1'b1;
                end
            end
            
            if (data_shift_done_r) begin
                mem_write_addr_r <= mem_write_addr_r + MEM_INC_COUNT;
            end
        end
    end
    
endmodule






















