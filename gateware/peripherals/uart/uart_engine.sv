`timescale 1ns / 1ps

module uart_engine (
    // Clock and reset signals
    input  logic        aclk,
    input  logic        aresetn,

    input logic [31:0]  uart_cpb_reg,  // Clock-per-bit register
    input logic [31:0]  uart_stp_reg,  // Stop-bit register

    input logic         data_tx_start_i,
    input logic [7:0]   uart_tx_data_i,  // Transmit data
    output logic        data_sent_o,

    output logic        rx_received_o,
    output logic [7:0]  rx_received_data_o,

    // UART pins
    input  logic        uart_rx,
    output logic        uart_tx
);
    // Register adresleri 
    localparam UART_CPB = 8'h00; // Clock-per-bit register
    localparam UART_STP = 8'h04; // Stop-bit register
    localparam UART_RDR = 8'h08; // Read data register
    localparam UART_TDR = 8'h0C; // Transmit data register
    localparam UART_CFG = 8'h10; // Configuration register
    
    // TX ve RX durum makineleri
    localparam IDLE  = 2'b00;
    localparam START = 2'b01;
    localparam DATA  = 2'b10;
    localparam STOP  = 2'b11;
    
    // TX sinyalleri
    logic [1:0] tx_state;
    logic tx_active;
    logic tx_done;
    logic [31:0] tx_counter;
    logic [2:0] tx_bit_idx;
    
    // RX sinyalleri
    logic [1:0] rx_state;
    logic rx_active;
    logic rx_done;
    logic [31:0] rx_counter;
    logic [2:0] rx_bit_idx;
    logic [7:0] rx_data;
    
    // Stop bits hesaplama
    logic [31:0] stop_cycles;
    
    // AXI handshake yardımcı değişkenleri
    logic        aw_en;
    logic [31:0] axi_awaddr;
    logic [31:0] axi_araddr;

    assign data_sent_o          = tx_done;
    assign rx_received_o        = rx_done;
    assign rx_received_data_o   = rx_data;
    
    //----------------------------------------------------------------------
    // Stop bit hesaplama
    //----------------------------------------------------------------------
    always_comb begin
        if (uart_stp_reg[1:0] == 2'b00)
            stop_cycles = uart_cpb_reg; 
        else if (uart_stp_reg[1:0] == 2'b01)
            stop_cycles = uart_cpb_reg + (uart_cpb_reg >> 1); 
        else
            stop_cycles = uart_cpb_reg << 1;
    end
    
    //----------------------------------------------------------------------
    // UART verici (transmitter)
    //----------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            tx_state <= IDLE;
            tx_active <= 1'b0;
            tx_done <= 1'b0;
            tx_counter <= 32'd0;
            tx_bit_idx <= 3'd0;
            uart_tx <= 1'b1;
        end else begin
            tx_done <= 1'b0;
            
            case (tx_state)
                IDLE: begin
                    uart_tx <= 1'b1;
                    tx_counter <= 32'd0;
                    tx_bit_idx <= 3'd0;
                    
                    if (data_tx_start_i && ~tx_done && (!tx_active)) begin
                        tx_active <= 1'b1;
                        tx_state <= START;
                        $display("TX: Starting transmission of 0x%h", uart_tx_data_i[7:0]);
                    end
                end
                
                START: begin
                    uart_tx <= 1'b0; // Start bit (low)
                    
                    if (tx_counter < uart_cpb_reg - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        tx_state <= DATA;
                        $display("TX: Start bit completed");
                    end
                end
                
                DATA: begin
                    uart_tx <= uart_tx_data_i[tx_bit_idx]; // Send data bit
                    
                    if (tx_counter < uart_cpb_reg - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        
                        if (tx_bit_idx < 7) begin
                            tx_bit_idx <= tx_bit_idx + 1;
                            $display("TX: Sent bit %0d = %0d", tx_bit_idx, uart_tx_data_i[tx_bit_idx]);
                        end else begin
                            tx_bit_idx <= 3'd0;
                            tx_state <= STOP;
                            $display("TX: All data bits sent");
                        end
                    end
                end
                
                STOP: begin
                    uart_tx <= 1'b1; // Stop bit (high)
                    
                    if (tx_counter < stop_cycles - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        tx_state <= IDLE;
                        tx_active <= 1'b0;
                        tx_done <= 1'b1; // Set TX completed flag
                        $display("TX: Stop bit completed, transmission done");
                    end
                end
                
                default: tx_state <= IDLE;
            endcase
        end
    end
    
    //----------------------------------------------------------------------
    // UART alıcı (receiver)
    //----------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            rx_state <= IDLE;
            rx_active <= 1'b0;
            rx_done <= 1'b0;
            rx_counter <= 32'd0;
            rx_bit_idx <= 3'd0;
            rx_data <= 8'd0;
        end else begin
            rx_done <= 1'b0;
            
            case (rx_state)
                IDLE: begin
                    rx_active <= 1'b0;
                    rx_counter <= 32'd0;
                    rx_bit_idx <= 3'd0;
                    
                    if (uart_rx == 1'b0 && !rx_active) begin
                        rx_state <= START;
                        rx_active <= 1'b1;
                        $display("RX: Start bit detected");
                    end
                end
                
                START: begin
                    if (rx_counter < (uart_cpb_reg >> 1) - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        if (uart_rx == 1'b0) begin
                            rx_state <= DATA;
                            $display("RX: Valid start bit confirmed");
                        end else begin
                            rx_state <= IDLE; 
                            rx_active <= 1'b0;
                            $display("RX: False start detected");
                        end
                    end
                end
                
                DATA: begin
                    if (rx_counter < uart_cpb_reg - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        rx_data[rx_bit_idx] <= uart_rx; 
                        $display("RX: Sampled bit %0d = %0d", rx_bit_idx, uart_rx);
                        
                        if (rx_bit_idx < 7) begin
                            rx_bit_idx <= rx_bit_idx + 1;
                        end else begin
                            rx_bit_idx <= 3'd0;
                            rx_state <= STOP;
                            $display("RX: All data bits received: 0x%h", {rx_data[6:0], uart_rx});
                        end
                    end
                end
                
                STOP: begin
                    if (rx_counter < uart_cpb_reg - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        rx_state <= IDLE;
                        rx_active <= 1'b0;
                        
                        if (uart_rx == 1'b1) begin
                            rx_done <= 1'b1; 
                            $display("RX: Stop bit valid, reception complete for byte 0x%h", rx_data);
                        end else begin
                    
                            $display("RX: Framing error, invalid stop bit");
                        end
                    end
                end
                
                default: rx_state <= IDLE;
            endcase
        end
    end
    
endmodule
