module uart (
    // Clock and reset signals
    input  logic        clk,
    input  logic        rst_n,
    
    // AXI4-Lite interface
    input  logic        psel,
    input  logic        penable,
    input  logic        pwrite,
    input  logic [31:0] paddr,
    input  logic [31:0] pwdata,
    output logic [31:0] prdata,
    output logic        pready,
    
    // UART pins
    input  logic        uart_rx,
    output logic        uart_tx
);
    // Register addresses (offset from base address)
    localparam UART_CPB = 8'h00; // Clock-per-bit register
    localparam UART_STP = 8'h04; // Stop-bit register
    localparam UART_RDR = 8'h08; // Read data register
    localparam UART_TDR = 8'h0C; // Transmit data register
    localparam UART_CFG = 8'h10; // Configuration register
    
    // Register definitions
    logic [31:0] uart_cpb_reg;  // Clock-per-bit register
    logic [31:0] uart_stp_reg;  // Stop-bit register
    logic [31:0] uart_rdr_reg;  // Read data register
    logic [31:0] uart_tdr_reg;  // Transmit data register
    logic [31:0] uart_cfg_reg;  // Configuration register
    logic tx_data_updated;      // Signal to indicate TDR has been updated
    logic rx_data_updated;      // Signal to indicate RDR has been updated

    // States for TX and RX state machines
    localparam IDLE  = 2'b00;
    localparam START = 2'b01;
    localparam DATA  = 2'b10;
    localparam STOP  = 2'b11;
    
    // TX signals
    logic [1:0] tx_state;
    logic tx_active;
    logic tx_done;
    logic [31:0] tx_counter;
    logic [2:0] tx_bit_idx;
    
    // RX signals
    logic [1:0] rx_state;
    logic rx_active;
    logic rx_done;
    logic [31:0] rx_counter;
    logic [2:0] rx_bit_idx;
    logic [7:0] rx_data;
    
    // Stop bits calculation
    logic [31:0] stop_cycles;
    
    // AXI4-Lite interface
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            uart_cpb_reg <= 32'd0;
            uart_stp_reg <= 32'd0;
            uart_rdr_reg <= 32'd0;
            uart_tdr_reg <= 32'd0;
            uart_cfg_reg <= 32'd0;
            pready <= 1'b0;
            tx_data_updated <= 1'b0;
            rx_data_updated <= 1'b0;
        end else begin
            // Default assignment
            pready <= 1'b0;
            tx_data_updated <= 1'b0;
            
            // Update status registers based on hardware events (prioritized before register writes)
            if (rx_done) begin
                uart_rdr_reg <= {24'b0, rx_data}; // Update RX data register
                rx_data_updated <= 1'b1; // Mark RDR as updated
                $display("RDR updated with 0x%h, will set RX flag next cycle", rx_data);
            end
            
            // Set RX flag a cycle after data is updated
            if (rx_data_updated) begin
                uart_cfg_reg[1] <= 1'b1; // Set data received flag
                rx_data_updated <= 1'b0; // Reset the updated signal
                $display("Setting RX flag for data 0x%h", uart_rdr_reg[7:0]);
            end
            
            if (tx_done) begin
                uart_cfg_reg[2] <= 1'b1; // Set TX completed flag
                $display("Setting TX completed flag");
            end
            
            // Handle register writes
            if (psel && penable && pwrite) begin
                pready <= 1'b1;
                case (paddr[7:0])
                    UART_CPB: uart_cpb_reg <= pwdata;
                    UART_STP: uart_stp_reg <= pwdata;
                    UART_TDR: begin
                        uart_tdr_reg <= pwdata;
                        tx_data_updated <= 1'b1; // Mark TDR as updated
                        $display("TDR updated with 0x%h", pwdata[7:0]);
                    end
                    UART_CFG: begin
                        // Always update TX enable bit
                        uart_cfg_reg[0] <= pwdata[0];
                        
                        // Allow software to clear status bits by writing 0
                        if (pwdata[1] == 1'b0) begin 
                            uart_cfg_reg[1] <= 1'b0; // Clear received flag
                            $display("Clearing RX flag");
                        end
                        if (pwdata[2] == 1'b0) begin
                            uart_cfg_reg[2] <= 1'b0; // Clear TX completed flag
                            $display("Clearing TX flag");
                        end
                    end
                    default: ; // Do nothing
                endcase
            end
            // Handle register reads
            else if (psel && penable && !pwrite) begin
                pready <= 1'b1;
                $display("Reading address 0x%h, value = 0x%h", paddr, prdata);
            end
            // Handle just psel assertion without penable
            else if (psel && !penable) begin
                pready <= 1'b0; // Make sure pready is deasserted during setup phase
            end
        end
    end
    
    // Read data multiplexer
    always_comb begin
        case (paddr[7:0])
            UART_CPB: prdata = uart_cpb_reg;
            UART_STP: prdata = uart_stp_reg;
            UART_RDR: prdata = uart_rdr_reg;
            UART_TDR: prdata = uart_tdr_reg;
            UART_CFG: prdata = uart_cfg_reg;
            default:  prdata = 32'd0;
        endcase
    end
    
    // Calculate stop bit cycles
    always_comb begin
        if (uart_stp_reg[1:0] == 2'b00)
            stop_cycles = uart_cpb_reg; // 1 stop bit
        else if (uart_stp_reg[1:0] == 2'b01)
            stop_cycles = uart_cpb_reg + (uart_cpb_reg >> 1); // 1.5 stop bits
        else
            stop_cycles = uart_cpb_reg << 1; // 2 stop bits
    end
    
    // UART transmitter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_state <= IDLE;
            tx_active <= 1'b0;
            tx_done <= 1'b0;
            tx_counter <= 32'd0;
            tx_bit_idx <= 3'd0;
            uart_tx <= 1'b1; // Idle high
        end else begin
            // Default assignments
            tx_done <= 1'b0;
            
            case (tx_state)
                IDLE: begin
                    uart_tx <= 1'b1; // Idle high
                    tx_counter <= 32'd0;
                    tx_bit_idx <= 3'd0;
                    
                    // Check if transmit is enabled by software and not already active
                    if (uart_cfg_reg[0] && (tx_data_updated || !tx_active)) begin
                        tx_active <= 1'b1;
                        tx_state <= START;
                        $display("TX: Starting transmission of 0x%h", uart_tdr_reg[7:0]);
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
                    uart_tx <= uart_tdr_reg[tx_bit_idx]; // Send data bit
                    
                    if (tx_counter < uart_cpb_reg - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        
                        if (tx_bit_idx < 7) begin
                            tx_bit_idx <= tx_bit_idx + 1;
                            $display("TX: Sent bit %0d = %0d", tx_bit_idx, uart_tdr_reg[tx_bit_idx]);
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
    
    // UART receiver
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_state <= IDLE;
            rx_active <= 1'b0;
            rx_done <= 1'b0;
            rx_counter <= 32'd0;
            rx_bit_idx <= 3'd0;
            rx_data <= 8'd0;
        end else begin
            // Default assignments
            rx_done <= 1'b0;
            
            case (rx_state)
                IDLE: begin
                    rx_active <= 1'b0;
                    rx_counter <= 32'd0;
                    rx_bit_idx <= 3'd0;
                    
                    // Detect start bit (falling edge)
                    if (uart_rx == 1'b0 && !rx_active) begin
                        rx_state <= START;
                        rx_active <= 1'b1;
                        $display("RX: Start bit detected");
                    end
                end
                
                START: begin
                    // Wait for half a bit time to sample in the middle of the start bit
                    if (rx_counter < (uart_cpb_reg >> 1) - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        // Verify still low (valid start bit)
                        if (uart_rx == 1'b0) begin
                            rx_state <= DATA;
                            $display("RX: Valid start bit confirmed");
                        end else begin
                            rx_state <= IDLE; // False start
                            rx_active <= 1'b0;
                            $display("RX: False start detected");
                        end
                    end
                end
                
                DATA: begin
                    // Sample in the middle of each data bit
                    if (rx_counter < uart_cpb_reg - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        rx_data[rx_bit_idx] <= uart_rx; // Sample bit
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
                    // Wait for stop bit
                    if (rx_counter < uart_cpb_reg - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        rx_state <= IDLE;
                        rx_active <= 1'b0;
                        
                        // Validate stop bit (should be high)
                        if (uart_rx == 1'b1) begin
                            rx_done <= 1'b1; // Data received successfully
                            $display("RX: Stop bit valid, reception complete for byte 0x%h", rx_data);
                        end else begin
                            // Framing error - could add error handling here
                            $display("RX: Framing error, invalid stop bit");
                        end
                    end
                end
                
                default: rx_state <= IDLE;
            endcase
        end
    end
    
endmodule