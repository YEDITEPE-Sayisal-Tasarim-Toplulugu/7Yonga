module uart_tb;
    //Testing in different baud rates and TX and RX of course.
    // Clock and reset signals
    logic        clk;
    logic        rst_n;
    
    // AXI4-Lite interface
    logic        psel;
    logic        penable;
    logic        pwrite;
    logic [31:0] paddr;
    logic [31:0] pwdata;
    logic [31:0] prdata;
    logic        pready;
    
    // UART loopback (connect TX to RX for testing)
    logic        uart_rx;
    logic        uart_tx;
    
    // Variables for storing read data
    logic [31:0] cfg_value;
    logic [31:0] rx_data;
    logic [31:0] divisor; // CPB değerini takip etmek için değişken
    
    // Constants
    localparam CLK_PERIOD = 10; // 100 MHz clock
    
    // UART registers addresses (offset from base address)
    localparam UART_CPB = 8'h00; // Clock-per-bit register
    localparam UART_STP = 8'h04; // Stop-bit register
    localparam UART_RDR = 8'h08; // Read data register
    localparam UART_TDR = 8'h0C; // Transmit data register
    localparam UART_CFG = 8'h10; // Configuration register
    
    // Instantiate UART DUT
    uart dut (
        .clk(clk),
        .rst_n(rst_n),
        .psel(psel),
        .penable(penable),
        .pwrite(pwrite),
        .paddr(paddr),
        .pwdata(pwdata),
        .prdata(prdata),
        .pready(pready),
        .uart_rx(uart_rx),
        .uart_tx(uart_tx)
    );
    
    // Connect TX to RX for loopback testing
    assign uart_rx = uart_tx;
    
    // Clock generation
    always begin
        clk = 0; #(CLK_PERIOD/2);
        clk = 1; #(CLK_PERIOD/2);
    end
    
    // Task for AXI4-Lite write transaction
    task axi_write(input [31:0] addr, input [31:0] data);
        // Setup phase
        psel <= 1'b1;
        pwrite <= 1'b1;
        paddr <= addr;
        pwdata <= data;
        penable <= 1'b0;
        @(posedge clk);
        
        // Access phase
        penable <= 1'b1;
        wait (pready);
        @(posedge clk);
        
        // End transaction
        psel <= 1'b0;
        penable <= 1'b0;
        @(posedge clk);
        
        // CPB değerini takip etme
        if (addr == UART_CPB) begin
            divisor = data;
            $display("Updated CPB value to %0d", divisor);
        end
    endtask
    
    // Task for AXI4-Lite read transaction
    task axi_read(input [31:0] addr, output [31:0] data);
        // Setup phase
        psel <= 1'b1;
        pwrite <= 1'b0;
        paddr <= addr;
        penable <= 1'b0;
        @(posedge clk);
        
        // Access phase
        penable <= 1'b1;
        wait (pready);
        data = prdata;
        @(posedge clk);
        
        // End transaction
        psel <= 1'b0;
        penable <= 1'b0;
        @(posedge clk);
    endtask
    
    // Task to wait for a specific bit to become 1 in CFG register
    task wait_for_flag(input int bit_index, input int max_cycles = 10000);
        int count = 0;
        logic [31:0] temp_cfg;
        
        while (count < max_cycles) begin
            axi_read(UART_CFG, temp_cfg);
            if (temp_cfg[bit_index] == 1'b1) begin
                cfg_value = temp_cfg;  // Save the value for the caller
                break;
            end
            count++;
            #(CLK_PERIOD * 10);  // Wait 10 cycles between reads
        end
        
        if (count >= max_cycles) begin
            $display("Timeout waiting for bit %0d in CFG register", bit_index);
        end
    endtask
    
    // Test sequence
    initial begin
        // Initialize signals
        psel = 0;
        penable = 0;
        pwrite = 0;
        paddr = 0;
        pwdata = 0;
        rst_n = 1;
        divisor = 0;
        
        // Apply reset
        #20 rst_n = 0;
        #20 rst_n = 1;
        
        $display("Starting UART test with 9600 baud rate equivalent");
        
        // Configure UART
        // Use a small divisor for simulation speed
        axi_write(UART_CPB, 50);
        
        // Set stop bits to 1
        axi_write(UART_STP, 0);
        
        // Send character 'A' (ASCII 65 or 0x41)
        axi_write(UART_TDR, 8'h41);
        
        // Enable transmission
        axi_write(UART_CFG, 1); // Bit 0 is TX enable
        $display("Sent TX command, waiting for completion...");
        
        // Wait for TX completed flag (bit 2)
        wait_for_flag(2);
        
        $display("TX completed flag detected in CFG register = 0x%h", cfg_value);
        
        // Give the RX a chance to complete - it may happen slightly after TX complete
        #(50 * CLK_PERIOD);
        
        // Wait for RX data received flag (bit 1)
        wait_for_flag(1);
        
        $display("RX completed flag detected in CFG register = 0x%h", cfg_value);
        
        // IMPROVED: Wait for a full frame time after RX flag detection
        $display("Waiting for %0d clock cycles (12 * divisor) before reading RDR", divisor * 12);
        repeat (divisor * 12) @(posedge clk);
        
        // Read received data
        axi_read(UART_RDR, rx_data);
        $display("Data received: 0x%h", rx_data[7:0]);
        
        // Clear both status flags
        axi_write(UART_CFG, 1); // TX enable, clear status flags
        
        // Verify received data is correct
        if (rx_data[7:0] == 8'h41) begin
            $display("Test PASSED: Received correct data 'A'");
        end
        else begin
            $display("Test FAILED: Received incorrect data 0x%h, expected 0x41", rx_data[7:0]);
        end
        
        // Allow some time for the system to settle
        #(100 * CLK_PERIOD);
        
        $display("\nStarting UART test with higher baud rate");
        
        // Test another baud rate (using 10 for simulation speed)
        axi_write(UART_CPB, 10);
        
        // Send character 'B' (ASCII 66 or 0x42)
        axi_write(UART_TDR, 8'h42);
        
        // Enable transmission (should already be enabled)
        axi_write(UART_CFG, 1);
        $display("Sent second TX command at higher baud rate");
        
        // Wait for TX completed flag (bit 2)
        wait_for_flag(2);
        
        $display("Second TX completed flag detected in CFG register = 0x%h", cfg_value);
        
        // Give the RX a chance to complete
        #(20 * CLK_PERIOD);
        
        // Wait for RX data received flag (bit 1)
        wait_for_flag(1);
        
        $display("Second RX completed flag detected in CFG register = 0x%h", cfg_value);
        
        // IMPROVED: Wait for a full frame time after RX flag detection
        $display("Waiting for %0d clock cycles (12 * divisor) before reading RDR", divisor * 12);
        repeat (divisor * 12) @(posedge clk);
        
        // Read received data
        axi_read(UART_RDR, rx_data);
        $display("Data received at higher baud rate: 0x%h", rx_data[7:0]);
        
        // Clear both status flags
        axi_write(UART_CFG, 1); // TX enable, clear status flags
        
        // Verify received data is correct
        if (rx_data[7:0] == 8'h42) begin
            $display("Test PASSED: Received correct data 'B' at higher baud rate");
        end
        else begin
            $display("Test FAILED: Received incorrect data 0x%h, expected 0x42", rx_data[7:0]);
            
            // Try waiting a bit more and reading again
            #(50 * CLK_PERIOD);
            
            // Wait for another RX data received flag (bit 1)
            wait_for_flag(1);
            
            // IMPROVED: Wait for a full frame time after RX flag detection
            $display("Waiting for %0d clock cycles (12 * divisor) before second read", divisor * 12);
            repeat (divisor * 12) @(posedge clk);
            
            // Read received data again
            axi_read(UART_RDR, rx_data);
            $display("Second read attempt - Data received: 0x%h", rx_data[7:0]);
            
            if (rx_data[7:0] == 8'h42) begin
                $display("Test PASSED on second attempt: Received correct data 'B'");
            end
        end
        
        // End simulation
        $display("Tests completed");
        #1000 $finish;
    end
    
    // Optional: Save waveforms
    initial begin
        $dumpfile("uart_tb.vcd");
        $dumpvars(0, uart_tb);
    end
    
endmodule