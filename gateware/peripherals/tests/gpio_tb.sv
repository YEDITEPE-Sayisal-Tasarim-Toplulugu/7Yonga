`timescale 1ns / 1ps

module gpio_tb;
    // Clock and reset signals
    logic        s_axi_aclk;
    logic        s_axi_aresetn;
    
    // AXI4-Lite Slave Interface
    // Write Address Channel
    logic [31:0] s_axi_awaddr;
    logic        s_axi_awvalid;
    logic        s_axi_awready;
    
    // Write Data Channel
    logic [31:0] s_axi_wdata;
    logic [3:0]  s_axi_wstrb;
    logic        s_axi_wvalid;
    logic        s_axi_wready;
    
    // Write Response Channel
    logic [1:0]  s_axi_bresp;
    logic        s_axi_bvalid;
    logic        s_axi_bready;
    
    // Read Address Channel
    logic [31:0] s_axi_araddr;
    logic        s_axi_arvalid;
    logic        s_axi_arready;
    
    // Read Data Channel
    logic [31:0] s_axi_rdata;
    logic [1:0]  s_axi_rresp;
    logic        s_axi_rvalid;
    logic        s_axi_rready;
    
    // GPIO pins
    logic [15:0] gpio_in;
    logic [15:0] gpio_out;
    
    // Register addresses
    localparam GPIO_IDR = 8'h00; // Input data register
    localparam GPIO_ODR = 8'h04; // Output data register
    
    // Instance of the GPIO module
    gpio dut (
        .s_axi_aclk    (s_axi_aclk),
        .s_axi_aresetn (s_axi_aresetn),
        
        .s_axi_awaddr  (s_axi_awaddr),
        .s_axi_awvalid (s_axi_awvalid),
        .s_axi_awready (s_axi_awready),
        
        .s_axi_wdata   (s_axi_wdata),
        .s_axi_wstrb   (s_axi_wstrb),
        .s_axi_wvalid  (s_axi_wvalid),
        .s_axi_wready  (s_axi_wready),
        
        .s_axi_bresp   (s_axi_bresp),
        .s_axi_bvalid  (s_axi_bvalid),
        .s_axi_bready  (s_axi_bready),
        
        .s_axi_araddr  (s_axi_araddr),
        .s_axi_arvalid (s_axi_arvalid),
        .s_axi_arready (s_axi_arready),
        
        .s_axi_rdata   (s_axi_rdata),
        .s_axi_rresp   (s_axi_rresp),
        .s_axi_rvalid  (s_axi_rvalid),
        .s_axi_rready  (s_axi_rready),
        
        .gpio_in       (gpio_in),
        .gpio_out      (gpio_out)
    );
    
    // Clock generation
    initial begin
        s_axi_aclk = 1'b0;
        forever #5 s_axi_aclk = ~s_axi_aclk; // 100MHz clock
    end
    
    // Tasks for AXI4-Lite transactions
    
    // AXI4-Lite write transaction
    task axi_write(input [31:0] addr, input [31:0] data);
        // Address phase
        s_axi_awaddr  <= addr;
        s_axi_awvalid <= 1'b1;
        s_axi_wdata   <= data;
        s_axi_wstrb   <= 4'hF; // Write all bytes
        s_axi_wvalid  <= 1'b1;
        s_axi_bready  <= 1'b1;
        
        wait(s_axi_awready && s_axi_wready);
        @(posedge s_axi_aclk);
        
        // Clear valid signals after handshake
        s_axi_awvalid <= 1'b0;
        s_axi_wvalid  <= 1'b0;
        
        // Response phase
        wait(s_axi_bvalid);
        @(posedge s_axi_aclk);
        s_axi_bready <= 1'b0;
        
        // Check response
        if (s_axi_bresp != 2'b00) begin
            $display("ERROR: AXI write response error at time %t", $time);
        end
        
        $display("AXI Write: Addr=0x%h, Data=0x%h at time %t", addr, data, $time);
    endtask
    
    // AXI4-Lite read transaction
    task axi_read(input [31:0] addr, output [31:0] data);
        // Address phase
        s_axi_araddr  <= addr;
        s_axi_arvalid <= 1'b1;
        s_axi_rready  <= 1'b1;
        
        wait(s_axi_arready);
        @(posedge s_axi_aclk);
        
        // Clear valid signal after handshake
        s_axi_arvalid <= 1'b0;
        
        // Data phase
        wait(s_axi_rvalid);
        data = s_axi_rdata;
        @(posedge s_axi_aclk);
        s_axi_rready <= 1'b0;
        
        // Check response
        if (s_axi_rresp != 2'b00) begin
            $display("ERROR: AXI read response error at time %t", $time);
        end
        
        $display("AXI Read: Addr=0x%h, Data=0x%h at time %t", addr, data, $time);
    endtask
    
    // Test sequence
    initial begin
        // Initialize signals
        s_axi_aresetn  = 1'b0;
        s_axi_awvalid  = 1'b0;
        s_axi_wvalid   = 1'b0;
        s_axi_bready   = 1'b0;
        s_axi_arvalid  = 1'b0;
        s_axi_rready   = 1'b0;
        gpio_in        = 16'h0000;
        
        // Apply reset
        #20;
        s_axi_aresetn = 1'b1;
        #20;
        
        // Test 1: Write to GPIO_ODR
        $display("\n--- Test 1: Write to GPIO_ODR ---");
        axi_write(GPIO_ODR, 32'hA5A5_5A5A);
        #10;
        
        // Check that only lower 16 bits affect output
        if (gpio_out !== 16'h5A5A) begin
            $display("ERROR: GPIO output doesn't match expected value. Got 0x%h, expected 0x%h", gpio_out, 16'h5A5A);
        end else begin
            $display("SUCCESS: GPIO output is correct: 0x%h", gpio_out);
        end
        
        // Test 2: Read from GPIO_ODR
        $display("\n--- Test 2: Read from GPIO_ODR ---");
        begin
            logic [31:0] read_data;
            axi_read(GPIO_ODR, read_data);
            
            // Check that the data read matches what was written
            if (read_data !== 32'hA5A5_5A5A) begin
                $display("ERROR: Read data from GPIO_ODR doesn't match expected value. Got 0x%h, expected 0x%h", read_data, 32'hA5A5_5A5A);
            end else begin
                $display("SUCCESS: Read data from GPIO_ODR is correct: 0x%h", read_data);
            end
        end
        
        // Test 3: Set input pins and read from GPIO_IDR
        $display("\n--- Test 3: Read from GPIO_IDR ---");
        gpio_in = 16'hABCD;
        #10; // Allow time for input to propagate
        
        begin
            logic [31:0] read_data;
            axi_read(GPIO_IDR, read_data);
            
            // Check that the upper 16 bits are 0 and lower 16 bits match gpio_in
            if (read_data !== 32'h0000_ABCD) begin
                $display("ERROR: Read data from GPIO_IDR doesn't match expected value. Got 0x%h, expected 0x%h", read_data, 32'h0000_ABCD);
            end else begin
                $display("SUCCESS: Read data from GPIO_IDR is correct: 0x%h", read_data);
            end
        end
        
        // Test 4: Try writing to GPIO_IDR (should have no effect since it's read-only)
        $display("\n--- Test 4: Write to GPIO_IDR (Read-Only) ---");
        axi_write(GPIO_IDR, 32'h1234_5678);
        #10;
        
        begin
            logic [31:0] read_data;
            axi_read(GPIO_IDR, read_data);
            
            // Verify that IDR still contains the value from gpio_in
            if (read_data !== 32'h0000_ABCD) begin
                $display("ERROR: GPIO_IDR changed after write to read-only register. Got 0x%h, expected 0x%h", read_data, 32'h0000_ABCD);
            end else begin
                $display("SUCCESS: GPIO_IDR correctly ignored write to read-only register: 0x%h", read_data);
            end
        end
        
        // Test 5: Change input pins and verify GPIO_IDR update
        $display("\n--- Test 5: Change input pins and verify GPIO_IDR update ---");
        gpio_in = 16'h1234;
        #10; // Allow time for input to propagate
        
        begin
            logic [31:0] read_data;
            axi_read(GPIO_IDR, read_data);
            
            // Check that GPIO_IDR reflects the new input value
            if (read_data !== 32'h0000_1234) begin
                $display("ERROR: GPIO_IDR doesn't reflect new input value. Got 0x%h, expected 0x%h", read_data, 32'h0000_1234);
            end else begin
                $display("SUCCESS: GPIO_IDR correctly updated with new input value: 0x%h", read_data);
            end
        end
        
        // Test 6: Write only to lower 16 bits of GPIO_ODR
        $display("\n--- Test 6: Write only to lower 16 bits of GPIO_ODR ---");
        axi_write(GPIO_ODR, 32'h0000_FEDC);
        #10;
        
        if (gpio_out !== 16'hFEDC) begin
            $display("ERROR: GPIO output doesn't match expected value. Got 0x%h, expected 0x%h", gpio_out, 16'hFEDC);
        end else begin
            $display("SUCCESS: GPIO output is correct: 0x%h", gpio_out);
        end
        
        $display("\n--- All GPIO Tests Completed ---");
        #100;
        $finish;
    end
    
    // Monitor GPIO signals
    initial begin
        $monitor("Time=%t, gpio_in=0x%h, gpio_out=0x%h", $time, gpio_in, gpio_out);
    end
endmodule