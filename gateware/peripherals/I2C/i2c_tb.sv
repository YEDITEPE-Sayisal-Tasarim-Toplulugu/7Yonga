`timescale 1ns / 1ps

module i2c_master_tb;
    // Clock and reset signals
    logic        s_axi_aclk;
    logic        s_axi_aresetn;
    
    // AXI4-Lite Slave Interface
    logic [31:0] s_axi_awaddr;
    logic        s_axi_awvalid;
    logic        s_axi_awready;
    logic [31:0] s_axi_wdata;
    logic [3:0]  s_axi_wstrb;
    logic        s_axi_wvalid;
    logic        s_axi_wready;
    logic [1:0]  s_axi_bresp;
    logic        s_axi_bvalid;
    logic        s_axi_bready;
    logic [31:0] s_axi_araddr;
    logic        s_axi_arvalid;
    logic        s_axi_arready;
    logic [31:0] s_axi_rdata;
    logic [1:0]  s_axi_rresp;
    logic        s_axi_rvalid;
    logic        s_axi_rready;
    
    // I2C Interface
    logic        scl_i;
    logic        scl_o;
    logic        scl_oen;
    logic        sda_i;
    logic        sda_o;
    logic        sda_oen;
    
    // Bidirectional I2C signals
    wire         scl;
    wire         sda;
    
    // Pull-up modeling
    pullup(scl);
    pullup(sda);
    
    // Bidirectional pin control
    assign scl = scl_oen ? 1'bz : scl_o;
    assign sda = sda_oen ? 1'bz : sda_o;
    assign scl_i = scl;
    assign sda_i = sda;
    
    // Register addresses
    localparam I2C_NBY = 8'h00;
    localparam I2C_ADR = 8'h04;
    localparam I2C_RDR = 8'h08;
    localparam I2C_TDR = 8'h0C;
    localparam I2C_CFG = 8'h10;
    
    // Instance of I2C Master
    i2c_master dut (
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
        
        .scl_i         (scl_i),
        .scl_o         (scl_o),
        .scl_oen       (scl_oen),
        .sda_i         (sda_i),
        .sda_o         (sda_o),
        .sda_oen       (sda_oen)
    );
    
    // Clock generation - 100MHz
    initial begin
        s_axi_aclk = 1'b0;
        forever #5 s_axi_aclk = ~s_axi_aclk;
    end
    
    // I2C Slave Model
    logic [7:0] slave_memory[0:255];
    logic [7:0] slave_addr = 8'h50;  // Slave address 0x50
    logic       slave_ack;
    logic [7:0] slave_data_out;
    logic       slave_sda_oen = 1'b1;
    
    assign sda = (!slave_sda_oen) ? 1'b0 : 1'bz;
    
    // Simple I2C slave behavior
    task i2c_slave_response();
        logic [7:0] received_addr;
        logic       rw_bit;
        logic [7:0] reg_addr;
        integer     bit_count;
        logic [7:0] data_byte;
        
        // Wait for START condition
        @(negedge sda);
        if (scl !== 1'b1) return;
        
        $display("I2C Slave: START condition detected");
        
        // Receive address + R/W bit
        received_addr = 8'b0;
        for (bit_count = 0; bit_count < 8; bit_count++) begin
            @(posedge scl);
            received_addr = {received_addr[6:0], sda};
            $display("I2C Slave: Bit %0d = %b, addr so far = 0x%h", bit_count, sda, received_addr);
        end
        
        // Extract address and R/W bit
        rw_bit = received_addr[0];
        $display("I2C Slave: Full byte received = 0x%h", received_addr);
        $display("I2C Slave: Address = 0x%h, R/W = %b", received_addr[7:1], rw_bit);
        
        // Send ACK if address matches
        @(negedge scl);
        if (received_addr[7:1] == slave_addr[6:0]) begin
            slave_sda_oen = 1'b0;  // Drive SDA low for ACK
            $display("I2C Slave: Sending ACK");
            @(negedge scl);
            slave_sda_oen = 1'b1;  // Release SDA
            
            if (rw_bit == 1'b0) begin  // Write operation
                // Receive data bytes
                for (int byte_num = 0; byte_num < 4; byte_num++) begin
                    data_byte = 8'b0;
                    for (bit_count = 0; bit_count < 8; bit_count++) begin
                        @(posedge scl);
                        data_byte = {data_byte[6:0], sda};
                    end
                    
                    $display("I2C Slave: Received data[%0d] = 0x%h", byte_num, data_byte);
                    
                    // Send ACK
                    @(negedge scl);
                    slave_sda_oen = 1'b0;  // ACK
                    @(negedge scl);
                    slave_sda_oen = 1'b1;  // Release
                    
                    // Check for STOP condition
                    #10; // Small delay to check stop
                    if (scl === 1'b1) begin
                        @(posedge sda);
                        if (scl === 1'b1) begin
                            $display("I2C Slave: STOP detected after byte %0d", byte_num);
                            break;
                        end
                    end
                end
            end else begin  // Read operation
                // Send data bytes
                for (int byte_num = 0; byte_num < 4; byte_num++) begin
                    data_byte = 8'hA0 + byte_num;  // Test data
                    
                    for (bit_count = 7; bit_count >= 0; bit_count--) begin
                        @(negedge scl);
                        slave_sda_oen = data_byte[bit_count] ? 1'b1 : 1'b0;
                        @(posedge scl);
                    end
                    
                    $display("I2C Slave: Sent data[%0d] = 0x%h", byte_num, data_byte);
                    
                    // Receive ACK/NACK
                    @(negedge scl);
                    slave_sda_oen = 1'b1;  // Release for master's ACK
                    @(posedge scl);
                    if (sda === 1'b1) begin  // NACK received
                        $display("I2C Slave: NACK received");
                        break;
                    end
                end
            end
        end else begin
            // NACK - address doesn't match
            @(negedge scl);
            slave_sda_oen = 1'b1;  // NACK
            $display("I2C Slave: Address mismatch, sending NACK");
        end
        
        // Wait for STOP condition
        @(posedge sda);
        if (scl === 1'b1) begin
            $display("I2C Slave: STOP condition detected");
        end
        
        slave_sda_oen = 1'b1;  // Ensure SDA is released
    endtask
    
    // AXI4-Lite write task
    task axi_write(input [31:0] addr, input [31:0] data);
        s_axi_awaddr  <= addr;
        s_axi_awvalid <= 1'b1;
        s_axi_wdata   <= data;
        s_axi_wstrb   <= 4'hF;
        s_axi_wvalid  <= 1'b1;
        s_axi_bready  <= 1'b1;
        
        wait(s_axi_awready && s_axi_wready);
        @(posedge s_axi_aclk);
        
        s_axi_awvalid <= 1'b0;
        s_axi_wvalid  <= 1'b0;
        
        wait(s_axi_bvalid);
        @(posedge s_axi_aclk);
        s_axi_bready <= 1'b0;
        
        $display("AXI Write: Addr=0x%h, Data=0x%h", addr, data);
    endtask
    
    // AXI4-Lite read task
    task axi_read(input [31:0] addr, output [31:0] data);
        s_axi_araddr  <= addr;
        s_axi_arvalid <= 1'b1;
        s_axi_rready  <= 1'b1;
        
        wait(s_axi_arready);
        @(posedge s_axi_aclk);
        
        s_axi_arvalid <= 1'b0;
        
        wait(s_axi_rvalid);
        data = s_axi_rdata;
        @(posedge s_axi_aclk);
        s_axi_rready <= 1'b0;
        
        $display("AXI Read: Addr=0x%h, Data=0x%h", addr, data);
    endtask
    
    // Wait for I2C transaction to complete
    task wait_i2c_complete();
        logic [31:0] cfg_val;
        int timeout_cnt = 0;
        
        do begin
            axi_read(I2C_CFG, cfg_val);
            #100;
            timeout_cnt++;
            if (timeout_cnt > 1000) begin
                $display("ERROR: I2C transaction timeout!");
                break;
            end
        end while (!(cfg_val[1] || cfg_val[3]));  // Wait for TX or RX complete
        
        if (timeout_cnt <= 1000) begin
            $display("I2C transaction completed in %0d cycles", timeout_cnt);
        end
    endtask
    
    // Main test sequence
    initial begin
        logic [31:0] read_data;
        
        // Initialize signals
        s_axi_aresetn  = 1'b0;
        s_axi_awvalid  = 1'b0;
        s_axi_wvalid   = 1'b0;
        s_axi_bready   = 1'b0;
        s_axi_arvalid  = 1'b0;
        s_axi_rready   = 1'b0;
        
        // Apply reset
        #20;
        s_axi_aresetn = 1'b1;
        #20;
        
        $display("\n--- Test 1: I2C Write Transaction ---");
        
        // Configure I2C for 2-byte write
        axi_write(I2C_NBY, 32'd2);           // 2 bytes to transfer
        axi_write(I2C_ADR, {25'd0, slave_addr[6:0]});  // Slave address
        axi_write(I2C_TDR, 32'hDEADBEEF);    // Data to send
        
        // Check registers
        axi_read(I2C_NBY, read_data);
        $display("NBY register check: 0x%h", read_data);
        axi_read(I2C_ADR, read_data);
        $display("ADR register check: 0x%h", read_data);
        axi_read(I2C_TDR, read_data);
        $display("TDR register check: 0x%h", read_data);
        
        // Start slave response handler
        fork
            i2c_slave_response();
        join_none
        
        // Start transmission
        $display("\nStarting I2C transmission...");
        axi_write(I2C_CFG, 32'h00000001);    // Set transmit enable
        
        // Wait without polling
        $display("Waiting for transaction to complete...");
        #10000; // 10us wait
        
        // Check status once
        axi_read(I2C_CFG, read_data);
        $display("After 10us: CFG status = 0x%h", read_data);
        
        // Wait more if needed
        if (read_data[1:0] == 2'b01) begin
            // Still busy, wait more
            #10000;
            axi_read(I2C_CFG, read_data);
            $display("After 20us: CFG status = 0x%h", read_data);
        end
        
        // Final status
        if (read_data[1]) begin
            $display("SUCCESS: I2C Write transaction completed");
        end else begin
            $display("ERROR: I2C Write transaction failed");
        end
        
        // Clear status bit
        axi_write(I2C_CFG, 32'h00000000);
        
        #1000;
        
        $display("\n--- Test 2: Simple State Machine Test ---");
        
        // Just try to start and see if state changes
        axi_write(I2C_NBY, 32'd1);
        axi_write(I2C_ADR, 32'h50);
        axi_write(I2C_TDR, 32'h12345678);
        
        $display("Before start - State: %s", dut.state.name());
        axi_write(I2C_CFG, 32'h00000001);
        
        repeat(5) begin
            #50;
            $display("After %0t - State: %s, clk_cnt: %d, clk_en: %b", 
                    $time, dut.state.name(), dut.clk_cnt, dut.clk_en);
        end
        
        #1000;
        
        $display("\n--- All I2C Tests Completed ---");
        #100;
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #100000;
        $display("ERROR: Test timeout!");
        $finish;
    end
    
endmodule