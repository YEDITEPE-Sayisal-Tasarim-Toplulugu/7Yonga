`timescale 1ns / 1ps

// QSPI Master Testbench
module qspi_master_tb;

    // Parameters
    parameter CLK_PERIOD = 10; // 100MHz clock
    parameter AXI_ADDR_WIDTH = 32;
    parameter AXI_DATA_WIDTH = 32;
    
    // Signals
    logic                        clk_i;
    logic                        rst_ni;
    
    // AXI4-Lite Slave Interface
    logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr;
    logic                        s_axi_awvalid;
    logic                        s_axi_awready;
    logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata;
    logic [3:0]                  s_axi_wstrb;
    logic                        s_axi_wvalid;
    logic                        s_axi_wready;
    logic [1:0]                  s_axi_bresp;
    logic                        s_axi_bvalid;
    logic                        s_axi_bready;
    logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr;
    logic                        s_axi_arvalid;
    logic                        s_axi_arready;
    logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata;
    logic [1:0]                  s_axi_rresp;
    logic                        s_axi_rvalid;
    logic                        s_axi_rready;
    
    // QSPI Interface
    logic                        qspi_sclk_o;
    logic                        qspi_cs_no;
    logic [3:0]                  qspi_data_o;
    logic [3:0]                  qspi_data_i;
    logic [3:0]                  qspi_data_oen;
    
    // Flash memory model signals
    logic [3:0]                  flash_data_o;
    logic [3:0]                  flash_data_i;
    
    // DUT Instance
    qspi_master #(
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
    ) dut (
        .clk_i          (clk_i),
        .rst_ni         (rst_ni),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),
        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),
        .qspi_sclk_o    (qspi_sclk_o),
        .qspi_cs_no     (qspi_cs_no),
        .qspi_data_o    (qspi_data_o),
        .qspi_data_i    (qspi_data_i),
        .qspi_data_oen  (qspi_data_oen)
    );
    
    // Clock generation
    initial begin
        clk_i = 0;
        forever #(CLK_PERIOD/2) clk_i = ~clk_i;
    end
    
    // Simple Flash Memory Model
    logic [7:0] flash_memory [0:1023]; // 1KB flash memory
    logic [23:0] flash_addr;
    logic [7:0] flash_cmd;
    logic [2:0] flash_state;
    logic [7:0] flash_rx_data;
    logic [7:0] flash_tx_data;
    logic [2:0] flash_bit_cnt;
    logic [2:0] flash_addr_byte_cnt;
    logic [9:0] flash_byte_cnt; // Counter for multi-byte reads
    logic flash_write_enable = 1'b0; // Initialize at declaration
    
    // Flash states
    localparam FLASH_IDLE = 3'd0;
    localparam FLASH_CMD = 3'd1;
    localparam FLASH_ADDR = 3'd2;
    localparam FLASH_READ_DATA = 3'd3;
    localparam FLASH_WRITE_DATA = 3'd4;
    
    // Flash commands
    localparam CMD_READ = 8'h03;
    localparam CMD_PP = 8'h02;
    localparam CMD_WREN = 8'h06;
    localparam CMD_WRDI = 8'h04;
    localparam CMD_RDSR1 = 8'h05;
    localparam CMD_DOR = 8'h3B;
    localparam CMD_QOR = 8'h6B;
    localparam CMD_QPP = 8'h32;
    
    // Flash data connections
    assign flash_data_i = qspi_data_o;
    assign qspi_data_i = flash_data_o;
    
    // Flash memory behavior
    always_ff @(posedge qspi_sclk_o or posedge qspi_cs_no) begin
        if (qspi_cs_no) begin
            flash_state <= FLASH_IDLE;
            flash_bit_cnt <= 3'd0;
            flash_addr_byte_cnt <= 3'd0;
            flash_rx_data <= 8'h00;
            flash_addr <= 24'h000000;
            flash_byte_cnt <= 10'd0;
            flash_tx_data <= 8'h00;
            // Check if we just completed a write operation
            if (flash_state == FLASH_WRITE_DATA && flash_write_enable) begin
                flash_write_enable <= 1'b0; // Clear WEL after write
            end
        end else begin
            case (flash_state)
                FLASH_IDLE: begin
                    flash_state <= FLASH_CMD;
                    flash_bit_cnt <= 3'd0;
                end
                
                FLASH_CMD: begin
                    flash_rx_data <= {flash_rx_data[6:0], flash_data_i[0]};
                    flash_bit_cnt <= flash_bit_cnt + 1'b1;
                    
                    if (flash_bit_cnt == 3'd7) begin
                        flash_cmd <= {flash_rx_data[6:0], flash_data_i[0]};
                        flash_bit_cnt <= 3'd0;
                        
                        case ({flash_rx_data[6:0], flash_data_i[0]})
                            CMD_WREN, CMD_WRDI: begin
                                flash_state <= FLASH_IDLE;
                                $display("Flash: %s command received", 
                                        ({flash_rx_data[6:0], flash_data_i[0]} == CMD_WREN) ? "WREN" : "WRDI");
                            end
                            CMD_READ, CMD_PP, CMD_DOR, CMD_QOR, CMD_QPP: flash_state <= FLASH_ADDR;
                            CMD_RDSR1: begin
                                flash_state <= FLASH_READ_DATA;
                                flash_tx_data <= {7'b0, flash_write_enable}; // Status register with WEL bit
                            end
                            default: flash_state <= FLASH_IDLE;
                        endcase
                        
                        // Handle write enable/disable commands
                        if ({flash_rx_data[6:0], flash_data_i[0]} == CMD_WREN) begin
                            flash_write_enable <= 1'b1;
                        end else if ({flash_rx_data[6:0], flash_data_i[0]} == CMD_WRDI) begin
                            flash_write_enable <= 1'b0;
                        end
                    end
                end
                
                FLASH_ADDR: begin
                    flash_rx_data <= {flash_rx_data[6:0], flash_data_i[0]};
                    flash_bit_cnt <= flash_bit_cnt + 1'b1;
                    
                    if (flash_bit_cnt == 3'd7) begin
                        flash_bit_cnt <= 3'd0;
                        case (flash_addr_byte_cnt)
                            3'd0: flash_addr[23:16] <= {flash_rx_data[6:0], flash_data_i[0]};
                            3'd1: flash_addr[15:8] <= {flash_rx_data[6:0], flash_data_i[0]};
                            3'd2: begin
                                flash_addr[7:0] <= {flash_rx_data[6:0], flash_data_i[0]};
                                if (flash_cmd == CMD_READ || flash_cmd == CMD_DOR || flash_cmd == CMD_QOR) begin
                                    flash_state <= FLASH_READ_DATA;
                                    flash_byte_cnt <= 10'd0;
                                    // Calculate the complete address
                                    flash_tx_data <= flash_memory[{flash_addr[15:8], flash_rx_data[6:0], flash_data_i[0]}];
                                    $display("Flash Read Start: addr=0x%03x, first_byte=0x%02x", 
                                             {flash_addr[15:8], flash_rx_data[6:0], flash_data_i[0]}, 
                                             flash_memory[{flash_addr[15:8], flash_rx_data[6:0], flash_data_i[0]}]);
                                end else if (flash_cmd == CMD_PP || flash_cmd == CMD_QPP) begin
                                    flash_state <= FLASH_WRITE_DATA;
                                    flash_byte_cnt <= 10'd0;
                                end
                            end
                        endcase
                        flash_addr_byte_cnt <= flash_addr_byte_cnt + 1'b1;
                    end
                end
                
                FLASH_READ_DATA: begin
                    // Handle different read modes
                    case (flash_cmd)
                        CMD_READ, CMD_RDSR1: begin
                            flash_bit_cnt <= flash_bit_cnt + 1'b1;
                            if (flash_bit_cnt == 3'd7) begin
                                flash_bit_cnt <= 3'd0;
                                if (flash_byte_cnt < 10'd8) begin  // Read up to 8 bytes
                                    flash_byte_cnt <= flash_byte_cnt + 1'b1;
                                    if (flash_byte_cnt < 10'd7) begin
                                        flash_tx_data <= flash_memory[(flash_addr[9:0] + flash_byte_cnt + 1'b1) & 10'h3FF];
                                    end
                                end
                            end
                        end
                        CMD_DOR: begin
                            flash_bit_cnt <= flash_bit_cnt + 3'd2; // 2 bits at a time
                            if (flash_bit_cnt >= 3'd6) begin
                                flash_bit_cnt <= 3'd0;
                                if (flash_byte_cnt < 10'd8) begin
                                    flash_byte_cnt <= flash_byte_cnt + 1'b1;
                                    if (flash_byte_cnt < 10'd7) begin
                                        flash_tx_data <= flash_memory[(flash_addr[9:0] + flash_byte_cnt + 1'b1) & 10'h3FF];
                                    end
                                end
                            end
                        end
                        CMD_QOR: begin
                            flash_bit_cnt <= flash_bit_cnt + 3'd4; // 4 bits at a time
                            if (flash_bit_cnt >= 3'd4) begin
                                flash_bit_cnt <= 3'd0;
                                if (flash_byte_cnt < 10'd8) begin
                                    flash_byte_cnt <= flash_byte_cnt + 1'b1;
                                    if (flash_byte_cnt < 10'd7) begin
                                        flash_tx_data <= flash_memory[(flash_addr[9:0] + flash_byte_cnt + 1'b1) & 10'h3FF];
                                    end
                                end
                            end
                        end
                    endcase
                end
                
                FLASH_WRITE_DATA: begin
                    if (flash_write_enable) begin
                        // Handle different write modes
                        case (flash_cmd)
                            CMD_PP: begin // x1 mode
                                flash_rx_data <= {flash_rx_data[6:0], flash_data_i[0]};
                                flash_bit_cnt <= flash_bit_cnt + 1'b1;
                                
                                if (flash_bit_cnt == 3'd7) begin
                                    flash_memory[(flash_addr[9:0] + flash_byte_cnt) & 10'h3FF] <= {flash_rx_data[6:0], flash_data_i[0]};
                                    flash_byte_cnt <= flash_byte_cnt + 1'b1;
                                    flash_bit_cnt <= 3'd0;
                                    
                                    // Debug print for write with byte count
                                    $display("Flash Write: byte_cnt=%0d, addr=0x%03x, data=0x%02x", 
                                    flash_byte_cnt,
                                    (flash_addr[9:0] + flash_byte_cnt) & 10'h3FF, 
                                        {flash_rx_data[6:0], flash_data_i[0]});
                                end
                            end
                            CMD_QPP: begin // x4 mode
                                if (flash_bit_cnt[1:0] == 2'b00) begin
                                    flash_rx_data[7:4] <= flash_data_i[3:0];
                                end else begin
                                    flash_rx_data[3:0] <= flash_data_i[3:0];
                                end
                                flash_bit_cnt <= flash_bit_cnt + 3'd4;
                                
                                if (flash_bit_cnt >= 3'd4) begin
                                    flash_memory[(flash_addr[9:0] + flash_byte_cnt) & 10'h3FF] <= flash_rx_data;
                                    flash_byte_cnt <= flash_byte_cnt + 1'b1;
                                    flash_bit_cnt <= 3'd0;
                                end
                            end
                        endcase
                    end
                end
            endcase
        end
    end
    
    // Flash data output
    always_comb begin
        flash_data_o = 4'h0;
        
        if (!qspi_cs_no) begin
            if (flash_state == FLASH_READ_DATA) begin
                case (flash_cmd)
                    CMD_READ, CMD_RDSR1: begin
                        // x1 mode - output on bit 1 (SO)
                        flash_data_o[1] = flash_tx_data[7-flash_bit_cnt];
                    end
                    CMD_DOR: begin
                        // x2 mode - output on bits 1:0
                        case (flash_bit_cnt[2:1])
                            2'b00: flash_data_o[1:0] = flash_tx_data[7:6];
                            2'b01: flash_data_o[1:0] = flash_tx_data[5:4];
                            2'b10: flash_data_o[1:0] = flash_tx_data[3:2];
                            2'b11: flash_data_o[1:0] = flash_tx_data[1:0];
                        endcase
                    end
                    CMD_QOR: begin
                        // x4 mode - output on bits 3:0
                        case (flash_bit_cnt[2])
                            1'b0: flash_data_o[3:0] = flash_tx_data[7:4];
                            1'b1: flash_data_o[3:0] = flash_tx_data[3:0];
                        endcase
                    end
                endcase
            end
        end
    end
    
    // AXI4-Lite Write Task
    task axi_write(input [31:0] addr, input [31:0] data);
        @(posedge clk_i);
        s_axi_awaddr = addr;
        s_axi_awvalid = 1'b1;
        s_axi_wdata = data;
        s_axi_wstrb = 4'hF;
        s_axi_wvalid = 1'b1;
        s_axi_bready = 1'b1;
        
        fork
            begin
                wait(s_axi_awready);
                @(posedge clk_i);
                s_axi_awvalid = 1'b0;
            end
            begin
                wait(s_axi_wready);
                @(posedge clk_i);
                s_axi_wvalid = 1'b0;
            end
        join
        
        wait(s_axi_bvalid);
        @(posedge clk_i);
        s_axi_bready = 1'b0;
    endtask
    
    // AXI4-Lite Read Task
    task axi_read(input [31:0] addr, output [31:0] data);
        @(posedge clk_i);
        s_axi_araddr = addr;
        s_axi_arvalid = 1'b1;
        s_axi_rready = 1'b1;
        
        wait(s_axi_arready);
        @(posedge clk_i);
        s_axi_arvalid = 1'b0;
        
        wait(s_axi_rvalid);
        data = s_axi_rdata;
        @(posedge clk_i);
        s_axi_rready = 1'b0;
    endtask
    
    // Wait for transaction complete
    task wait_transaction_complete();
        logic [31:0] status;
        do begin
            axi_read(32'h28, status);
            #100;
        end while (status[1] == 1'b1); // Wait while busy
    endtask
    
    // Test variables
    logic [31:0] read_data;
    logic [31:0] dr0_read, dr1_read;
    
    // Test stimulus
    initial begin
        
        // Initialize signals
        rst_ni = 1'b0;
        s_axi_awaddr = '0;
        s_axi_awvalid = 1'b0;
        s_axi_wdata = '0;
        s_axi_wstrb = '0;
        s_axi_wvalid = 1'b0;
        s_axi_bready = 1'b0;
        s_axi_araddr = '0;
        s_axi_arvalid = 1'b0;
        s_axi_rready = 1'b0;
        // flash_write_enable = 1'b0; // Remove this - it's handled in always_ff block
        
        // Initialize flash memory with pattern for testing
        for (int i = 0; i < 1024; i++) begin
            flash_memory[i] = 8'h00;
        end
        
        // Pre-load some test data at specific addresses
        // This helps verify read operations work correctly
        // Don't pre-load at 0x100 since we'll write there
        
        // Debug: Print initial DR values
        $display("\nInitial Data Register values:");
        for (int i = 0; i < 8; i++) begin
            $display("  DR[%0d] = 0x%08x", i, dut.qspi_dr[i]);
        end
        
        // Reset sequence
        #100;
        rst_ni = 1'b1;
        #100;
        
        $display("Starting QSPI Master Tests...");
        
        // Test 1: Write Enable Command
        $display("\nTest 1: Write Enable Command (WREN)");
        axi_write(32'h00, {1'b0, 6'd0, 9'd0, 5'd0, 1'b1, 2'b00, 8'h06}); // WREN command
        wait_transaction_complete();
        $display("Write Enable sent");
        
        // Verify WEL bit is set by reading status register
        #100; // Small delay
        axi_write(32'h00, {1'b0, 6'd0, 9'd0, 5'd0, 1'b0, 2'b01, 8'h05}); // RDSR1
        wait_transaction_complete();
        axi_read(32'h08, read_data);
        $display("Status Register after WREN = 0x%02h (WEL bit should be 1)", read_data[7:0]);
        
        // Test 2: Page Program (x1 mode)
        $display("\nTest 2: Page Program in x1 mode");
        // Set address
        axi_write(32'h04, 24'h000100); // Address 0x000100
        // Set test data - note byte order for verification
        // DR0 = 0x01234567 -> bytes: 67, 45, 23, 01
        // DR1 = 0x89ABCDEF -> bytes: EF, CD, AB, 89
        axi_write(32'h08, 32'h01234567); // DR0
        axi_write(32'h0C, 32'h89ABCDEF); // DR1
        // Clear other data registers
        for (int i = 2; i < 8; i++) begin
            axi_write(32'h08 + i*4, 32'h00000000);
        end
        
        // Debug: Print DR values after write but before PP command
        $display("\nData Register values after AXI write:");
        for (int i = 0; i < 8; i++) begin
            axi_read(32'h08 + i*4, read_data);
            $display("  DR[%0d] = 0x%08x", i, read_data);
        end
        
        // Send PP command: instruction=0x02, data_mode=x1, write=1, data_length=7 (8 bytes)
        axi_write(32'h00, {1'b0, 6'd0, 9'd7, 5'd0, 1'b1, 2'b01, 8'h02});
        wait_transaction_complete();
        $display("Page Program completed");
        
        // Debug: Print actual byte transfer sequence
        $display("\nExpected byte sequence:");
        $display("  Byte 0: 0x67 (from DR0[7:0])");
        $display("  Byte 1: 0x45 (from DR0[15:8])");
        $display("  Byte 2: 0x23 (from DR0[23:16])");
        $display("  Byte 3: 0x01 (from DR0[31:24])");
        $display("  Byte 4: 0xEF (from DR1[7:0])");
        $display("  Byte 5: 0xCD (from DR1[15:8])");
        $display("  Byte 6: 0xAB (from DR1[23:16])");
        $display("  Byte 7: 0x89 (from DR1[31:24])");
        
        // Add delay to ensure flash write completes
        #100;
        
        // Test 3: Read Data (x1 mode)
        $display("\nTest 3: Read Data in x1 mode");
        // Set address
        axi_write(32'h04, 24'h000100); // Address 0x000100
        
        // Debug: Clear data registers before read
        for (int i = 0; i < 8; i++) begin
            axi_write(32'h08 + i*4, 32'h00000000);
        end
        
        // Send READ command: instruction=0x03, data_mode=x1, read=0, data_length=7 (8 bytes)
        axi_write(32'h00, {1'b0, 6'd0, 9'd7, 5'd0, 1'b0, 2'b01, 8'h03});
        wait_transaction_complete();
        
        // Read back data
        axi_read(32'h08, dr0_read);
        $display("DR0 = 0x%08h (expected: 0x01234567)", dr0_read);
        axi_read(32'h0C, dr1_read);
        $display("DR1 = 0x%08h (expected: 0x89ABCDEF)", dr1_read);
        
        // Debug: Print expected vs actual byte values
        $display("\nExpected vs Actual byte values:");
        $display("  Byte 0: expected=0x67, actual=0x%02x", dr0_read[7:0]);
        $display("  Byte 1: expected=0x45, actual=0x%02x", dr0_read[15:8]);
        $display("  Byte 2: expected=0x23, actual=0x%02x", dr0_read[23:16]);
        $display("  Byte 3: expected=0x01, actual=0x%02x", dr0_read[31:24]);
        $display("  Byte 4: expected=0xEF, actual=0x%02x", dr1_read[7:0]);
        $display("  Byte 5: expected=0xCD, actual=0x%02x", dr1_read[15:8]);
        $display("  Byte 6: expected=0xAB, actual=0x%02x", dr1_read[23:16]);
        $display("  Byte 7: expected=0x89, actual=0x%02x", dr1_read[31:24]);
        
        // Debug: Print all DR values after read
        $display("\nData Register values after read:");
        for (int i = 0; i < 8; i++) begin
            axi_read(32'h08 + i*4, read_data);
            $display("  DR[%0d] = 0x%08x", i, read_data);
        end
        
        // Verify the data
        if (dr0_read == 32'h01234567 && dr1_read == 32'h89ABCDEF) begin
            $display("Read test PASSED!");
        end else begin
            $display("Read test FAILED!");
            $display("Flash memory contents at 0x100-0x107:");
            for (int i = 0; i < 8; i++) begin
                $display("  [0x%03x] = 0x%02x", 256+i, flash_memory[256+i]);
            end
        end
        
        // Test 4: Dual Read (x2 mode)
        $display("\nTest 4: Dual Output Read (DOR) in x2 mode");
        axi_write(32'h04, 24'h000100);
        // DOR command with 8 dummy cycles
        axi_write(32'h00, {1'b0, 6'd0, 9'd7, 5'd8, 1'b0, 2'b10, 8'h3B});
        wait_transaction_complete();
        
        axi_read(32'h08, read_data);
        $display("DR0 (DOR) = 0x%08h", read_data);
        
        // Test 5: Quad Read (x4 mode)
        $display("\nTest 5: Quad Output Read (QOR) in x4 mode");
        axi_write(32'h04, 24'h000100);
        // QOR command with 8 dummy cycles
        axi_write(32'h00, {1'b0, 6'd0, 9'd7, 5'd8, 1'b0, 2'b11, 8'h6B});
        wait_transaction_complete();
        
        axi_read(32'h08, read_data);
        $display("DR0 (QOR) = 0x%08h", read_data);
        
        // Test 6: Read Status Register
        $display("\nTest 6: Read Status Register 1");
        axi_write(32'h00, {1'b0, 6'd0, 9'd0, 5'd0, 1'b0, 2'b01, 8'h05}); // RDSR1
        wait_transaction_complete();
        
        axi_read(32'h08, read_data);
        $display("Status Register = 0x%02h", read_data[7:0]);
        
        // Test with different prescaler values
        $display("\nTest 7: Test with different prescaler (slower clock)");
        axi_write(32'h04, 24'h000200);
        // Set prescaler to 4 (divide by 5)
        axi_write(32'h00, {1'b0, 6'd4, 9'd3, 5'd0, 1'b0, 2'b01, 8'h03});
        wait_transaction_complete();
        
        $display("\nAll tests completed!");
        
        // Final memory dump for verification
        $display("\nFinal flash memory contents at address 0x100-0x107:");
        for (int i = 0; i < 8; i++) begin
            $display("  [0x%03x] = 0x%02x", 256+i, flash_memory[256+i]);
        end
        
        #1000;
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0t CS=%b SCLK=%b DO=%h DI=%h OEN=%h", 
                 $time, qspi_cs_no, qspi_sclk_o, qspi_data_o, qspi_data_i, qspi_data_oen);
    end
    
    // Waveform dump
    initial begin
        $dumpfile("qspi_master_tb.vcd");
        $dumpvars(0, qspi_master_tb);
    end

endmodule