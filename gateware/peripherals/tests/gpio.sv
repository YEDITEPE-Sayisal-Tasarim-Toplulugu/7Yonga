module gpio (
    // Clock and reset signals
    input  logic        s_axi_aclk,
    input  logic        s_axi_aresetn,
    
    // AXI4-Lite Slave Interface
    // Write Address Channel
    input  logic [31:0] s_axi_awaddr,
    input  logic        s_axi_awvalid,
    output logic        s_axi_awready,
    
    // Write Data Channel
    input  logic [31:0] s_axi_wdata,
    input  logic [3:0]  s_axi_wstrb,
    input  logic        s_axi_wvalid,
    output logic        s_axi_wready,
    
    // Write Response Channel
    output logic [1:0]  s_axi_bresp,
    output logic        s_axi_bvalid,
    input  logic        s_axi_bready,
    
    // Read Address Channel
    input  logic [31:0] s_axi_araddr,
    input  logic        s_axi_arvalid,
    output logic        s_axi_arready,
    
    // Read Data Channel
    output logic [31:0] s_axi_rdata,
    output logic [1:0]  s_axi_rresp,
    output logic        s_axi_rvalid,
    input  logic        s_axi_rready,
    
    // GPIO pins
    input  logic [15:0] gpio_in,     // 16 input pins
    output logic [15:0] gpio_out     // 16 output pins
);
    // Register addresses - as defined in specification
    localparam GPIO_IDR = 8'h00; // Input data register
    localparam GPIO_ODR = 8'h04; // Output data register
    
    // Register definitions
    logic [31:0] gpio_idr_reg;  // Input data register
    logic [31:0] gpio_odr_reg;  // Output data register
    
    // AXI handshake helper variables
    logic        aw_en;
    logic [31:0] axi_awaddr;
    logic [31:0] axi_araddr;
    
    //----------------------------------------------------------------------
    // GPIO signal assignments
    //----------------------------------------------------------------------
    // Connect GPIO pins to registers
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            gpio_idr_reg <= 32'h0;
        end else begin
            // Update input register with incoming GPIO signals
            gpio_idr_reg <= {16'h0, gpio_in}; // Upper 16 bits are always 0
        end
    end
    
    // Connect output register to GPIO output pins
    assign gpio_out = gpio_odr_reg[15:0];
    
    //----------------------------------------------------------------------
    // AXI4-Lite Interface - Write Channel
    //----------------------------------------------------------------------
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_awready <= 1'b0;
            s_axi_wready  <= 1'b0;
            s_axi_bvalid  <= 1'b0;
            s_axi_bresp   <= 2'b00;
            aw_en         <= 1'b1;
            axi_awaddr    <= 32'd0;
            
            // Register reset
            gpio_odr_reg <= 32'd0;
        end else begin
            // AWREADY (address acceptance)
            if (!s_axi_awready && s_axi_awvalid && s_axi_wvalid && aw_en) begin
                s_axi_awready <= 1'b1;
                axi_awaddr    <= s_axi_awaddr;
                aw_en         <= 1'b0;
            end else if (s_axi_bready && s_axi_bvalid) begin
                s_axi_awready <= 1'b0;
                aw_en         <= 1'b1;
            end
            
            // WREADY (data acceptance)
            if (!s_axi_wready && s_axi_wvalid && s_axi_awvalid && aw_en) begin
                s_axi_wready <= 1'b1;
            end else begin
                s_axi_wready <= 1'b0;
            end
            
            // Write response
            if (s_axi_awready && s_axi_awvalid && !s_axi_bvalid && s_axi_wready && s_axi_wvalid) begin
                s_axi_bvalid <= 1'b1;
                s_axi_bresp  <= 2'b00; // OKAY
            end else if (s_axi_bvalid && s_axi_bready) begin
                s_axi_bvalid <= 1'b0;
            end
            
            // Register write operation - only when address and data are ready
            if (s_axi_awready && s_axi_awvalid && s_axi_wready && s_axi_wvalid) begin
                case (axi_awaddr[7:0])
                    GPIO_ODR: begin
                        // Only process writes to ODR register (IDR is read-only)
                        // Only lower 16 bits are used for output
                        gpio_odr_reg <= s_axi_wdata;
                        $display("GPIO: ODR updated with 0x%h", s_axi_wdata);
                    end
                    default: ; // Do nothing for other addresses
                endcase
            end
        end
    end

    //----------------------------------------------------------------------
    // AXI4-Lite Interface - Read Channel
    //----------------------------------------------------------------------
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_arready <= 1'b0;
            s_axi_rvalid  <= 1'b0;
            s_axi_rresp   <= 2'b00;
            axi_araddr    <= 32'd0;
        end else begin
            // ARREADY (read address acceptance)
            if (!s_axi_arready && s_axi_arvalid) begin
                s_axi_arready <= 1'b1;
                axi_araddr    <= s_axi_araddr;
            end else begin
                s_axi_arready <= 1'b0;
            end
            
            // RVALID (read data ready)
            if (s_axi_arready && s_axi_arvalid && !s_axi_rvalid) begin
                s_axi_rvalid <= 1'b1;
                s_axi_rresp  <= 2'b00; // OKAY
                
                // Register read
                case (axi_araddr[7:0])
                    GPIO_IDR: begin
                        s_axi_rdata <= gpio_idr_reg;
                        $display("GPIO: Reading IDR = 0x%h", gpio_idr_reg);
                    end
                    
                    GPIO_ODR: begin
                        s_axi_rdata <= gpio_odr_reg;
                        $display("GPIO: Reading ODR = 0x%h", gpio_odr_reg);
                    end
                    
                    default: begin
                        s_axi_rdata <= 32'd0;
                        $display("GPIO: Reading unknown address 0x%h", axi_araddr);
                    end
                endcase
            end else if (s_axi_rvalid && s_axi_rready) begin
                s_axi_rvalid <= 1'b0;
            end
        end
    end
    
endmodule