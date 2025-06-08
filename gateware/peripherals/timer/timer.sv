module timer (
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
    input  logic        s_axi_rready
);
    // Register addresses - as defined in the specification
    localparam TIM_PRE = 8'h00; // Prescaler register
    localparam TIM_ARE = 8'h04; // Auto-reload register
    localparam TIM_CLR = 8'h08; // Clear register
    localparam TIM_ENA = 8'h0C; // Enable register
    localparam TIM_MOD = 8'h10; // Mode register
    localparam TIM_CNT = 8'h14; // Counter register (Read-only)
    localparam TIM_EVN = 8'h18; // Event register (Read-only)
    localparam TIM_EVC = 8'h1C; // Event clear register
    
    // Register definitions
    logic [31:0] tim_pre_reg; // Prescaler register
    logic [31:0] tim_are_reg; // Auto-reload register
    logic        tim_clr_reg; // Clear register (only bit 0 used)
    logic        tim_ena_reg; // Enable register (only bit 0 used)
    logic        tim_mod_reg; // Mode register (only bit 0 used)
    logic [31:0] tim_cnt_reg; // Counter register
    logic [31:0] tim_evn_reg; // Event register
    logic        tim_evc_reg; // Event clear register (only bit 0 used)
    
    // Internal signals
    logic [31:0] prescaler_counter;   // Prescaler counter
    logic count_tick;                 // Tick signal for the counter
    logic auto_reload_event;          // Auto-reload event trigger
    logic first_load;                 // Flag to track first load in down-counting mode
    
    // AXI handshake helper variables
    logic        aw_en;
    logic [31:0] axi_awaddr;
    logic [31:0] axi_araddr;
    
    //----------------------------------------------------------------------
    // Prescaler and Tick Generation
    //----------------------------------------------------------------------
    
    // Generate tick for counter based on prescaler
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            prescaler_counter <= 32'd0;
            count_tick <= 1'b0;
        end else begin
            // Default state
            count_tick <= 1'b0;
            
            if (!tim_ena_reg || tim_clr_reg) begin
                // Reset prescaler counter when timer is disabled or cleared
                prescaler_counter <= 32'd0;
            end else begin
                // Normal prescaler operation
                if (prescaler_counter >= tim_pre_reg) begin
                    prescaler_counter <= 32'd0;
                    count_tick <= 1'b1;
                end else begin
                    prescaler_counter <= prescaler_counter + 1;
                end
            end
        end
    end
    
    //----------------------------------------------------------------------
    // Counter Logic
    //----------------------------------------------------------------------
    
    // Counter and event logic
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            tim_cnt_reg <= 32'd0;
            auto_reload_event <= 1'b0;
            first_load <= 1'b1;
        end else begin
            // Default state
            auto_reload_event <= 1'b0;
            
            // Handle clear request (highest priority)
            if (tim_clr_reg) begin
                tim_cnt_reg <= 32'd0;
                first_load <= 1'b1;  // Reset first load flag on clear
            end
            // When timer is enabled
            else if (tim_ena_reg) begin
                // Normal counting operation with tick
                if (count_tick) begin
                    if (tim_mod_reg) begin
                        // Up-counting mode
                        if (tim_cnt_reg == tim_are_reg) begin
                            tim_cnt_reg <= 32'd0;
                            auto_reload_event <= 1'b1;
                        end else begin
                            tim_cnt_reg <= tim_cnt_reg + 1;
                        end
                    end else begin
                        // Down-counting mode
                        if (tim_cnt_reg == 32'd0) begin
                            tim_cnt_reg <= tim_are_reg;
                            auto_reload_event <= !first_load;  // Generate event only if not first load
                            first_load <= 1'b0;  // Clear first load flag
                        end else begin
                            tim_cnt_reg <= tim_cnt_reg - 1;
                        end
                    end
                end
                // Special case: When counter is 0 in down-counting mode (no tick)
                else if (tim_cnt_reg == 32'd0 && !tim_mod_reg) begin
                    tim_cnt_reg <= tim_are_reg;
                    auto_reload_event <= !first_load;  // Generate event only if not first load
                    first_load <= 1'b0;  // Clear first load flag
                end
            end
            else begin
                // When timer is disabled
                // Reset first_load flag so next enable will be treated as first load
                first_load <= 1'b1;
            end
        end
    end
    
    //----------------------------------------------------------------------
    // Event Counter Logic
    //----------------------------------------------------------------------
    
    // Event counter logic
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            tim_evn_reg <= 32'd0;
        end else begin
            // Clear event counter if requested
            if (tim_evc_reg) begin
                tim_evn_reg <= 32'd0;
            end
            // Increment event counter on auto-reload event
            else if (auto_reload_event) begin
                tim_evn_reg <= tim_evn_reg + 1;
            end
        end
    end
    
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
            tim_pre_reg <= 32'd0;
            tim_are_reg <= 32'd0;
            tim_clr_reg <= 1'b0;
            tim_ena_reg <= 1'b0;
            tim_mod_reg <= 1'b0;
            tim_evc_reg <= 1'b0;
        end else begin
            // Clear the one-shot registers
            tim_clr_reg <= 1'b0;
            tim_evc_reg <= 1'b0;
            
            // AWREADY (address acceptance)
            if (!s_axi_awready && s_axi_awvalid && s_axi_wvalid && aw_en) begin
                s_axi_awready <= 1'b1;
                axi_awaddr    <= s_axi_awaddr;
                aw_en         <= 1'b0;
            end else if (s_axi_bready && s_axi_bvalid) begin
                s_axi_awready <= 1'b0;
                aw_en         <= 1'b1;
            end else begin
                s_axi_awready <= 1'b0;
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
                    TIM_PRE: begin
                        tim_pre_reg <= s_axi_wdata;
                        $display("Timer: PRE updated with 0x%08h", s_axi_wdata);
                    end
                    TIM_ARE: begin
                        tim_are_reg <= s_axi_wdata;
                        $display("Timer: ARE updated with 0x%08h", s_axi_wdata);
                    end
                    TIM_CLR: begin
                        tim_clr_reg <= s_axi_wdata[0];
                        $display("Timer: CLR updated with 0x%08h", s_axi_wdata);
                    end
                    TIM_ENA: begin
                        tim_ena_reg <= s_axi_wdata[0];
                        $display("Timer: ENA updated with 0x%08h", s_axi_wdata);
                    end
                    TIM_MOD: begin
                        tim_mod_reg <= s_axi_wdata[0];
                        $display("Timer: MOD updated with 0x%08h", s_axi_wdata);
                    end
                    TIM_EVC: begin
                        tim_evc_reg <= s_axi_wdata[0];
                        $display("Timer: EVC updated with 0x%08h", s_axi_wdata);
                    end
                    // TIM_CNT and TIM_EVN are read-only, ignore writes
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
            s_axi_rdata   <= 32'd0;
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
                    TIM_PRE: begin
                        s_axi_rdata <= tim_pre_reg;
                        $display("Timer: Reading PRE = 0x%08h", tim_pre_reg);
                    end
                    TIM_ARE: begin
                        s_axi_rdata <= tim_are_reg;
                        $display("Timer: Reading ARE = 0x%08h", tim_are_reg);
                    end
                    TIM_CLR: begin
                        s_axi_rdata <= {31'd0, tim_clr_reg};
                        $display("Timer: Reading CLR = 0x%08h", {31'd0, tim_clr_reg});
                    end
                    TIM_ENA: begin
                        s_axi_rdata <= {31'd0, tim_ena_reg};
                        $display("Timer: Reading ENA = 0x%08h", {31'd0, tim_ena_reg});
                    end
                    TIM_MOD: begin
                        s_axi_rdata <= {31'd0, tim_mod_reg};
                        $display("Timer: Reading MOD = 0x%08h", {31'd0, tim_mod_reg});
                    end
                    TIM_CNT: begin
                        s_axi_rdata <= tim_cnt_reg;
                        $display("Timer: Reading CNT = 0x%08h", tim_cnt_reg);
                    end
                    TIM_EVN: begin
                        s_axi_rdata <= tim_evn_reg;
                        $display("Timer: Reading EVN = 0x%08h", tim_evn_reg);
                    end
                    TIM_EVC: begin
                        s_axi_rdata <= {31'd0, tim_evc_reg};
                        $display("Timer: Reading EVC = 0x%08h", {31'd0, tim_evc_reg});
                    end
                    default: begin
                        s_axi_rdata <= 32'd0;
                        $display("Timer: Reading unknown address 0x%08h", axi_araddr);
                    end
                endcase
            end else if (s_axi_rvalid && s_axi_rready) begin
                s_axi_rvalid <= 1'b0;
            end
        end
    end
    
endmodule