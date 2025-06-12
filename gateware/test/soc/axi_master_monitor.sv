module axi_debug_slave #(
  parameter string LoggerName = "axi_slave_debugger"
)(
  input  logic clk_i,
  input  logic rst_ni,

  // AXI interface, Slave modport'u ile bağlanacak
  AXI_BUS.Slave axi
);

  // Internal registers
  logic aw_handshake, w_handshake, ar_handshake;

  // ready sinyalleri
  assign axi.aw_ready = 1'b1; // Her zaman hazır
  assign axi.w_ready  = 1'b1;
  assign axi.ar_ready = 1'b1;

  // b_valid üretimi (basit: AW + W sonrası tek cycle aktif)
  logic b_valid_reg;
  assign axi.b_valid = b_valid_reg;
  assign axi.b_id    = axi.aw_id;
  assign axi.b_resp  = '0;
  assign axi.b_user  = '0;

  // r_valid üretimi (basit: AR sonrası tek cycle aktif)
  logic r_valid_reg;
  assign axi.r_valid = r_valid_reg;
  assign axi.r_id    = axi.ar_id;
  assign axi.r_data  = 'hDEADBEEF; // dummy data
  assign axi.r_resp  = '0;
  assign axi.r_last  = 1'b1;
  assign axi.r_user  = '0;

  // AW + W + AR takibi ve yanıt üretimi
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      b_valid_reg <= 1'b0;
      r_valid_reg <= 1'b0;
    end else begin
      // Address Write
      if (axi.aw_valid && axi.aw_ready) begin
        $display("[%0t] %s: AW - Addr: 0x%08x ID: %0d Len: %0d Size: %0d",
          $time, LoggerName, axi.aw_addr, axi.aw_id, axi.aw_len, axi.aw_size);
      end

      // Write Data
      if (axi.w_valid && axi.w_ready) begin
        $display("[%0t] %s: W  - Data: 0x%h Strb: 0x%x Last: %b",
          $time, LoggerName, axi.w_data, axi.w_strb, axi.w_last);
      end

      // B response (tek cycle yüksek)
      if ((axi.aw_valid && axi.aw_ready) && (axi.w_valid && axi.w_ready)) begin
        b_valid_reg <= 1'b1;
      end else if (axi.b_valid && axi.b_ready) begin
        b_valid_reg <= 1'b0;
      end

      // Address Read
      if (axi.ar_valid && axi.ar_ready) begin
        $display("[%0t] %s: AR - Addr: 0x%08x ID: %0d Len: %0d Size: %0d",
          $time, LoggerName, axi.ar_addr, axi.ar_id, axi.ar_len, axi.ar_size);
        r_valid_reg <= 1'b1;
      end else if (axi.r_valid && axi.r_ready) begin
        r_valid_reg <= 1'b0;
      end
    end
  end

endmodule
