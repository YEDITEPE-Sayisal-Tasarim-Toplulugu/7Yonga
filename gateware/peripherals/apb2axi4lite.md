APB'den AXI4-Lite'a UART Dönüşüm Rehberi
Bu doküman, çalışan APB tabanlı UART modülünü AXI4-Lite protokolüne dönüştürme sürecini açıklar. Dönüşüm yaparken dikkat edilmesi gereken değişiklikler ve tasarım kararları burada belirtilmiştir.
1. Protokol Farklılıkları
APB Protokolü

Basit, adres + veri + kontrol sinyalleri
Tek bir setup ve access fazı
psel, penable, pwrite, pready sinyalleri ile kontrol

AXI4-Lite Protokolü

5 ayrı kanal (Yazma Adresi, Yazma Verisi, Yazma Yanıtı, Okuma Adresi, Okuma Verisi)
Daha karmaşık handshaking mekanizması
Her kanal için ayrı valid/ready sinyalleri
Yanıt kanalları ile hata durumlarını belirtme imkanı

2. Yapılan Temel Değişiklikler
2.1. Port Listesi Değişimi
verilog// APB
input  logic        clk,
input  logic        rst_n,
input  logic        psel,
input  logic        penable,
input  logic        pwrite,
input  logic [31:0] paddr,
input  logic [31:0] pwdata,
output logic [31:0] prdata,
output logic        pready,

// AXI4-Lite
input  logic        s_axi_aclk,
input  logic        s_axi_aresetn,
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
2.2. Register Erişim Mekanizması
APB implementasyonunda register erişimi:
verilog// Register yazma
if (psel && penable && pwrite) begin
    pready <= 1'b1;
    case (paddr[7:0])
        // Register yazma işlemleri
    endcase
end

// Register okuma
else if (psel && penable && !pwrite) begin
    pready <= 1'b1;
end
AXI4-Lite implementasyonunda register erişimi:
verilog// Adres kabul etme
if (!s_axi_awready && s_axi_awvalid && s_axi_wvalid && aw_en) begin
    s_axi_awready <= 1'b1;
    axi_awaddr    <= s_axi_awaddr;
    aw_en         <= 1'b0;
end

// Veri kabul etme
if (!s_axi_wready && s_axi_wvalid && s_axi_awvalid && aw_en) begin
    s_axi_wready <= 1'b1;
end

// Register yazma
if (s_axi_awready && s_axi_awvalid && s_axi_wready && s_axi_wvalid) begin
    case (axi_awaddr[7:0])
        // Register yazma işlemleri
    endcase
end
2.3. Handshaking Mekanizmaları
APB protokolünde handshaking:
verilogpready <= 1'b1; // İşlem tamamlandı
AXI4-Lite protokolünde handshaking:
verilog// Yazma işlemi tamamlandı
s_axi_bvalid <= 1'b1;
s_axi_bresp  <= 2'b00; // OKAY

// Yazma yanıtı kabul edildi
if (s_axi_bvalid && s_axi_bready) begin
    s_axi_bvalid <= 1'b0;
end

// Okuma işlemi tamamlandı
s_axi_rvalid <= 1'b1;
s_axi_rresp  <= 2'b00; // OKAY

// Okuma verisi kabul edildi
if (s_axi_rvalid && s_axi_rready) begin
    s_axi_rvalid <= 1'b0;
end
3. UART Mantığında Korunan Özellikler
Dönüşüm sırasında, UART'ın temel işlevselliğini sağlayan bölümler olduğu gibi korunmuştur:

TX ve RX durum makineleri (IDLE, START, DATA, STOP durumları)
Bit zamanlaması (Clock-per-bit değerine göre)
Stop bit hesaplama mantığı
Flag yönetimi (TX tamamlandı, RX veri alındı)
Veri formatı (8 bit veri, programlanabilir stop bitler)

4. AXI4-Lite UART Test Bench Tasarımı
Test bench tasarlarken şu adımlar izlenmiştir:

AXI4-Lite master davranışı modelleme:

Adres ve veri kanalları için ayrı handshaking
Yanıt kanallarını bekleme


Özel task'lar tasarlama:

axi_write: AXI4-Lite protokolüne uygun yazma işlemleri
axi_read: AXI4-Lite protokolüne uygun okuma işlemleri
wait_for_flag: Belirli bir flag'in set edilmesini bekleme


Test senaryoları oluşturma:

Normal baud rate ile veri gönderme/alma
Yüksek baud rate ile veri gönderme/alma
Flag'lerin doğru ayarlanıp temizlenmesini kontrol etme



5. Önemli Tasarım Kararları

AXI Handshaking Yönetimi:

AXI spesifikasyonuna uygun olarak, adres ve veri kanalları bağımsız olarak kabul edilebilir
Ancak tasarım basitliği için, sadece her iki kanal da hazır olduğunda yazmaya izin verilir


Flag Yönetimi:

TX ve RX flag'leri donanım tarafından ayarlanır
Yazılım tarafından sadece 0 yazılarak temizlenebilir


AW Enable Sinyali:

aw_en sinyali kullanılarak, bir yazma işlemi tamamlanmadan yeni bir yazma işleminin başlaması engellenir



6. Simulasyon ve Doğrulama
Doğrulama için şu adımlar izlenir:

Loopback Testi:

TX pini RX pinine bağlanarak, gönderilen verinin geri alınması kontrol edilir


Flag Kontrolü:

TX tamamlandı ve RX veri alındı flag'lerinin doğru şekilde ayarlanması ve temizlenmesi kontrol edilir


Farklı Baud Rate Testi:

Farklı CPB değerleri ile iletişimin doğru çalıştığı doğrulanır


AXI Handshaking Kontrolü:

Valid/ready sinyallerinin protokole uygun şekilde çalıştığı kontrol edilir



7. Potansiyel Geliştirmeler
Bu implementasyon, temel AXI4-Lite özelliklerini kullanmaktadır. İleriki aşamalarda şu geliştirmeler yapılabilir:
DMA Güncellemesi

8. Sonuç
Bu dönüşüm, APB tabanlı UART modülünün AXI4-Lite protokolüne başarıyla uyarlanmasını sağlamıştır. Temel UART işlevselliği korunurken, AXI4-Lite'ın sağladığı daha gelişmiş handshaking ve hata bildirimi özellikleri kazanılmıştır.