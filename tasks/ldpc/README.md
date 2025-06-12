# LDPC Hakkında
<br>Mikrodenetleyicinin üzerinde LDPC (low-density parity-check code) enkoder donanım hızlandırıcı bulunmalıdır. LDPC enkodere sürülecek veriler bu iş için atanmış UART arayüzü üzerinden istenen bellek alanına yönlendirilmeli, bellekten AXI arayüzü üzerinden hızlandırıcı üzerine çekilerek bu hızlandırıcı üzerinde işlenmeli ve kodlanmış veriler yine AXI arayüzü üzerinden istenen bellek alanına geri yazılmalıdır.

## Önemli Belgeler
Video Ders İçeriği:  
https://www.youtube.com/watch?v=B_VgyNY6cBs&list=PLyqSpQzTE6M81HJ26ZaNv0V3ROBrcv-Kc


PDF Belgesi:  
38212-g40.pdf

## LDPC hızlandırıcı çalışma şeması aşağıdaki şekilde olmalıdır: 
* Çip üzerinden gelecek spesifik bellek adreslerine yapılacak yazma komutları, bellek veri akışı için kullanılacak olan UART çevre biriminin konfigürasyon yazmaçlarına ve LDPC hızlandırıcı içerisindeki konfigürasyon yazmaçlarına yazılacak olup bu yazma komutları ile LDPC çekirdek ve hızlandırıcısı konfigüre edilmelidir. 

* Konfigürasyonun ardından stream amaçlı UART arayüzü (UART-stream) üzerinden gönderilen veriler istenen bellek alanına yazılmalıdır.

* İstenen bellek alanına yazılmış olan veri, LDPC hızlandırıcıya aşağıdaki iki yoldan biri üzerinden gönderilmeli ve geri alınmalıdır:
    * Çekirdek üzerinden yükle-yaz (İng. load-store) komutlarıyla ilgili bellek alanından LDPC hızlandırıcıya veri transferi yapılmalı ve yine çekirdekten oluşturulacak okuma komutları ile kodlanmış veri, ilgili bellek alanına geri yazılmalıdır. 
    
    * Doğrudan bellek erişimi (İng. direct memory access) (DMA) kullanılarak konfigürasyonun ardından LDPC hızlandırıcı doğrudan kendisine ayrılan bellek alanından kodlanmamış verinin okumasını ve bu bellek alanına kodlanmış verinin yazmasını yapmalıdır. (Bu yaklaşımı başarılı uygulayan yarışmacılar +7 bonus puan ile ödüllendirilir) 
* Kodlama operasyonu tamamlandıktan sonra aşağıdaki iki yoldan biri üzerinden çekirdek, işlemin tamamlandığına dair haberdar edilmelidir: 
    * Belli bir LDPC hızlandırıcı yazmacına işlemin tamamlandığına dair bir değer yazılması ve işlemcinin sorgulama (İng. polling) ile bu durumdan haberdar olması. 
    
    * İşlemciye bir işkesme (İng. interrupt) sinyali gönderilmesi ve işlemcinin ilgili interrupt sinyalini alıp önceden belirlenmiş bir rutini icra etmesi. (Bu yaklaşımı başarılı uygulayan yarışmacılar +3 bonus puan ile ödüllendirilir) 
* Çıktıların kontrolü, UART üzerinden kodlanmış LDPC verisinin hex karakterleri halinde çıkartılması ve bu çıktının, modelden alınmış eş verinin kodlanmış çıktısı ile kıyaslanması sonucu sağlanacaktır. 
