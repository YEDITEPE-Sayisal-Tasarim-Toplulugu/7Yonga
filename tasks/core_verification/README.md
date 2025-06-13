# Çekirdek Doğrulaması

## Dizin
```bash
core_verification/
├── spike_part/                     # Spike çıktısı için gerekli araçları bulunduran klasör
│   └── Makefile                    # Bir prgram için spike çıktısını alan program, spike'ın yürütme çıktıları bu dosya ile aynı dizinde olur
├── testprogram/                    # Simülasyonda kullanılacak programları içeren klasör
│   └── coremark/                   # Simülasyon için coremark programı
│   └── firstapp/                   # Simülasyon için  basit assembly program
├── testsuit/                       # Simülasyon için gerekli HDL kod ve tanımları içerir
│   └── inc/                        # Simülasyon için gerekli header dosyalarını içerir
│   └── memory_system/              # Mikrodenetleyici çekirdeğine bağlı bulunan, bellekleri içerir
│   └── cv32e40p_tracer.sv          # Yürütülen programın buyruk kaydını tutan modül
│   └── tb_suit.sv                  # Simülasyon için Top modül
├── files.txt                       # Simülasyonda kullanılan kodların bulunduğu dizinlerin listesini ve içeri aktarılacak programların uzantısını içerir
├── freelist_generator_v2.py        # Belirtilen dizinleri okuyarak kaynak kodların listesini çıkaran python programı
├── README.md                       # Bu dosya
├── verification.tcl                # Vivado için simülasyon betiğidir, Simülasyonun yapılandırmasını yapar. Win_Verificator.bat tarafından Vivado üzerinde yürütlür
├── Win_Verificator.bat             # Vivado ve dizin kontrolünü yapan betiktir. Çalışıtırıldığında Vivado Xsim başlatılarak simülasyon gerçekleştirlir
```

## Kurulum
Win_Verificator.bat dosyasında ki VIVADO_DIR'de düzenleme yapılarak vivado klasörünün belirtilmesi gerekir.

## Kullanım
Win_Verificator.bat dosyası Windows ortamında çalışıtırıldığında, vivado Xsim aracı ile simülasyon yapılır ve çekirdek için yürütme kayıtları oluşturulur. Çekirdeğin yürütme kayıtları bu dosyanın olduğu dizinde oluşur.

## Spike Çıktıları
Spike için spike_part içinde bulunan makefile çalıştırılarak bu dosya ile aynı dizinde spike çıktısı elde edilebilir.

