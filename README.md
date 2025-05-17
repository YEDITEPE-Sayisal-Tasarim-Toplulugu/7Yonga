# 7Yonga Projesi

Başvuru Yaptığı Takım Adı:
Yeditepe Üniversitesi Sayısal Tasarım Topluluğu 

Takım ID:
#582202 

Başvuru ID:
#3062081 

Takımımız, Yeditepe Üniversitesi Elektrik-Elektronik ve Bilgisayar Mühendisliği lisans
öğrencilerinden oluşmaktadır. 7Yonga projesi kapsamında, açık kaynaklı bir RISC-V çekirdeği, çevre
birimleri ve veri yolları ile özgün bir mikrodenetleyici tasarlamayı hedeflemekteyiz. Bu
mikrodenetleyici, yüksek doğruluk ve düşük güç tüketimi öncelikleri doğrultusunda geliştirilecektir.

## Üyeler
* Muhammet Furkan UZUN (İletişim Sorumlusu) (@mhfuzun)
  - Öğrenim: Yeditepe Üniversitesi, Elektrik-Elektronik Mühendisliği 2. Sınıf öğrencisi.
  - İş yükü: Çekirdeğin, belleklerin, veri yollarının implementasyonu,
donanım hızlandırıcı
* Hasan GÜZELŞEMME (@princeofyozgat)
  - Öğrenim: Yeditepe Üniversitesi, Bilgisayar Mühendisliği 3. Sınıf öğrencisi.
  - İş yükü: Çekirdek implementasyonu, çevre birimleri tasarımı, devre
serimi
* Erhan ÖNALDI (@ErhanOnaldi)
  - Öğrenim: Yeditepe Üniversitesi, Bilgisayar Mühendisliği 4. Sınıf öğrencisi.
  - İş yükü: Çevre Birimleri tasarımı, testler, donanım hızlandırıcı

## Tasarım
<div style="background-color: white; display: inline-block; padding: 0px; border-radius: 8px; box-shadow: 0 0 0px rgba(0,0,0,0.1);">
  <img src="tasarımlar/görseller/YONGA-TASARIM-TOP_v2.0.drawio.png" alt="Mikrodentleyici Tasarımı" width="500"/>
</div>

## İş Planı
![İş Planı](tasarımlar/görseller/isPlani.jpg)

## Dizin Yapısı:
```bash
my-project/
│
├── README.md               # Projenin tanıtım dosyası
├── LICENSE                 # Lisans bilgisi
├── .gitignore              # Git tarafından yok sayılacak dosyalar
├── requirements.txt        # Gerekli Python paketleri (Python için)
├── dependences.md          # Bağımlı olunan harici repolar (Makefile dependences ile toplu olarak "clone"'lanabilir)
│
├── docs/                   # Belgeler
│   └── kaynaklar/          # Referans Dokümanlar
|
├── tasarımlar/             # Proje tasarım klasörü, drawio tasarımlarını içerir
│   └── görseller/          # drawio tasarımlarının .jpg/.png çıktılarını içerir
│
├── teknofest/              # Teknofest 2025 Klasörü, Yarışma aşamlarını ve repor (şablonlarını) içerir.
│   └── önbaşvuru/          # Teknofest 2025 ~ Ön Başvuru Aşaması
│   └── dtr/                # Teknofest 2025 ~ DTR Aşaması
│   └── ötr/                # Teknofest 2025 ~ OTR Aşaması
|
├── LDPC/                   # LDPC çalışma klasörü
│   └── articles/           # LDPC ile ilgli referans kaynaklar
│   └── pdfs/               # LPDC çalışma çıktıları
│
├── firmware/               # Mikrodenetleyici yazılımlarını içerir
|
├── gateware/               # HDL kodları
│   └── axi4/               # AXI4 Klasörü
│     └── axi/              # Harici AXI4 reposu
│     └── Makefile          # AXI4 reposunu klonlamak için betik
│     └── README.md         # AXI4 reposu ile ilgili karşılaşılan hatalar
│   └── core/               # CORE Klasörü
│   └── inc/                # SOC için Systemverilog Header dosyaları
│   └── peripherals/        # Mikrodenetleyici Çevre Birimleri klasörü
│     └── uart/             # UART Çevre Birimi HDL ve test kodları
│     └── README.MD         #
│   └── pulp_common_cell/   # Pulp Common Cell klasörü, harici repo içerir.
│     └── Makefile          # Pulp Common Cell reposunu klonlamak için betik
│   └── soc/                # Mikrodenetleyici SOC yapısına ait HDL kodlarını içerir
│     └── adapter/          # SOC içerisinde bulunan arayüzler için arayüz dönüşümlerini sağlar.
│     └── core_interfaces/  # Çekirdeğin SOC içerisindeki sarıcı data&instruction arayüzlerini içerir
│   └── test/               # HDL test klasörü
│
```