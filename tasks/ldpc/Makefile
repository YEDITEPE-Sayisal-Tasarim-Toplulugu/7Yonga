# PDF çıktılarının kaydedileceği dizin
OUTPUT_DIR = pdfs

# Tüm kaynak Markdown dosyalarını al
MD_SRCS := $(wildcard *.md)

# PDF dosyalarının adlarını oluştur (pdfs/dosya.pdf)
PDFS := $(patsubst %.md,$(OUTPUT_DIR)/%.pdf,$(MD_SRCS))

# Varsayılan hedef: tüm Markdown dosyalarını PDF'ye çevir
all: $(PDFS)

# PDF çıktı dizinini oluştur ve Markdown'ı PDF'ye çevir
$(OUTPUT_DIR)/%.pdf: %.md | $(OUTPUT_DIR)
	pandoc $< -o $@ --pdf-engine=xelatex

# Çıktı dizini yoksa oluştur
$(OUTPUT_DIR):
	mkdir -p $(OUTPUT_DIR)

# Temizlik komutu (tüm PDF'leri siler)
clean:
	rm -rf $(OUTPUT_DIR)

.PHONY: all clean
