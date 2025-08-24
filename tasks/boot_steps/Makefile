
FIRMWARE_DIR 	= ../../firmware
OUTDIR			= ./OUT

PYTHON	 		= python3
GEN 			= boot_code_generator.py

BINFILE			?= $(FIRMWARE_DIR)/loader/BUILD/program.bin
TEMPFILE		= boot_code_file_template.txt
OUTFILE			= boot_code.sv

TARGET			= $(OUTDIR)/$(OUTFILE)

all: $(TARGET)

$(OUTDIR):
	mkdir $(OUTDIR)

$(TARGET): $(OUTDIR) $(TEMPFILE) $(BINFILE)
	$(PYTHON) $(GEN) --bin $(BINFILE) --template $(TEMPFILE) --o $@

clean:
	rm $(TARGET)
