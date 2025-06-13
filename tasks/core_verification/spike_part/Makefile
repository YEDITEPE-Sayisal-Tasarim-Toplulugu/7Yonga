# 7Yonga
# Yeditepe Üniversitesi, Sayısal Tasarım Topluluğu
# 06.2025

PROGRAM			= $(realpath ../testprogram/firstapp/program.elf)
BASE_ADDR 		= 0x30000000
SPIKEMEMORY 	= 131072

LOGFILE			= ../spike_program.log

SPIKEFLAGS     	= --isa=RV32IMAC -m$(BASE_ADDR):$(SPIKEMEMORY) --log-commits

all: run

run: $(PROGRAM)
	spike $(SPIKEFLAGS) $< 2>&1 | tee $(LOGFILE)

# yalnızca test kodu gözüksün
	tail +6 $(LOGFILE) | tee $(LOGFILE)
