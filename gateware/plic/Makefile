REPO_URL := https://github.com/RoaLogic/plic.git
REPO_DIR := $(pwd)

.PHONY: setup

all: setup

setup:
	@if [ ! -d "$(REPO_DIR)" ]; then \
		git clone $(REPO_URL); \
	else \
		echo "$(REPO_DIR) already exists. Skipping clone."; \
	fi

