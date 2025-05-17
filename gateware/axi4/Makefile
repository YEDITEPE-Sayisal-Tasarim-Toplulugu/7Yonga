REPO_URL := https://github.com/pulp-platform/axi.git
REPO_DIR := $(pwd)
CORE_NAME = axi

.PHONY: setup

setup:
	@if [ ! -d "$(REPO_DIR)" ]; then \
		git clone $(REPO_URL); \
	else \
		echo "$(REPO_DIR) already exists. Skipping clone."; \
	fi
