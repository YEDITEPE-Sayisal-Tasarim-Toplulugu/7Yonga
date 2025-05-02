REPO_URL := https://github.com/pulp-platform/common_cells.git
REPO_DIR := $(pwd)
CORE_NAME = common_cells

.PHONY: setup

setup:
	@if [ ! -d "$(REPO_DIR)" ]; then \
		git clone $(REPO_URL); \
	else \
		echo "$(REPO_DIR) already exists. Skipping clone."; \
	fi
