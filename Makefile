SRC_DIR   = markdowns
BUILD_DIR = src
DIST_DIR  = dist

TEMPLATE  = templates/main.latex
FILTER    = templates/main.lua

DIST_NAME = tacet-whitepaper.pdf

MD_FILES    := $(wildcard $(SRC_DIR)/*.md)
LATEX_FILES := $(patsubst $(SRC_DIR)/%.md,$(BUILD_DIR)/%.latex,$(MD_FILES))

.DEFAULT_GOAL := dist

.PHONY: build dist clean

## Convert markdowns/*.md to src/*.latex fragments
build: $(LATEX_FILES)

$(BUILD_DIR)/%.latex: $(SRC_DIR)/%.md $(FILTER) | $(BUILD_DIR)
	pandoc $< --lua-filter=$(FILTER) --top-level-division=chapter -t latex -o $@

## Compile the template into dist/tacet-whitepaper.pdf
dist: build
	mkdir -p $(DIST_DIR)
	tectonic $(TEMPLATE) --outdir $(DIST_DIR)
	mv $(DIST_DIR)/$(notdir $(basename $(TEMPLATE))).pdf $(DIST_DIR)/$(DIST_NAME)

$(BUILD_DIR):
	mkdir -p $@

## Remove generated latex fragments and the built pdf
clean:
	rm -rf $(BUILD_DIR) $(DIST_DIR)
