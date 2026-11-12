default: compile

base_dir   = $(abspath .)
src_dir    = $(base_dir)/src/main
gen_dir    = $(base_dir)/generated-src
out_dir    = $(base_dir)/outputs
nproc      = $(shell nproc --ignore 1)

SBT       = sbt
SBT_FLAGS = -ivy $(base_dir)/.ivy2

sbt:
	$(SBT) $(SBT_FLAGS)

compile: $(gen_dir)/Tile.sv

# Generate CoreSoc FIRRTL and Coq, then check the generated Coq file.
coq:
	bash "$(base_dir)/scripts/generate-coq.sh"

# CIRCT/MLIR state-machine version described in fir2coq.md.
coq-mlir:
	bash "$(base_dir)/scripts/generate-coq-mlir.sh"

coq-mlir-tool:
	@test -n "$(CIRCT_ROOT)" || { echo "Set CIRCT_ROOT to the CIRCT SDK directory" >&2; exit 1; }
	cmake -S "$(base_dir)/mlir-to-coq" -B "$(base_dir)/out/coq-mlir" -G Ninja \
		-DCMAKE_PREFIX_PATH="$(CIRCT_ROOT)" -DCMAKE_BUILD_TYPE=Release
	cmake --build "$(base_dir)/out/coq-mlir" -j$(or $(JOBS),2)

test-coq-mlir: coq-mlir-tool
	ctest --test-dir "$(base_dir)/out/coq-mlir" --output-on-failure

$(gen_dir)/Tile.sv: $(wildcard $(src_dir)/scala/*.scala)
	$(SBT) $(SBT_FLAGS) "run --target-dir=$(gen_dir)"

CXXFLAGS += -std=c++11 -Wall -Wno-unused-variable

# compile verilator
VERILATOR = verilator --cc --exe
VERILATOR_FLAGS = --assert -Wno-STMTDLY -O3 --trace --threads $(nproc)\
	--top-module Tile -Mdir $(gen_dir)/VTile.csrc \
	-CFLAGS "$(CXXFLAGS) -include $(gen_dir)/VTile.csrc/VTile.h" 

$(base_dir)/VTile: $(gen_dir)/Tile.sv $(src_dir)/cc/top.cc $(src_dir)/cc/mm.cc $(src_dir)/cc/mm.h
	$(VERILATOR) $(VERILATOR_FLAGS) -o $@ $< $(word 2, $^) $(word 3, $^)
	$(MAKE) -C $(gen_dir)/VTile.csrc -f VTile.mk

verilator: $(base_dir)/VTile

# isa tests + benchmarks with verilator
test_hex_files = $(wildcard $(base_dir)/tests/*.hex)
test_out_files = $(foreach f,$(test_hex_files),$(patsubst %.hex,%.out,$(out_dir)/$(notdir $f)))

$(test_out_files): $(out_dir)/%.out: $(base_dir)/VTile $(base_dir)/tests/%.hex
	mkdir -p $(out_dir)
	$^ $(patsubst %.out,%.vcd,$@) 2> $@

run-tests: $(test_out_files)

# run custom benchamrk
custom_bmark_hex ?= $(base_dir)/custom-bmark/main.hex
custom_bmark_out  = $(patsubst %.hex,%.out,$(out_dir)/$(notdir $(custom_bmark_hex)))
$(custom_bmark_hex):
	$(MAKE) -C custom-bmark

$(custom_bmark_out): $(base_dir)/VTile $(custom_bmark_hex)
	mkdir -p $(out_dir)
	$^ $(patsubst %.out,%.vcd,$@) 2> $@

run-custom-bmark: $(custom_bmark_out)

# unit tests + integration tests
test:
	$(SBT) $(SBT_FLAGS) test

# Only runs tests that failed in the previous run
test-quick:
	$(SBT) $(SBT_FLAGS) testQuick

clean:
	rm -rf $(gen_dir) $(out_dir) test_run_dir

cleanall: clean
	rm -rf target project/target

.PHONY: sbt compile coq coq-mlir coq-mlir-tool test-coq-mlir verilator run-tests run-custom-bmark test test-quick clean cleanall
