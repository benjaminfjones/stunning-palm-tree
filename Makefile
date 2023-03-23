dafny_files := $(wildcard *.dfy)
solver_logs := $(patsubst %.dfy,%.log,$(dafny_files))

all: $(solver_logs)
	@echo "Verifying all"
.PHONY: all

%.log: %.dfy
	@echo Verifying $<
	dafny verify --solver-log $@ $< 

clean:
	rm -rf *.log
	rm -rf *.log.*
