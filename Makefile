LEAN_DIR=/home/segfault/lean4
LEAN_PATH=$(LEAN_DIR)/library:./src:./sample-lean

CPP = src/network/n2o/web/server.cpp
LEAN = src/network/n2o/internal src/network/n2o/web/http src/data/bert sample-lean/sample

LIBS = -lwebsockets
BIN = sample

define lean-olean
LEAN_PATH=$(LEAN_PATH) $(LEAN_DIR)/bin/lean --make $(1).lean

endef

define lean-compile
LEAN_PATH=$(LEAN_PATH) $(LEAN_DIR)/bin/lean -c $(1).cpp $(1).lean

endef

all: clean
	$(foreach file,$(LEAN),$(call lean-olean,$(file)))
	$(foreach file,$(LEAN),$(call lean-compile,$(file)))
	$(LEAN_DIR)/bin/leanc $(CPP) $(foreach file,$(LEAN),$(file).cpp) $(LIBS) -o $(BIN) -g -Wall

clean:
	rm -f $(foreach file,$(LEAN),$(file).cpp) $(foreach file,$(LEAN),$(file).olean)
	rm -f $(BIN)

run:
	./$(BIN)
