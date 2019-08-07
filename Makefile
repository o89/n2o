LEAN_DIR=/home/segfault/lean4
LEAN_PATH=$(LEAN_DIR)/library:./src:./sample-lean

CPP = src/Network/N2O/Web/Server.cpp
LEAN = src/Network/N2O/Internal src/Network/N2O/Web/Http src/Data/BERT sample-lean/sample

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
