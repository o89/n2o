#LEAN_DIR = # May be set here
LEAN_PATH = $(LEAN_DIR)/library:./src:./sample-lean
export LEAN_PATH

CPP = src/network/n2o/web/callback src/network/n2o/web/server
LEAN = src/data/bytes src/data/sum src/data/put src/data/vector src/data/parser src/data/bert src/network/n2o/internal src/network/n2o/web/http
FLAGS = -g -Wall

LIBNAME = libn2o.a

LIBS = -lwebsockets

SAMPLE = sample-lean/sample

define g++-obj
$(LEAN_DIR)/bin/leanc -c $(1).cpp $(FLAGS) -o $(1).o

endef

define lean-olean
$(LEAN_DIR)/bin/lean --make $(1).lean

endef

define lean-compile
$(LEAN_DIR)/bin/lean -c $(1).cpp $(1).lean

endef

all: olean
	$(foreach file,$(LEAN),$(call lean-compile,$(file)))
	$(foreach file,$(CPP) $(LEAN),$(call g++-obj,$(file)))
	ar rvs $(LIBNAME) $(addsuffix .o,$(CPP) $(LEAN))

olean:
	$(foreach file,$(LEAN),$(call lean-olean,$(file)))

clean:
	rm -f $(addsuffix .cpp,$(LEAN)) $(addsuffix .olean,$(LEAN))
	rm -f $(addsuffix .o,$(CPP) $(LEAN))
	rm -f $(SAMPLE) $(SAMPLE).cpp $(SAMPLE).olean $(LIBNAME)

sample:
	$(call lean-compile,$(SAMPLE))
	$(call lean-olean,$(SAMPLE))
	$(LEAN_DIR)/bin/leanc $(FLAGS) $(SAMPLE).cpp $(LIBNAME) $(LIBS) -o $(SAMPLE)

run:
	./$(SAMPLE)
