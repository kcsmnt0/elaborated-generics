AGDA_BIN    ?= agda
RTS_OPTIONS ?= +RTS -M8G -H3.5G -A128M -s -RTS
AGDA_EXEC   = $(AGDA_BIN) $(RTS_OPTIONS)

everything: Everything.agda
	$(AGDA_EXEC) -i. -isrc Everything.agda --profile=internal

.PHONY: Everything.agda
Everything.agda:
	cabal run GenerateEverything

clean :
	find . -type f -name '*.agdai' -delete
