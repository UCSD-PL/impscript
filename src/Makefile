
LIBS=-libs unix,str
LAM=-I LamJS
STATS=-I BNstats
PARSE=-use-menhir -yaccflag --explain # set to empty for ocamlyacc

all:
	([ -d out ] && echo "out/ exists") || (mkdir out && echo "out/ created")
	rm -f _build/langParser.conflicts
	ocamlbuild $(LIBS) $(PARSE) $(LAM) $(STATS) -no-links main.native
	ln -f -s _build/main.native impscript

loc:
	wc -l lang.ml main.ml langUtils.ml                \
	  utils.ml settings.ml log.ml                     \
	  langLexer.mll langParser.mly                    \
	  desugar.ml printer.ml acePrinter.ml             \
	  typing.ml                                       \
	  ../prims/prims.is                               \

clean:
	rm -rf _build out impscript

