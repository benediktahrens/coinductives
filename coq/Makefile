#######################################################
# BINARIES

LIBS=-R . Cat

COQC=$(COQBIN)coqc $(LIBS)
COQDEP=$(COQBIN)coqdep $(LIBS)

#######################################################
# FILES

FILES=\
	  Misc/Unicode.v                                     \
	  Theory/Notations.v                                 \
	  Theory/SetoidType.v                                \
	  Theory/Category.v                                  \
	  Theory/Functor.v                                   \
	  Theory/RelativeComonad.v                           \
	  Category/Type.v                                    \
	  Category/Setoid.v                                  \
	  Category/Functor/Type_Setoid.v                     \
	  InfiniteTriangles/redecInfiniteTriangles8_4.v      \
	  Category/RelativeComonad/InfiniteTriangles.v       \
	  Theory/Comodule.v                                  \
	  Category/RComod.v                                  \
	  Category/RComonad.v                                \
	  Category/Categories.v                              \
	  Theory/InitialTerminal.v                           \
	  Theory/Product.v                                   \
	  Theory/Morphism.v                                  \
	  Theory/StrongMonoidal.v


ALL= $(FILES)

#######################################################
# TARGETS

.SUFFIXES: .v .vo
.PHONY: all files depend

all: $(ALL:.v=.vo)
files: $(FILES:.v=.vo)
depend: .depend

.v.vo : .depend
	$(COQC) $<


#######################################################
#DEPENDENCIES

.depend : $(ALL)
	$(COQDEP) -I . $(ALL) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
include .depend
endif
