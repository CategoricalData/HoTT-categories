MODULES    := theories/Peano \
	theories/Coq/Arith/Le \
	theories/Coq/Arith/Lt \
	theories/Coq/Arith/Plus \
	theories/Coq/Arith/Gt \
	theories/Coq/Logic/Decidable \
	theories/Coq/Arith/Compare_dec \
	\
	theories/Notations \
	theories/NotationsUtf8 \
	theories/Common \
	\
	theories/Category/Core \
	theories/Functor/Core \
	\
	theories/Category/Equality \
	theories/Category/Morphisms \
	theories/Category/UnivalentCategory \
	theories/Category/StrictCategory \
	theories/Category/Objects \
	theories/Category/Duals \
	theories/Category \
	\
	theories/Functor/Equality \
	theories/Functor/Identity \
	theories/Functor/Composition \
	theories/Functor/CompositionLaws \
	theories/Functor/Duals \
	theories/Functor \
	\
	theories/NaturalTransformation/Core \
	theories/NaturalTransformation/Equality \
	theories/NaturalTransformation/Identity \
	theories/NaturalTransformation/Composition \
	theories/NaturalTransformation/CompositionLaws \
	theories/NaturalTransformation/Duals \
	theories/NaturalTransformation \
	\
	theories/Category/Product \
	theories/Functor/Product \
	theories/NaturalTransformation/Product \
	\
	theories/Category/Sum \
	theories/Functor/Sum \
	theories/NaturalTransformation/Sum \
	\
	theories/Subcategory/Sigma \
	theories/Subcategory/SigmaObjects \
	theories/Subcategory/SigmaMorphisms \
	theories/Subcategory/Wide \
	theories/Subcategory/Full \
	theories/Subcategory \
	\
	theories/SetCategory \
	\
	theories/ComputableCat \
	\
	theories/FunctorCategory \
	theories/FunctorCategory/Morphisms \
	\
	theories/Functor/ProductFunctor \
	\
	theories/CategoryOfSections \
	\
	theories/NaturalTransformation/Isomorphisms \
	\
	theories/Functor/Pointwise \
	theories/Functor/Pointwise/Properties \
	theories/NaturalTransformation/Pointwise \
	\
	theories/Groupoid \
	theories/Groupoid/Functors \
	theories/Groupoid/Duals \
	theories/DiscreteCategory \
	theories/Discrete/Duals \
	theories/IndiscreteCategory \
	theories/BoolCategory \
	theories/NatCategory \
	theories/NatCategory/Duals \
	\
	theories/InitialTerminalCategory \
	\
	theories/Cat \
	theories/Cat/Morphisms \
	\
	theories/FunctorCategory/Functorial \
	\
	theories/DualFunctor \
	\
	theories/Pseudofunctor/Core \
	theories/Pseudofunctor/FromFunctor \
	theories/Pseudofunctor \
	\
	theories/Comma/CommaCategory \
	theories/Comma/Duals \
	theories/Comma/Projection \
	theories/Comma/InducedFunctors \
	\
	theories/UniversalProperties \
	\
	theories/IsGroupoid \
	\
	theories/Grothendieck/ToSet \
	theories/Grothendieck \
	theories/Grothendieck/PseudofunctorToCat \
	theories/Grothendieck/ToCat \
	\
	theories/DependentProduct \
	\
	theories/NaturalNumbersObject \
	theories/Hom \
	\
	theories/Functor/Attributes \
	\
	theories/Adjoint/UnitCounit \
	theories/Adjoint/UnitCounitCoercions \
	theories/Adjoint/Hom \
	theories/Adjoint/Duals \
	theories/Adjoint/Identity \
	theories/Adjoint/Composition \
	theories/Adjoint/Equality \
	theories/Adjoint/UniversalMorphisms \
	theories/Adjoint \
	\
	theories/Utf8

VS         := $(MODULES:%=%.v)
VDS	   := $(MODULES:%=%.v.d)

V = 0

SILENCE_HOQC_0 := @echo \"HOQC $$<\"; #
SILENCE_HOQC_1 :=
SILENCE_HOQC = $(SILENCE_HOQC_$(V))

SILENCE_COQDEP_0 := @echo \"COQDEP $$<\"; #
SILENCE_COQDEP_1 :=
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

NEW_TIME_FILE=time-of-build-after.log
OLD_TIME_FILE=time-of-build-before.log
BOTH_TIME_FILE=time-of-build-both.log
NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
SINGLE_TIME_FILE=time-of-build.log
SINGLE_PRETTY_TIME_FILE=time-of-build-pretty.log
TIME_SHELF_NAME=time-of-build-shelf
COQDOCFLAGS=--external http://hott.github.io/HoTT/coqdoc-html/ HoTT -interpolate -utf8


HOQC=$(shell readlink -f ./HoTT/hoqc)


.PHONY: coq clean pretty-timed pretty-timed-files html HoTT

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

pretty-timed-diff:
	bash ./etc/make-each-time-file.sh "$(MAKE)" "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)"
	$(MAKE) combine-pretty-timed

combine-pretty-timed:
	python ./etc/make-both-time-files.py "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)" "$(BOTH_TIME_FILE)"
	cat "$(BOTH_TIME_FILE)"
	@echo

pretty-timed:
	bash ./etc/make-each-time-file.sh "$(MAKE) SEMICOLON=;" "$(SINGLE_TIME_FILE)"
	python ./etc/make-one-time-file.py "$(SINGLE_TIME_FILE)" "$(SINGLE_PRETTY_TIME_FILE)"
	cat "$(SINGLE_PRETTY_TIME_FILE)"
	@echo

Makefile.coq: Makefile $(VS) HoTT
	coq_makefile COQC = "$(SILENCE_HOQC)\$$(TIMER) \"$(HOQC)\"" COQDEP = "$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" $(VS) -arg -dont-load-proofs -o Makefile.coq -R HoTT/theories HoTT -R theories HoTT.Categories

HoTT/Makefile:
	cd HoTT; ./configure

HoTT: HoTT/Makefile
	cd HoTT; $(MAKE)

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
