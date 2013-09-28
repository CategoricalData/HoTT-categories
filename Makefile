MODULES    := Peano \
	Coq/Arith/Le \
	Coq/Arith/Lt \
	Coq/Arith/Plus \
	Coq/Arith/Gt \
	Coq/Logic/Decidable \
	Coq/Arith/Compare_dec \
	\
	Notations \
	NotationsUtf8 \
	Common \
	\
	Category/Core \
	Functor/Core \
	\
	Category/Equality \
	Category/Morphisms \
	Category/UnivalentCategory \
	Category/StrictCategory \
	Category/Objects \
	Category/Duals \
	Category \
	\
	Functor/Equality \
	Functor/Identity \
	Functor/Composition \
	Functor/CompositionLaws \
	Functor/Duals \
	Functor \
	\
	NaturalTransformation/Core \
	NaturalTransformation/Equality \
	NaturalTransformation/Identity \
	NaturalTransformation/Composition \
	NaturalTransformation/CompositionLaws \
	NaturalTransformation/Duals \
	NaturalTransformation \
	\
	Category/Product \
	Functor/Product \
	NaturalTransformation/Product \
	\
	Category/Sum \
	Functor/Sum \
	NaturalTransformation/Sum \
	\
	Subcategory/Sigma \
	Subcategory/SigmaObjects \
	Subcategory/SigmaMorphisms \
	Subcategory/Wide \
	Subcategory/Full \
	Subcategory \
	\
	SetCategory \
	\
	ComputableCat \
	\
	FunctorCategory \
	FunctorCategory/Morphisms \
	\
	Functor/Product/ProductFunctor \
	\
	CategoryOfSections \
	\
	NaturalTransformation/Isomorphisms \
	\
	Functor/Pointwise \
	Functor/Pointwise/Properties \
	NaturalTransformation/Pointwise \
	\
	ExponentialLaws/Law1/Functors \
	ExponentialLaws/Law2/Functors \
	ExponentialLaws/Law3/Functors \
	ExponentialLaws/Law4/Functors \
	ExponentialLaws/Law1/Law \
	ExponentialLaws/Law2/Law \
	ExponentialLaws/Law3/Law \
	ExponentialLaws/Law4/Law \
	ExponentialLaws/Law0 \
	ExponentialLaws/Law1 \
	ExponentialLaws/Law2 \
	ExponentialLaws/Law3 \
	ExponentialLaws/Law4 \
	ExponentialLaws \
	\
	NaturalTransformation/Composition/Functorial \
	Functor/Composition/Functorial \
	\
	Groupoid \
	Groupoid/Functors \
	Groupoid/Duals \
	DiscreteCategory \
	Discrete/Duals \
	IndiscreteCategory \
	BoolCategory \
	NatCategory \
	NatCategory/Duals \
	\
	InitialTerminalCategory \
	\
	Cat \
	Cat/Morphisms \
	\
	FunctorCategory/Functorial \
	\
	DualFunctor \
	\
	Pseudofunctor/Core \
	Pseudofunctor/FromFunctor \
	Pseudofunctor \
	\
	Comma/CommaCategory \
	Comma/Duals \
	Comma/Projection \
	Comma/InducedFunctors \
	\
	UniversalProperties \
	\
	IsGroupoid \
	\
	Grothendieck/ToSet \
	Grothendieck \
	Grothendieck/PseudofunctorToCat \
	Grothendieck/ToCat \
	\
	DependentProduct \
	\
	NaturalNumbersObject \
	Hom \
	\
	Functor/Attributes \
	\
	Adjoint/UnitCounit \
	Adjoint/UnitCounitCoercions \
	Adjoint/Hom \
	Adjoint/Duals \
	Adjoint/Identity \
	Adjoint/Composition \
	Adjoint/Equality \
	Adjoint/UniversalMorphisms \
	Adjoint \
	\
	Utf8

VS         := $(MODULES:%=theories/Categories/%.v)
VDS	   := $(MODULES:%=theories/Categories/%.v.d)

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
	coq_makefile COQC = "$(SILENCE_HOQC)\$$(TIMER) \"$(HOQC)\"" COQDEP = "$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" $(VS) -arg -dont-load-proofs -o Makefile.coq -R HoTT/theories HoTT -R theories HoTT

HoTT/configure.ac::

HoTT/Makefile.am::

HoTT/autogen.sh::

HoTT/configure: HoTT/configure.ac HoTT/autogen.sh
	cd HoTT; ./autogen.sh

HoTT/Makefile: HoTT/configure HoTT/Makefile.am
	cd HoTT; ./configure

HoTT: HoTT/Makefile
	cd HoTT; $(MAKE)

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
