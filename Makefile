MODULES    := theories/Peano \
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
	theories/Category/Category \
	theories/Category/StrictCategory \
	theories/Category/Objects \
	theories/Category/Duals \
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
	theories/SumPreCategory \
	\
	theories/SetCategory \
	\
	theories/ComputableCat \
	\
	theories/FunctorCategory \
	theories/FunctorCategory/Morphisms \
	\
	theories/NaturalTransformation/Isomorphisms \
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
	theories/Comma/CommaCategory \
	theories/Comma/Duals \
	theories/Comma/Projection \
	theories/Comma/InducedFunctors \
	\
	theories/UniversalProperties \
	\
	theories/IsGroupoid \
	\
	theories/Adjoint/UnitCounit \
	\
	theories/Grothendieck/ToSet \
	theories/Grothendieck \
	\
	theories/NaturalNumbersObject \
	theories/Hom \
	\
	theories/Utf8

VS         := $(MODULES:%=%.v)
VDS	   := $(MODULES:%=%.v.d)

NEW_TIME_FILE=time-of-build-after.log
OLD_TIME_FILE=time-of-build-before.log
BOTH_TIME_FILE=time-of-build-both.log
NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
TIME_SHELF_NAME=time-of-build-shelf



.PHONY: coq clean pretty-timed pretty-timed-files html HoTT

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

pretty-timed-diff:
	sh ./make-each-time-file.sh "$(MAKE)" "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)"
	$(MAKE) combine-pretty-timed

combine-pretty-timed:
	python ./make-both-time-files.py "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)" "$(BOTH_TIME_FILE)"
	cat "$(BOTH_TIME_FILE)"
	@echo

pretty-timed:
	sh ./make-each-time-file.sh "$(MAKE)" "$(NEW_TIME_FILE)"
	python ./make-one-time-file.py "$(NEW_TIME_FILE)" "$(NEW_PRETTY_TIME_FILE)"
	cat "$(NEW_PRETTY_TIME_FILE)"
	@echo

Makefile.coq: Makefile $(VS) HoTT
	coq_makefile $(VS) -arg -dont-load-proofs -o Makefile.coq -R HoTT/theories HoTT -R theories HoTT.Categories
	sed s':\$$(COQBIN)coqc:'"$$(readlink -f ./HoTT/hoqc)"':g' -i Makefile.coq

HoTT/Makefile:
	cd HoTT; ./configure

HoTT: HoTT/Makefile
	cd HoTT; $(MAKE)

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
