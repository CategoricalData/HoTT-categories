MODULES    := theories/Notations \
	theories/NotationsUtf8 \
	theories/Common \
	\
	theories/PreCategory/Core \
	theories/PreCategory/Equality \
	theories/PreCategory \
	theories/StrictCategory \
	\
	theories/Functor/Core \
	theories/Functor/Equality \
	theories/Functor/Identity \
	theories/Functor/Composition \
	theories/Functor/CompositionLaws \
	theories/Functor \
	\
	theories/NaturalTransformation/Core \
	theories/NaturalTransformation/Equality \
	theories/NaturalTransformation/Identity \
	theories/NaturalTransformation/Composition \
	theories/NaturalTransformation/CompositionLaws \
	theories/NaturalTransformation \
	\
	theories/ProductPreCategory \
	theories/SumPreCategory \
	\
	theories/FunctorPreCategory \
	\
	theories/DiscretePreCategory \
	theories/BoolCategory \
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

HoTT:
	cd HoTT; $(MAKE)

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
