MODULES    := theories/Notations \
	theories/NotationsUtf8 \
	theories/Common \
	\
	theories/PreCategory \
	theories/Functor \
	\
	theories/Utf8

VS         := $(MODULES:%=%.v)
VDS	   := $(MODULES:%=%.v.d)

NEW_TIME_FILE=time-of-build-after.log
OLD_TIME_FILE=time-of-build-before.log
BOTH_TIME_FILE=time-of-build-both.log
NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
TIME_SHELF_NAME=time-of-build-shelf



.PHONY: coq clean timed pretty-timed pretty-timed-files html HoTT

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

# TODO(jgross): Look into combining this with the time-make.sh script
timed: Makefile.coq
	chmod +x ./report_time.sh
	./report_time.sh -c $(MAKE) -f Makefile.coq SHELL=./report_time.sh

pretty-timed-diff:
	sh ./make-each-time-file.sh "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)"
	$(MAKE) combine-pretty-timed

combine-pretty-timed:
	python ./make-both-time-files.py "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)" "$(BOTH_TIME_FILE)"
	cat "$(BOTH_TIME_FILE)"

pretty-timed:
	sh ./make-each-time-file.sh "$(NEW_TIME_FILE)"
	python ./make-one-time-file.py "$(NEW_TIME_FILE)" "$(NEW_PRETTY_TIME_FILE)"

Makefile.coq: Makefile $(VS) HoTT
	coq_makefile $(VS) -arg -dont-load-proofs -o Makefile.coq -R HoTT/theories HoTT -R theories HoTT.Categories
	sed s':\$$(COQBIN)coqc:'"$$(readlink -f ./HoTT/hoqc)"':g' -i Makefile.coq

HoTT:
	cd HoTT; $(MAKE)

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
