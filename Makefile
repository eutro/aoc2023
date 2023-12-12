KNOWNTARGETS := _CoqProject Makefile.coq clean default
KNOWNFILES := _CoqProject.in Makefile

default:
	@+$(MAKE) --no-print-directory today

_CoqProject: _CoqProject.in scripts/gen_coqproject.sh
	@scripts/gen_coqproject.sh > $@

Makefile.coq: _CoqProject
	@$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	@+$(MAKE) --no-print-directory -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -rf input processed

invoke-coqmakefile: Makefile.coq
	@+$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
	@true
