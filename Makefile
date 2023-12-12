.PHONY: today
today:
	@$(MAKE) --no-print-directory day-"$$(printf "%02d" "$$(date +%d | sed 's/^0*//')")"

.PHONY: todaytop
todaytop:
	@$(MAKE) --no-print-directory daytop-"$$(printf "%02d" "$$(date +%d | sed 's/^0*//')")"

.PHONY: day-%
day-%:
	@touch -c processed/DayIn$*.v
	@$(MAKE) --no-print-directory out/DayIn$*.vo

.PHONY: daytop-%
daytop-%:
	@$(MAKE) --no-print-directory out/DayIn$*.vo
	rlwrap coqtop -R out Aoc2023 -ri DayIn$*

.PHONY:
clean:
	rm -rf input out processed

.SECONDEXPANSION:

include Makefile.generate

out/Day%.vo: src/Day%.v
	@mkdir -p out
	coqc -R out Aoc2023 $< -o $@

out/DayIn%.vo: processed/DayIn%.v out/Day%.vo
	coqc -R out Aoc2023 $< -o $@
