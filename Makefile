.PHONY: today
today:
	@$(MAKE) day-"$$(printf "%02d" "$$(date +%d | sed 's/^0*//')")"

.PHONY: day-%
day-%:
	$(MAKE) processed/DayIn$*.v processed/Day$*.v
	touch processed/DayIn$*.v
	$(MAKE) out/Day$*.vo out/DayIn$*.vo

out/%.vo: processed/%.v out
	coqc -R out Aoc2023 $< -o $@

processed/Day%.v: processed src/Day%.v
	cp src/Day$*.v processed/Day$*.v

.SECONDEXPANSION:
processed/DayIn%.v: processed input/day$$*.txt $$(wildcard src/Day$$*.prep)
	echo -e "Require Import Day$*. Definition x := input" > $@
	if [ -f src/Day$*.prep ]; \
		then src/Day$*.prep < input/day$*.txt ; \
		else cat input/day$*.txt ; \
	fi >> $@
	echo -e ".\nCompute main x." >> $@

input/day%.txt:
	@./fetch.sh $*

processed:
	mkdir processed
out:
	mkdir out

clean:
	rm -rf input out processed
