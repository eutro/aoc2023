#!/usr/bin/env sh

DIR="$(readlink -f "$(dirname "$0")"/..)"
cd "$DIR" || exit 1

SRC="$(find src -name '*.v' | sort)"
DAYS_IN="$(printf "%s\n" $SRC | grep Day | sed -e s/Day/DayIn/g -e s/src/processed/g)"

cat _CoqProject.in
printf "%s\n" $SRC $DAYS_IN
