#!/usr/bin/env sh

YEAR=2023
DIR="$(readlink -f "$(dirname "$0")"/..)"
cd "$DIR" || exit 1

if [ ! -f session.key ] ; then
   echo "session.key missing"
   exit 1
fi

KEY="$(cat session.key)"

if [ -z "$1" ]
then DAYN="$(date +%d)"
else DAYN="$1"
fi
DAY="$(echo "$DAYN" | sed 's/^0*//')"
DAYP="$(printf "%02d" "$DAY")"

mkdir -p input
echo "Fetching day $DAY..."
curl -fs -H"Cookie: session=$KEY" \
     "https://adventofcode.com/$YEAR/day/$DAY/input" \
     -o "input/day$DAYP.txt" &&
    echo "Success" && exit 0 || echo "Errored" && exit 1
