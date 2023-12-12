# AOC 2023

These are my solutions to [Advent of Code
2023](https://adventofcode.com/2023), written in Coq.

## Building

Building is done with GNU Make. The `day-NN` target compiles the
source code for the day (if modified) and always recompiles the
[input-generated code](#input). A valid `session.key` (the `session`
cookie from the adventofcode.com site) must be provided for input
fetching to work.

## Input

Since Coq doesn't have IO, puzzle input is handled by generating a
source file including it, which always looks roughly like this:

```coq
Require Export DayNN.
Definition inp := input
<input goes here>
.
Time Compute main inp.
```

The `input` syntax is defined each day to parse the input, which may
optionally be preprocessed with a `DayNN.prep` script. This setup was
inspired by [someone else's previous Coq
solutions](https://github.com/Lysxia/advent-of-coq-2021).
