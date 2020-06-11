These measurements were made using the selfinterference script, now renamed "board_measurements"

With this script, everything is performed locally:
1. PREMized benchmarks are evaluated without interference.
2. Then with two identical non-PREMized background benchmarks to interfere.
3. Then with two identical PREMized background benchmarks to interfere.

In this run, the board_measurements script was updated to kill and spawn cmux more regularly, as
well as reperforming the board preparation routine every time cmux is spawned.
