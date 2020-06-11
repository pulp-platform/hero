These measurements were made using the selfinterference script found in this folder.

With this script, everything is performed remotely:
1. PREMized benchmarks are evaluated without interference.
2. Then with two identical non-PREMized background benchmarks to interfere.
3. Then with two identical PREMized background benchmarks to interfere.

Shortcomings:
- Always initiating SSH connections.
- No script to migrate already processes on the board to a core and assign them a low prio.
