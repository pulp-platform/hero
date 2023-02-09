#!/bin/ash

for seed in $(seq 5)
do
    for width in $(seq 2 4 128)
    do
        echo "Running mm-small with width=$width"
        # Run the app
        time ./mm-small $width > output.log
        echo -n "$seed " >> results.csv
        # Get all the "csv" output and write them in a new line in results.csv
        grep "csv :" output.log | awk '{$1=$2=""; print $0}' | xargs echo >> results.csv
    done
done
