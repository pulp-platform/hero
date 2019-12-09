curdir=$(dirname "$(readlink -f "$0")")
cd $curdir/../hardware/vsim
../test/gen_slm_files.sh polybench-acc/$1
output=$(mktemp)
DISPLAY= ./start_sim.sh | tee $output

simout=$(cat $output | fgrep '# [0,0]' | tail -n +2 | sed -e 's/# \[0,0\] //' \
  | sed -e 's/[[:space:]]*$//')
expout=$(cat "$curdir/../openmp-examples/polybench-acc/$1/$1.exp")
rm $output
if [ "$simout" = "$expout" ]; then
  echo "> OUTPUT: OK";
  exit 0
else
  echo "> OUTPUT: WRONG!"
  echo "--- OUT ---"
  echo $simout
  echo "--- EXP ---"
  echo $expout
  exit 1
fi
