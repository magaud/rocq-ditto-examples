#!/bin/bash

if [ "$1" = "-keep-postscript" ]
then
keep_postscript=yes
else
keep_postscript=no
fi

for i in 0 1 2
do
  for j in 0 1 2
  do
    echo "Require Import String smooth_trajectories. Compute example_by_index $i $j true." \
     | coqtop -R . trajectories | ../coq_output_to_postscript.pl > "output_"$i"_"$j"_true".ps
  ps2pdf "output_"$i"_"$j"_true".ps
  if [ "$keep_postscript" = yes ]
  then true
  else rm "output_"$i"_"$j"_true".ps
  fi
  done
done

