#!/bin/bash

### user variables (to be tuned according to your own setting
ALL="delaunayflip GeoCoq"
ROCQDITTODIR=../rocq-ditto # the directory which contains rocq-ditto
OUTPUT=_output


### general variables (do not change!)
WDIR=$(pwd)
bold=$(tput bold)
normal=$(tput sgr0)

cd $ROCQDITTODIR
for i in $ALL;
do
    echo "======================== running rocq-ditto on directory ${bold}$i${normal}... ========================"
    #echo "$WDIR/$i"
    #echo "$WDIR/$i$OUTPUT"
    dune exec --profile=release rocq-ditto -- -i $WDIR/$i -o $WDIR/$i_$OUTPUT -t turn_into_oneliner -v
    echo "======================== done running rocq-ditto, output in ${bold}$i$OUTPUT${normal}! ========================"
done
cd $WDIR




