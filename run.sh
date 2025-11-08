#!/bin/bash

### user variables (to be tuned according to your own setting
ALL="delaunayflip" #ALL="delaunayflip GeoCoq stdpp"
ROCQDITTODIR="/Users/magaud/rocq-ditto" # the directory which contains rocq-ditto
OUTPUT=_xxx

eval $(opam env --switch=$ROCQDITTODIR --set-switch)
### general variables (do not change!)
WDIR=$(pwd)
bold=$(tput bold)
normal=$(tput sgr0)

cd $ROCQDITTODIR
make build
for i in $ALL;
do
    echo "======================== running rocq-ditto on directory ${bold}$i${normal}... ========================"
    echo "$WDIR/$i"
    echo "$WDIR/$i$OUTPUT"
    dune exec --profile=release rocq-ditto -- -i $WDIR/$i -o $WDIR/$i$OUTPUT -t turn_into_oneliner -v --save-vo
    echo "======================== done running rocq-ditto, output in ${bold}$i$OUTPUT${normal}! ========================"
done
cd $WDIR




