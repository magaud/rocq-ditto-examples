#!/bin/perl

$printit = 0;
while(<STDIN>) {
  if(/END/) { exit 0; }
  elsif(/START/) {$printit = 1}
  elsif(1 == $printit){print}
}
