#!/bin/sh
set -e
# Script generating the contents of [_CoqProject] based on files [config/*].
# We use standard dune variable DUNE_SOURCEROOT to determine if the build
# system is dune. In a dune build, the [_CoqProject] is solely used for editor
# support.

echo "# Generated file, edit [config/*] instead."

echo
echo "# Search paths"
# Adding "-Q " prefix to all non-empty, non-comment lines of [config/paths].
cat config/paths | grep "^[^#]\+" | sed "s/^/-Q /"
# When building with dune, we also add the corresponding paths under dune's
# [_build] directory. This is done by adding the prefix "-Q $PWD/" to all
# non-empty, non-comment lines of [config/paths]. So for instance, this will
# complement an entry of the form "-Q dir coqdir" produced above, with an
# entry "-Q $PWD/dir coqdir". This relies on the fact that dune runs (a copy
# of) the current script in the corresponding path under [_build]. This is
# where ".vo" files actually end up in a dune build. Note that paths without
# the "$PWD/" prefix are given first, so that editors find the original ".v"
# sources (e.g., for "jump to definition") instead of their copy under the
# [_build] directory.
if [ -n "$DUNE_SOURCEROOT" ]; then
  cat config/paths | grep "^[^#]\+" | sed "s,^,-Q $PWD/,"
fi

echo
echo "# Flags"
# Adding "-arg " prefix to all non-empty, non-comment lines of [config/flags].
cat config/flags | grep "^[^#]\+" | sed "s/^/-arg /"

# Potential extra local configuration.
if [ -f config/local ]; then
  echo
  # We take the whole file; no need to strip comments.
  cat config/local
fi

# The list of source files is only needed for [coq_makefile] builds.
if [ -z "$DUNE_SOURCEROOT" ]; then
  echo
  echo "# Sources"
  # Take only non-empty, non-comment lines of [config/source-list].
  cat config/source-list | grep "^[^#]\+"
fi
