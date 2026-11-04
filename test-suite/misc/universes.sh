#!/bin/sh
# Sort universes for the whole standard library.
# Prop is not counted. Corelib and Ltac2 need two (Set < Type.0 < Type.1).
# The third appears once Stdlib is included: Hurkens uses monomorphic
# eq_rect on an equality between Type and a smaller type, so eq_rect's
# carrier universe sits strictly above that top (Type.1 < Type.2).
# Corelib.Gradual.Gradual.gradual is an alias of Type.0, not a new level.
EXPECTED_UNIVERSES=3
$coqc -R misc/universes Universes misc/universes/all_stdlib 2>&1
$coqc -R misc/universes Universes misc/universes/universes 2>&1
mv universes.txt misc/universes
N=$(awk '{print $3}' misc/universes/universes.txt | sort -u | wc -l)
printf "Found %s/%s universes\n" "$N" "$EXPECTED_UNIVERSES"
if [ "$N" -eq $EXPECTED_UNIVERSES ]; then exit 0; else exit 1; fi
