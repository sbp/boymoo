#!/bin/sh
# Run from the repository root. With three file arguments, replay one input.
exec python3 -B review/steps/replay.py "$@"
