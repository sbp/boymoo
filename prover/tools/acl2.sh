#!/bin/sh
# Runs ACL2 on its standard input with a heap of 1500 megabytes.  From the
# root of the repository:
#
#     sh prover/tools/acl2.sh < FORMS > OUTPUT
#
# Always run ACL2 through this script.
SBCL_USER_ARGS="--dynamic-space-size 1500"
export SBCL_USER_ARGS
exec acl2 "$@"
