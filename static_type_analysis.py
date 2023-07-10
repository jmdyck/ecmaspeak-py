#!/usr/bin/python3

# ecmaspeak-py/static_type_analysis.py:
# Perform static type analysis/inference on the spec's pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys

import shared

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

outdir = sys.argv[1]
shared.register_output_dir(outdir)
shared.spec.restore()

import pseudocode_semantics

pseudocode_semantics.do_static_type_analysis()

# vim: sw=4 ts=4 expandtab
