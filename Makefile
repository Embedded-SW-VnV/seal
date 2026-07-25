.PHONY: build clean run-examples soundness-check \
	full-check full-check-pad0 full-check-pad-default full-check-thorough

build:
	dune build

clean:
	dune clean

# Quick smoke test (examples/run_examples.ml)
run-examples: build
	dune exec examples/run_examples.exe

# Exploratory diagnostics (examples/soundness_check_main.ml): simulation-based
# checks of individual analyses, not structured/aggregated (see full-check
# below for the CSV-producing non-regression sweep).
soundness-check: build
	dune exec examples/soundness_check_main.exe

# Full non-regression sanity sweep (examples/full_check_main.ml): every
# Analysis method x every example system x every degree/k parameter, each
# checked against simulated trajectories, one CSV row per run. Produces two
# CSVs, one per pad setting (see full_check_main.ml's header comment for
# what "pad" means and why both are worth comparing):
#   - full_check_pad0.csv:         pad=0 (the paper/Matlab experiments' own,
#                                   less conservative setting)
#   - full_check_pad_default.csv:  each method's regular/current default
#                                   (round/shape/affine/piecewise_lin: 2.;
#                                   prop_driven_sos_lyap/liouville_method: 0.)
#
# max_paths caps piecewise_lin's k-induction at a routine-runtime size (see
# full_check_main.ml). Measured directly on this machine: RunningExample's
# k=1 (4 paths, df=3) already takes ~2 minutes by itself, and its k=2 (17
# paths) ran for over an hour without converging -- SDP solve cost grows
# much faster than linearly in path count, so a path-count cap alone can't
# safely admit RunningExample's k=2/k=3 (17/73 paths) in a routine target.
# 15 keeps RunningExample at k=1 only, while still admitting
# MignoneInvariance1's k=1/k=2 (4/12 paths, a cheaper df=2 problem, found a
# real soundness issue at k=2 -- see full_check_main.ml's module doc).
# Raise it (or use full-check-thorough below) for an occasional, much
# slower, more complete run.
full-check-pad0: build
	dune exec examples/full_check_main.exe -- zero full_check_pad0.csv 15

full-check-pad-default: build
	dune exec examples/full_check_main.exe -- default full_check_pad_default.csv 15

full-check: full-check-pad0 full-check-pad-default

# Occasional, much slower run with no path-count cap: also exercises
# piecewise_lin's k=4 on every example (including the paper's 314-path
# "running example"), which can take upwards of an hour on its own.
full-check-thorough:
	dune exec examples/full_check_main.exe -- zero full_check_pad0_thorough.csv 100000
	dune exec examples/full_check_main.exe -- default full_check_pad_default_thorough.csv 100000
