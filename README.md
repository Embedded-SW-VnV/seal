# Seal

> **Work in progress — do not rely on its results.** Seal is under active
> development: interfaces, representations and results may change without
> notice. Some analyses are **known to return unsound invariants** in some
> cases: `prop_driven_sos_lyap` at high template degrees (>= 6), because of
> the numerical conditioning of the monomial basis, and `liouville_method`
> on some systems (e.g. Thao8.3), with violations near the initial region.
> This list may not be exhaustive. These gaps are diagnosed but not fixed
> yet (see the comments in
> `lib/templates/propSOSTemplates.ml` and `lib/liouville.ml`). Every result
> should be checked independently, e.g. with the simulation-based harness
> `make full-check` (see below); some templates are also incomplete or
> unreliable on larger problems (see the notes in
> `examples/run_examples.ml`).

Seal is an OCaml library for the analysis of dynamical systems (linear,
piecewise-linear, and polynomial) via invariant synthesis, built on
sum-of-squares (SOS) programming and semidefinite programming solvers
through [OSDP](https://cavale.enseeiht.fr/osdp/).

It provides:

- A representation layer for linear, piecewise-linear and polynomial
  discrete-time dynamical systems, with guarded modes and casts between
  linear and polynomial forms (`Seal.Dynsys`).
- Quadratic invariant templates (round / shape / affine) for linear systems.
- k-inductive piecewise-quadratic invariant synthesis for piecewise-linear
  systems.
- Property-directed SOS Lyapunov-style invariant synthesis and per-variable
  reachable-set bounds for polynomial systems.
- A reachability invariant synthesis method based on Liouville's equation
  for polynomial systems.

## Building

Seal uses [dune](https://dune.build) and depends on
[`osdp`](https://cavale.enseeiht.fr/osdp/), `num`, `zarith` and
`ocplib-simplex`.

Seal currently needs `osdp` features not yet in a released version
(the latest release on the official opam repository is 1.1.1). Until a
new `osdp` release is published there, `seal.opam` pins `osdp` to the
[`dev` branch](https://github.com/Embedded-SW-VnV/osdp/tree/dev) via
`pin-depends`, so a plain `opam install .` from a clone of this repo
resolves it automatically. **Seal is not yet published on the official
opam repository** (packages there cannot use `pin-depends`), so
`opam install seal` will not work until that `osdp` release lands.

```sh
git clone https://github.com/Embedded-SW-VnV/seal.git
cd seal
opam install . --deps-only
dune build
dune runtest
```

## Usage

See `examples/` for sample dynamical systems and `examples/run_examples.ml`
for a smoke-test driver exercising the library end-to-end (representation
casts, quadratic templates, piecewise-quadratic invariants, property-driven
SOS templates, and reachability bounds).

```sh
dune exec examples/run_examples.exe
```

To check the invariants against simulated trajectories:

- `make soundness-check` runs `examples/soundness_check_main.ml` on a few
  purpose-built systems;
- `make full-check` runs every analysis on every example system (sweeping
  the degree or the path length k), checks each invariant against
  simulated trajectories, writes one CSV row per run, and prints a summary
  classifying each failure as unsound or imprecise (`make
  full-check-summary` re-prints it from the existing CSVs).

## References

Seal implements methods described in the following publications:

- Pierre-Loïc Garoche. *Formal Verification of Control System Software*.
  Princeton University Press, 2019.
- Victor Magron, Pierre-Loïc Garoche, Didier Henrion, Xavier Thirioux.
  *Semidefinite Approximations of Reachable Sets for Discrete-time
  Polynomial Systems*. SIAM J. Control Optim. 57(4): 2799-2820 (2019).
- Assalé Adjé, Pierre-Loïc Garoche. *Automatic synthesis of k-inductive
  piecewise quadratic invariants for switched affine control programs*.
  Comput. Lang. Syst. Struct. 47: 44-61 (2017).
- Assalé Adjé, Pierre-Loïc Garoche, Victor Magron. *Property-based
  Polynomial Invariant Generation Using Sums-of-Squares Optimization*.
  SAS 2015: 235-251.
- Assalé Adjé, Pierre-Loïc Garoche. *Automatic Synthesis of Piecewise
  Linear Quadratic Invariants for Programs*. VMCAI 2015: 99-116.
- Pierre Roux, Romain Jobredeaux, Pierre-Loïc Garoche, Eric Feron. *A
  generic ellipsoid abstract domain for linear time invariant systems*.
  HSCC 2012: 105-114.

## License

Seal is distributed under the GNU Lesser General Public License, version 3
or later (LGPL-3.0-or-later). See [LICENSE](LICENSE) for the full text.

## Authors

Pierre-Loïc Garoche (ENAC) — pierre-loic.garoche@enac.fr
