# projective-prover : a plugin to use David Braun's automatic prover from projective geometry in Coq

Nicolas Magaud

This plugin transforms a Coq goal using the specification language of our automatic prover for projective geometry, computes a proof and then produces a trace as a Coq proof script, which is returned to Coq to be checked.

Work in progress, works with Coq 8.12.2 (December 2020).

# Quick start
- launching Coq in command-line mode : coqtop -I src -R theories Tuto0
- Loading the prover infrastructure inside Coq : Require Import Tuto0.Loader.

See also : https://github.com/ProjectiveGeometry/ProjectiveGeometry

Using prouver-pascal directory (calls "main file.stat")

# TODO
- ignore hypotheses which are not of the form rk(?e)=?v

- replace "find_reference" with "Coqlib.lib_ref"
