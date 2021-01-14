# projective-prover : a plugin to use David Braun's automatic prover from projective geometry in Coq

Nicolas Magaud

This plugin transforms a Coq goal using the specification language of our automatic prover for projective geometry, computes a proof and then produces a trace as a Coq proof script, which is returned to Coq to be checked.

Work in progress, works with Coq 8.12.2 (December 2020).

# Quick start
- launching Coq in command-line mode : coqtop -I src -R theories Tuto0
- Loading the prover infrastructure inside Coq : Require Import Tuto0.Loader.

Available tactics are : pprove. or pprove 4.

# Scope

The prover deals with goals of the following shape :

Lemma ex2 : forall A B C D:Point,<br>
    rk(A::D::B::nil) = 3 -><br>
    rk(A::C::D::nil) = 2 -><br>
    rk(C::A::nil) = 2 -><br>
    rk(C::D::nil) = 2 -><br>
    rk(A::C::B::nil) = 3.<br>
Proof.

The conclusion must be of the form rk(e)=n and only variables of type Point and hypotheses of the form rk(e)=n are used. All other variables and hypotheses are ignored by the automatic prover.


# Links and related work
See https://github.com/pascalschreck/MatroidIncidenceProver for the implementation of the saturation procedure and the generation of the Coq script (calls "main file.stat").<br>
See also : https://github.com/ProjectiveGeometry/ProjectiveGeometry


# TODO
- ignore hypotheses which are not of the form rk(?e)=?v

- replace "find_reference" with "Coqlib.lib_ref"

- removes the call to "Vernacstate.Declare.get_current_proof_name"