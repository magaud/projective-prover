## projective-prover : a plugin to use David Braun's automatic prover from projective geometry in Coq
Nicolas Magaud

* [General info](#general-info)
* [Scope](#scope)
* [Quick start](#quick-start)
* [Links and related work](#links)
* [TODO] (#todo)

# General Info

This plugin transforms a Coq goal using the specification language of the automatic prover (Bip) for projective geometry, computes a proof and then produces a trace as a Coq proof script, which is returned to Coq to be checked.

Work in progress, works with Coq 8.13.2 (May 2021).

# Scope

The prover deals with goals of the following shape :
```
Lemma ex2 : forall A B C D:Point,
    rk(A::D::B::nil) = 3 ->
    rk(A::C::D::nil) = 2 ->
    rk(C::A::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    rk(A::C::B::nil) = 3.
Proof.
```
The conclusion must be of the form rk(e)=n and only variables of type Point and hypotheses of the form rk(e)=n are used. All other variables and hypotheses are ignored by the automatic prover.


# Quick start
- launching Coq in command-line mode :
```
coqtop -I src -R theories Tuto0
```
- Loading the prover infrastructure inside Coq :
```
Require Import Tuto0.Loader.
```

Available tactics are : pprove. or pprove 4.


# Links and related work
See https://github.com/pascalschreck/MatroidIncidenceProver for the implementation of the saturation procedure and the generation of the Coq script (our plugin performs the following call: "main file.stat").<br>
See also : https://github.com/ProjectiveGeometry/ProjectiveGeometry


## TODO
- Coq internals
* ignore hypotheses which are not of the form rk(?e)=?v

* replace "find_reference" with "Coqlib.lib_ref"

* remove the call to "Vernacstate.Declare.get_current_proof_name"

- Proofs
* make a proof of DG property which creates points interactively and use the general instance to solve the goal