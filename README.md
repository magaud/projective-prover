## projective-prover : a Coq plugin to use David Braun's automatic prover for projective geometry


* [General info](#general-info)
* [Scope](#scope)
* [Quick start](#quick-start)
* [Links and related work](#links)
* [TODO](#todo)

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

The main tactic is ````pprove```.
Ìf no argument is given to the tactic, we assume the dimension is 3. Alternatively, the tactic can be followed by an integer, which specifies the dimension of the considered space.



# Links and related work
- https://github.com/pascalschreck/MatroidIncidenceProver (the implementation of the saturation procedure and the generation of the Coq script - our plugin performs the following call: "main file.stat").
- https://github.com/ProjectiveGeometry/ProjectiveGeometry
- http://www.theses.fr/2019STRAD020


## TODO
- Coq internals
* ignore hypotheses which are not of the form rk(?e)=?v

* replace "find_reference" with "Coqlib.lib_ref"

* remove the call to "Vernacstate.Declare.get_current_proof_name"

- Proofs
* make a proof of DG property which creates points interactively and use the general instance to solve the goal