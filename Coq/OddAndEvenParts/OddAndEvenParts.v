Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Open Scope R_scope.

Require Import Psatz.

Definition evenPart : (R -> R) -> (R -> R) := fun f => fun x => (f x + f (-x)) * 0.5.
Definition oddPart  : (R -> R) -> (R -> R) := fun f => fun x => (f x - f (-x)) * 0.5.

Definition isEven (f : R -> R) := forall (x : R), f (-x) =   (f x).
Definition isOdd  (f : R -> R) := forall (x : R), f (-x) = - (f x).

Theorem evenPartIsEven : forall (f : R -> R), isEven (evenPart f).
Proof.
  intros.
  unfold isEven.
  intros.
  unfold evenPart.
  rewrite Ropp_involutive with (r := x).
  rewrite Rplus_comm with (r1 := f x) (r2 := f (-x)).
  reflexivity.
Qed.

Theorem oddPartIsOdd : forall (f : R -> R), isOdd (oddPart f).
Proof.
  intros.
  unfold isOdd.
  intros.
  unfold oddPart.
  rewrite Ropp_involutive with (r := x).
  rewrite Rmult_minus_distr_r with (r1 := 0.5) (r2 := f x) (r3 := f (-x)).
  rewrite Ropp_minus_distr with (r1 := f x * 0.5) (r2 := f (-x) * 0.5).
  rewrite <- Rmult_minus_distr_r with (r1 := 0.5) (r2 := f (-x)) (r3 := f x).
  reflexivity.
Qed.

Theorem fIsEvenPlusOdd : forall (f : R -> R) (x : R), f x = evenPart f x + oddPart f x.
Proof.
  intros.
  unfold evenPart.
  unfold oddPart.
  lra.
Qed.
