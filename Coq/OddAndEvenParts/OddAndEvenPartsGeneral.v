Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.setoid_ring.Field_theory.
Require Import Coq.setoid_ring.Ring_theory.

Section FieldProperties.

  Context {F : Type}.
  Context {zero one : F}.
  Context {add mul sub : F -> F -> F}.
  Context {opp inv : F -> F}.
  Context {div : F -> F -> F}.

  (* Declare notation and scope for the field *)
  Declare Scope field_scope.
  Notation "0" := zero : field_scope.
  Notation "1" := one : field_scope.
  Notation "x + y" := (add x y) : field_scope.
  Notation "2" := (add one one) : field_scope.
  Notation "x * y" := (mul x y) : field_scope.
  Notation "x - y" := (sub x y) : field_scope.
  Notation "- x" := (opp x) : field_scope.
  Notation "x / y" := (div x y) : field_scope.
  Notation "/ x" := (inv x) : field_scope.
  Delimit Scope field_scope with F.

  Open Scope field_scope.

  Context {eq_refl : forall x : F, x = x}.
  Context {eq_sym : forall x y : F, x = y -> y = x}.
  Context {eq_trans : forall x y z : F, x = y -> y = z -> x = z}.
  Context {neq_1_0 : 1 <> 0}.
  Context {neq_2_0 : 2 <> 0}.
  Context {add_comm : forall x y : F, (x + y) = (y + x)}.
  Context {add_assoc : forall x y z : F, ((x + y) + z) = (x + (y + z))}.
  Context {add_0_l : forall x : F, (0 + x) = x}.
  Context {add_0_r : forall x : F, x + 0 = x}.
  Context {add_opp_r : forall x : F, x + (- x) = 0}.
  Context {mul_comm : forall x y : F, (x * y) = (y * x)}.
  Context {mul_assoc : forall x y z : F, (x * (y * z)) = ((x * y) * z)}.
  Context {mul_1_l : forall x : F, (1 * x) = x}.
  Context {mul_1_r : forall x : F, (x * 1) = x}.
  Context {mul_add_distr_l : forall x y z : F, (x * (y + z)) = ((x * y) + (x * z))}.
  Context {mul_add_distr_r : forall x y z : F, (x + y) * z = (x * z) + (y * z)}.
  Context {sub_def : forall x y : F, (x - y) = (x + (- y))}.
  Context {opp_def : forall x : F, (x + (- x)) = 0}.
  Context {opp_involutive : forall x : F, - (- x) = x}.
  Context {div_def : forall x y : F, (x / y) = (x * (/ y))}.
  Context {inv_mul : forall x : F, ~ x = 0 -> (x * (/ x)) = 1}.
  Context {mul_sub_distr_r : forall r1 r2 r3 : F, (r2 - r3) * r1 = (r2 * r1) - (r3 * r1)}.
  Context {opp_sub_distr : forall r1 r2 : F, - (r1 - r2) = r2 - r1}.

  Context {F_field_theory : field_theory zero one add mul sub opp div inv eq}.

  (* Definitions of even and odd parts for functions over a field *)
  Definition evenPart (f : F -> F) : F -> F := fun x => (f x + f (- x)) * / 2.
  Definition oddPart  (f : F -> F) : F -> F := fun x => (f x - f (- x)) * / 2.

  (* Definitions of even and odd functions *)
  Definition isEven (f : F -> F) := forall x : F, f (- x) = f x.
  Definition isOdd  (f : F -> F) := forall x : F, f (- x) = - f x.

  Theorem evenPartIsEven : forall (f : F -> F), isEven (evenPart f).
  Proof.
    intros.
    unfold isEven, evenPart.
    intros.
    rewrite opp_involutive.
    rewrite (add_comm (f x) (f (- x))).
    reflexivity.
  Qed.

  Theorem oddPartIsOdd : forall (f : F -> F), isOdd (oddPart f).
  Proof.
    intros.
    unfold isOdd, oddPart.
    intros.
    rewrite opp_involutive.
    rewrite mul_sub_distr_r with (r1 := /2) (r2 := f x) (r3 := f (-x)).
    rewrite opp_sub_distr with (r1 := f x * /2) (r2 := f (-x) * /2).
    rewrite <- mul_sub_distr_r with (r1 := /2) (r2 := f (-x)) (r3 := f x).
    reflexivity.
  Qed.

 Theorem fIsEvenPlusOdd : forall (f : F -> F) (x : F), f x = evenPart f x + oddPart f x.
  Proof.
    intros.
    (*
      f x = evenPart f x + oddPart f x
    *)

    unfold evenPart, oddPart.
    (*
      f x = (f x + f (- x)) * /2 + (f x - f (- x)) * /2
    *)

    rewrite mul_add_distr_r.
    rewrite mul_sub_distr_r.
    (*
      f x = f x * /2 + f (- x) * /2 + (f x * /2 - f (- x) * /2)
      f x = (f x * /2 + f (- x) * /2) + (f x * /2 - f (- x) * /2)
    *)
    
    rewrite sub_def.
    (*
      f x = f x * /2 + f (- x) * /2 + (f x * /2 + - (f (- x) * /2))
    *)

    rewrite <- add_assoc with (x := f x * /2 + f (- x) * /2) (y := f x * /2) (z := - (f (- x) * /2)).
    rewrite add_assoc with (x := f x * /2) (y := f (- x) * /2) (z := f x * /2).
    rewrite add_comm with (x := f (- x) * /2) (y := f x * /2).
    rewrite add_assoc.
    rewrite add_assoc.
    rewrite add_opp_r.
    rewrite add_0_r.
    (*
      f x = f x * / 2 + f x * / 2
    *)

    rewrite <- mul_add_distr_l with (x := f x) (y := /2) (z := /2).
    rewrite <- mul_1_l with (x := /2).
    rewrite <- mul_add_distr_r.
    rewrite inv_mul by apply neq_2_0.
    rewrite mul_1_r.
    (*
      f x = f x
    *)

    reflexivity.
  Qed.

End FieldProperties.