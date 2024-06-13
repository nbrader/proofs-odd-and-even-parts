Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Section ThreeValuedField.

  (* Define the type F as integers with values restricted to -1, 0, and 1 *)
  Inductive TV : Type :=
    | TVn : TV (* -1 *)
    | TVz : TV (* 0 *)
    | TVp : TV (* 1 *).

  (* Define the max operation as the add function *)
  Definition TVadd (x y : TV) : TV :=
    match x, y with
    | TVp, _ => TVp
    | _, TVp => TVp
    | TVz, _ => y
    | _, TVz => x
    | TVn, TVn => TVn
    end.

  (* Define the min operation as the mul function *)
  Definition TVmul (x y : TV) : TV :=
    match x, y with
    | TVp, TVp => TVp
    | TVn, TVn => TVp
    | TVz, _ => TVz
    | _, TVz => TVz
    | TVp, TVn => TVn
    | TVn, TVp => TVn
    end.

  Definition TVopp (x : TV) : TV :=
    match x with
    | TVp => TVn
    | TVz => TVz
    | TVn => TVp
    end.

  Definition TVinv (x : TV) : TV := x.

  Definition TVsub (x y : TV) : TV := TVadd x (TVopp y).

  Definition TVdiv (x y : TV) : TV := TVmul x (TVinv y).

  Variable F : Type.
  Variable zero one : F.
  Variable add mul sub : F -> F -> F.
  Variable opp inv : F -> F.
  Variable div : F -> F -> F.

  Declare Scope field_scope.
  Notation "0" := zero : field_scope.
  Notation "1" := one : field_scope.
  Notation "x + y" := (add x y) : field_scope.
  Notation "2" := (add one one) : field_scope.
  Notation "x * y" := (mul x y) : field_scope.
  Notation "x - y" := (sub x y) : field_scope.
  Notation "- x" := (opp x) : field_scope.
  Notation "/ x" := (inv x) : field_scope.

  Open Scope field_scope.

  Variable neq_2_0 : 2 <> 0.
  Variable add_comm : forall x y : F, (x + y) = (y + x).
  Variable add_assoc : forall x y z : F, ((x + y) + z) = (x + (y + z)).
  Variable add_0_r : forall x : F, x + 0 = x.
  Variable add_opp_r : forall x : F, x + (- x) = 0.
  Variable mul_1_l : forall x : F, (1 * x) = x.
  Variable mul_1_r : forall x : F, (x * 1) = x.
  Variable mul_add_distr_l : forall x y z : F, (x * (y + z)) = ((x * y) + (x * z)).
  Variable mul_add_distr_r : forall x y z : F, (x + y) * z = (x * z) + (y * z).
  Variable sub_def : forall x y : F, (x - y) = (x + (- y)).
  Variable opp_involutive : forall x : F, - (- x) = x.
  Variable inv_mul : forall x : F, ~ x = 0 -> (x * (/ x)) = 1.
  Variable mul_sub_distr_r : forall r1 r2 r3 : F, (r2 - r3) * r1 = (r2 * r1) - (r3 * r1).
  Variable opp_sub_distr : forall r1 r2 : F, - (r1 - r2) = r2 - r1.

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

End ThreeValuedField.

(* Assign F to TV and use theorems *)
Module ApplyThreeValuedField.

  (* Instantiating the field with the three-valued number system *)
  Definition F := TV.
  Definition zero := TVz.
  Definition one := TVp.
  Definition add := TVadd.
  Definition mul := TVmul.
  Definition sub := TVsub.
  Definition opp := TVopp.
  Definition inv := TVinv.
  Definition div := TVdiv.

  Definition neq_2_0 : (TVadd TVp TVp) <> TVz.
  Proof.
    unfold TVadd. discriminate.
  Qed.

  Declare Scope field_scope.
  Notation "0" := zero : field_scope.
  Notation "1" := one : field_scope.
  Notation "x + y" := (add x y) : field_scope.
  Notation "2" := (add one one) : field_scope.
  Notation "x * y" := (mul x y) : field_scope.
  Notation "x - y" := (sub x y) : field_scope.
  Notation "- x" := (opp x) : field_scope.
  Notation "/ x" := (inv x) : field_scope.

  Open Scope field_scope.

  Definition add_comm : forall x y : F, (x + y) = (y + x).
  Proof.
    intros. unfold add, TVadd. destruct x, y; reflexivity.
  Qed.

  Definition add_assoc : forall x y z : F, ((x + y) + z) = (x + (y + z)).
  Proof.
    intros. unfold add, TVadd. destruct x, y, z; reflexivity.
  Qed.

  Definition add_0_r : forall x : F, x + 0 = x.
  Proof.
    intros. unfold add, zero, TVadd. destruct x; reflexivity.
  Qed.

  (* Definition add_opp_r : forall x : F, x + (- x) = 0.
  Proof.
    intros. unfold add, opp, zero, TVadd, TVopp. destruct x; reflexivity.
  Qed. *)

  Definition mul_1_l : forall x : F, (1 * x) = x.
  Proof.
    intros. unfold mul, one, TVmul. destruct x; reflexivity.
  Qed.

  Definition mul_1_r : forall x : F, (x * 1) = x.
  Proof.
    intros. unfold mul, one, TVmul. destruct x; reflexivity.
  Qed.

  (* Definition mul_add_distr_l : forall x y z : F, (x * (y + z)) = ((x * y) + (x * z)).
  Proof.
    intros. unfold mul, add, TVmul, TVadd. destruct x, y, z; reflexivity.
  Qed. *)

  (* Definition mul_add_distr_r : forall x y z : F, (x + y) * z = (x * z) + (y * z).
  Proof.
    intros. unfold mul, add, TVmul, TVadd. destruct x, y, z; reflexivity.
  Qed. *)

  Definition sub_def : forall x y : F, (x - y) = (x + (- y)).
  Proof.
    intros. unfold sub, add, opp, TVsub, TVadd, TVopp. reflexivity.
  Qed.

  Definition opp_involutive : forall x : F, - (- x) = x.
  Proof.
    intros. unfold opp, TVopp. destruct x; reflexivity.
  Qed.

  Definition inv_mul : forall x : F, ~ x = zero -> (x * (/ x)) = one.
  Proof.
    intros. unfold mul, inv, one, TVmul, TVinv. destruct x; try contradiction; reflexivity.
  Qed.

  (* Definition mul_sub_distr_r : forall r1 r2 r3 : F, (r2 - r3) * r1 = (r2 * r1) - (r3 * r1).
  Proof.
    intros. unfold mul, sub, TVmul, TVsub, TVadd, TVopp. destruct r1, r2, r3; reflexivity.
  Qed. *)

  (* Definition opp_sub_distr : forall r1 r2 : F, - (r1 - r2) = r2 - r1.
  Proof.
    intros. unfold sub, opp, TVsub, TVadd, TVopp. destruct r1, r2; reflexivity.
  Qed. *)

  (* Define a polynomial function f(x) = x^3 + x *)
  Definition poly1 (x : F) : F := add (mul (mul x x) x) x.

  (* Apply the theorems to the three-valued number system *)
  Compute (evenPart _ _ _ _ _ _ poly1 TVn).
  Compute (oddPart _ _ _ _ _ _ _ poly1 TVn).
  Compute (evenPart _ _ _ _ _ _ poly1 TVz).
  Compute (oddPart _ _ _ _ _ _ _ poly1 TVz).
  Compute (evenPart _ _ _ _ _ _ poly1 TVp).
  Compute (oddPart _ _ _ _ _ _ _ poly1 TVp).

  (* Example to verify the sum of even and odd parts equals the original polynomial *)
  (* Example poly_even_odd_sum : forall x : F, poly1 x = TVadd (evenPart _ _ _ _ _ _ poly1 x) (oddPart _ _ _ _ _ _ _ poly1 x).
  Proof.
    intros x.
    unfold evenPart, oddPart.
    unfold poly1.
    rewrite add_comm.
    rewrite sub_def.
    rewrite opp_involutive.
    rewrite mul_sub_distr_r.
    rewrite mul_add_distr_r.
    rewrite add_opp_r.
    rewrite add_0_r.
    rewrite mul_1_l.
    reflexivity.
  Qed. *)

End ApplyThreeValuedField.
