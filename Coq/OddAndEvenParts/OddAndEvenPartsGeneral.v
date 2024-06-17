Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Section FiniteFieldModulo3.

  (* Define the type F as integers with values restricted to 0, 1, and 2 *)
  Inductive F3 : Type :=
    | F0 : F3 (* 0 *)
    | F1 : F3 (* 1 *)
    | F2 : F3 (* 2 *).

  (* Define the addition operation modulo 3 *)
  Definition F3add (x y : F3) : F3 :=
    match x, y with
    | F0, y => y
    | x, F0 => x
    | F1, F1 => F2
    | F1, F2 => F0
    | F2, F1 => F0
    | F2, F2 => F1
    end.

  (* Define the multiplication operation modulo 3 *)
  Definition F3mul (x y : F3) : F3 :=
    match x, y with
    | F0, _ => F0
    | _, F0 => F0
    | F1, y => y
    | x, F1 => x
    | F2, F2 => F1
    end.

  (* Define the negation operation modulo 3 *)
  Definition F3add_inv (x : F3) : F3 :=
    match x with
    | F0 => F0
    | F1 => F2
    | F2 => F1
    end.

  (* Define the inversion operation modulo 3 *)
  Definition F3inv (x : F3) : F3 :=
    match x with
    | F0 => F0 (* Not defined, but here represented as F0 *)
    | F1 => F1
    | F2 => F2
    end.

  Definition F3sub (x y : F3) : F3 := F3add x (F3add_inv y).

  Definition F3div (x y : F3) : F3 := F3mul x (F3inv y).

  (* Redefine the field structure *)
  Variable F : Type.
  Variable zero one : F.
  Variable add mul sub : F -> F -> F.
  Variable add_inv inv : F -> F.
  Variable div : F -> F -> F.

  Declare Scope field_scope.
  Notation "0" := zero : field_scope.
  Notation "1" := one : field_scope.
  Notation "x + y" := (add x y) : field_scope.
  Notation "2" := (add one one) : field_scope.
  Notation "x * y" := (mul x y) : field_scope.
  Notation "x - y" := (sub x y) : field_scope.
  Notation "- x" := (add_inv x) : field_scope.
  Notation "/ x" := (inv x) : field_scope.

  Open Scope field_scope.
  
  Variable add_assoc : forall x y z : F, (x + y) + z = x + (y + z).
  Variable add_0_r : forall x : F, x + 0 = x.
  Variable add_inv_r : forall x : F, x + (- x) = 0.
  Variable add_comm : forall x y : F, x + y = y + x.
  Variable mul_1_l : forall x : F, 1 * x = x.
  Variable mul_1_r : forall x : F, x * 1 = x.
  Variable mul_inv : forall x : F, x <> 0 -> x * (/ x) = 1.
  Variable mul_add_distr_l : forall x y z : F, x * (y + z) = (x * y) + (x * z).
  Variable mul_add_distr_r : forall x y z : F, (x + y) * z = x * z + y * z.
  Variable sub_def : forall x y : F, x - y = x + (- y).
  Variable mul_sub_distr_r : forall r1 r2 r3 : F, (r2 - r3)*r1 = r2 * r1 - r3 * r1.
  Variable add_inv_sub_distr : forall r1 r2 : F, - (r1 - r2) = r2 - r1.
  Variable neq_1_0 : 1 <> 0.

  Variable neq_2_0 : 2 <> 0.

  Lemma add_0_l : forall x : F, 0 + x = x.
  Proof.
    intro.
    rewrite add_comm.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma add_inv_involutive : forall x : F, - (- x) = x.
  Proof.
    intro.
    rewrite <- add_0_r with (x := --x).
    rewrite <- add_inv_r with (x := x).
    rewrite add_comm with (x := x) (y := -x).
    rewrite <- add_assoc with (x := --x) (y := -x) (z := x).
    rewrite add_comm with (x := --x) (y := -x).
    rewrite add_inv_r with (x := -x).
    rewrite add_0_l.
    reflexivity.
  Qed.

  Lemma add_0_unique : forall (y : F), (forall x : F, x + y = x) -> y = 0.
  Proof.
    intros.
    specialize (H 0).
    rewrite add_comm in H.
    rewrite add_0_r in H.
    apply H.
  Qed.

  Lemma add_0_unique_2 : forall (y : F), y = 0 -> (forall x : F, x + y = x).
  Proof.
    intros.
    rewrite H.
    apply add_0_r.
  Qed.

  Lemma add_inv_unique : forall x y : F, y + x = 0 -> y = -x.
  Proof.
    intros.
    rewrite <- add_0_r with (x := y).
    rewrite <- add_inv_r with (x := x).
    rewrite <- add_assoc with (x := y) (y := x) (z := -x).
    rewrite H.
    rewrite add_0_l.
    reflexivity.
  Qed.

  Definition mul_comm := forall x y : F, x * y = y * x.
  Definition mul_assoc := forall x y z : F, (x * y) * z = x * (y * z).
  Definition mul_inv_nonzero := forall x : F, x <> 0 -> /x <> 0.

  Lemma mul_inv_unique (Hmul_assoc : mul_assoc) : forall x y : F, x <> 0 -> y * x = 1 -> y = /x.
  Proof.
    intros.
    rewrite <- mul_1_r with (x := y).
    rewrite <- mul_inv with (x := x).
    - rewrite <- Hmul_assoc with (x := y) (y := x) (z := /x).
      rewrite H0.
      rewrite mul_1_l.
      reflexivity.
    - apply H.
  Qed.

  Lemma mul_inv_involutive_2 (Hmul_comm : mul_comm) (Hmul_assoc : mul_assoc) (Hmul_inv_nonzero : mul_inv_nonzero) : forall x : F, x <> 0 -> x = //x.
  Proof.
    intros.
    assert (//x * /x = 1).
    - rewrite <- Hmul_comm with (x := /x).
      rewrite mul_inv with (x := /x).
      reflexivity.
      apply Hmul_inv_nonzero.
      apply H.
    - assert (x * /x = 1).
      + apply mul_inv.
        apply H.
      + assert (/x <> 0).
        * apply Hmul_inv_nonzero.
          apply H.
        * apply (mul_inv_unique Hmul_assoc (/x) x H2).
          apply mul_inv.
          apply H.
  Qed.

  Lemma mul_inv_involutive (Hmul_comm : mul_comm) (Hmul_assoc : mul_assoc) (Hmul_inv_nonzero : mul_inv_nonzero) : forall x : F, x <> 0 -> //x = x.
  Proof.
    intros.
    rewrite <- mul_1_r with (x := //x).
    rewrite <- mul_inv with (x := x).
    rewrite Hmul_comm with (x := x) (y := /x).
    rewrite <- Hmul_assoc with (x := //x) (y := /x) (z := x).
    rewrite Hmul_comm with (x := //x) (y := /x).
    rewrite mul_inv with (x := /x).
    rewrite mul_1_l.
    reflexivity.
    - apply Hmul_inv_nonzero.
      apply H.
    - apply H.
  Qed.

  Lemma add_perserves_add_l : forall x y z : F, z + x = z + y <-> x = y.
  Proof.
    split.
    - intros.
      rewrite <- add_0_l with (x := x) at 1.
      rewrite <- add_inv_r with (x := z).
      rewrite add_comm with (x := z) (y := - z).
      rewrite add_assoc.
      rewrite H.
      rewrite <- add_assoc.
      rewrite <- add_comm with (x := z) (y := - z).
      rewrite add_inv_r.
      rewrite <- add_0_l.
      reflexivity.
    - intros.
      rewrite H.
      reflexivity.
  Qed.

  Lemma add_perserves_add_r : forall x y z : F, x + z = y + z <-> x = y.
  Proof.
    split.
    - intros.
      rewrite <- add_0_r with (x := x) at 1.
      rewrite <- add_inv_r with (x := z).
      rewrite <- add_assoc.
      rewrite H.
      rewrite add_assoc.
      rewrite add_inv_r.
      rewrite add_0_r.
      reflexivity.
    - intros.
      rewrite H.
      reflexivity.
  Qed.

  Lemma add_idemp_0 : forall x : F, x + x = x -> x = 0.
  Proof.
    intros.
    rewrite <- add_perserves_add_r with (x := x+x) (y := x) (z := -x) in H.
    rewrite add_assoc in H.
    rewrite add_inv_r in H.
    rewrite add_0_r in H.
    apply H.
  Qed.

  Lemma add_involutive_0_r : forall x : F, x = 0 -> x = -x.
  Proof.
    intros.
    rewrite H.
    rewrite <- add_0_l.
    rewrite add_inv_r.
    reflexivity.
  Qed.

  Lemma mul_0_r : forall x : F, x*0 = 0.
  Proof.
    intros.
    apply add_idemp_0.
    rewrite <- mul_add_distr_l.
    rewrite add_0_l.
    reflexivity.
  Qed.

  Lemma mul_neg_1_inv : forall x : F, x*-(1) = -x.
  Proof.
    intros.
    apply add_perserves_add_l with (x := x * -(1)) (y := -x) (z := x).
    rewrite <- mul_1_r with (x := x) at 1.
    rewrite <- mul_add_distr_l.
    rewrite add_inv_r.
    rewrite add_inv_r.
    apply mul_0_r.
  Qed.

  Lemma neg_1_sqr : - (1) * - (1) = 1.
  Proof.
    rewrite <- add_0_r at 1.
    rewrite <- add_inv_r with (x := -(1)).
    rewrite add_inv_involutive.
    rewrite <- add_assoc.
    rewrite <- mul_1_r with (x := -(1)) at 3.
    rewrite <- mul_add_distr_l with (x := -(1)).
    rewrite add_comm with (x := - (1)) (y := 1).
    rewrite add_inv_r.
    rewrite mul_0_r.
    rewrite add_0_l.
    reflexivity.
  Qed.

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
    rewrite add_inv_involutive.
    rewrite (add_comm (f x) (f (- x))).
    reflexivity.
  Qed.

  Theorem oddPartIsOdd : forall (f : F -> F), isOdd (oddPart f).
  Proof.
    intros.
    unfold isOdd, oddPart.
    intros.
    rewrite add_inv_involutive.
    rewrite mul_sub_distr_r with (r1 := /2) (r2 := f x) (r3 := f (-x)).
    rewrite add_inv_sub_distr with (r1 := f x * /2) (r2 := f (-x) * /2).
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
    rewrite add_inv_r.
    rewrite add_0_r.
    (*
      f x = f x * / 2 + f x * / 2
    *)

    rewrite <- mul_add_distr_l with (x := f x) (y := /2) (z := /2).
    rewrite <- mul_1_l with (x := /2).
    rewrite <- mul_add_distr_r.
    rewrite mul_inv by apply neq_2_0.
    rewrite mul_1_r.
    (*
      f x = f x
    *)

    reflexivity.
  Qed.

End FiniteFieldModulo3.

(* Assign F to F3 and use theorems *)
Module ApplyFiniteFieldModulo3.

  (* Instantiating the field with the finite field modulo 3 *)
  Definition F := F3.
  Definition zero := F0.
  Definition one := F1.
  Definition add := F3add.
  Definition mul := F3mul.
  Definition sub := F3sub.
  Definition add_inv := F3add_inv.
  Definition inv := F3inv.
  Definition div := F3div.

  Definition neq_2_0 : (F3add F1 F1) <> F0.
  Proof.
    unfold F3add. discriminate.
  Qed.

  Declare Scope field_scope.
  Notation "0" := zero : field_scope.
  Notation "1" := one : field_scope.
  Notation "x + y" := (add x y) : field_scope.
  Notation "2" := (add one one) : field_scope.
  Notation "x * y" := (mul x y) : field_scope.
  Notation "x - y" := (sub x y) : field_scope.
  Notation "- x" := (add_inv x) : field_scope.
  Notation "/ x" := (inv x) : field_scope.

  Open Scope field_scope.

  Definition add_comm : forall x y : F, (x + y) = (y + x).
  Proof.
    intros. unfold add, F3add. destruct x, y; reflexivity.
  Qed.

  Definition add_assoc : forall x y z : F, ((x + y) + z) = (x + (y + z)).
  Proof.
    intros. unfold add, F3add. destruct x, y, z; reflexivity.
  Qed.

  Definition add_0_r : forall x : F, x + 0 = x.
  Proof.
    intros. unfold add, zero, F3add. destruct x; reflexivity.
  Qed.

  Definition add_inv_r : forall x : F, x + (- x) = 0.
  Proof.
    intros. unfold add, add_inv, zero, F3add, F3add_inv. destruct x; reflexivity.
  Qed.

  Definition mul_1_l : forall x : F, (1 * x) = x.
  Proof.
    intros. unfold mul, one, F3mul. destruct x; reflexivity.
  Qed.

  Definition mul_1_r : forall x : F, (x * 1) = x.
  Proof.
    intros. unfold mul, one, F3mul. destruct x; reflexivity.
  Qed.

  Definition mul_add_distr_l : forall x y z : F, (x * (y + z)) = ((x * y) + (x * z)).
  Proof.
    intros. unfold mul, add, F3mul, F3add. destruct x, y, z; reflexivity.
  Qed.

  Definition mul_add_distr_r : forall x y z : F, (x + y) * z = (x * z) + (y * z).
  Proof.
    intros. unfold mul, add, F3mul, F3add. destruct x, y, z; reflexivity.
  Qed.

  Definition sub_def : forall x y : F, (x - y) = (x + (- y)).
  Proof.
    intros. unfold sub, add, add_inv, F3sub, F3add, F3add_inv. reflexivity.
  Qed.

  Definition add_inv_involutive : forall x : F, - (- x) = x.
  Proof.
    intros. unfold add_inv, F3add_inv. destruct x; reflexivity.
  Qed.

  Definition mul_inv : forall x : F, ~ x = zero -> (x * (/ x)) = one.
  Proof.
    intros. unfold mul, inv, one, F3mul, F3inv. destruct x; try contradiction; reflexivity.
  Qed.

  Definition mul_sub_distr_r : forall r1 r2 r3 : F, (r2 - r3) * r1 = (r2 * r1) - (r3 * r1).
  Proof.
    intros. unfold mul, sub, F3mul, F3sub, F3add, F3add_inv. destruct r1, r2, r3; reflexivity.
  Qed.

  Definition add_inv_sub_distr : forall r1 r2 : F, - (r1 - r2) = r2 - r1.
  Proof.
    intros. unfold sub, add_inv, F3sub, F3add, F3add_inv. destruct r1, r2; reflexivity.
  Qed.

  (* Define a polynomial function f(x) = x^2 + x *)
  Definition poly1 (x : F) : F := (x * x) + x.

  Lemma poly1EventPart (Hmul_comm : mul_comm F mul) (Hmul_assoc : mul_assoc F mul) (Hmul_inv_nonzero : mul_inv_nonzero F 1 inv) (x : F) : evenPart F 1 add mul add_inv inv poly1 x = x * x.
  Proof.
    unfold evenPart, poly1.
    rewrite <- (mul_neg_1_inv F 0 1 add mul add_inv) at 1 2.
    rewrite Hmul_assoc with (x := x) (y := -(1)) (z := (x * - (1))).
    rewrite Hmul_comm with (x := - (1)) (y := (x * - (1))).
    rewrite Hmul_assoc.
    rewrite (neg_1_sqr F 0 1 add).
    rewrite mul_1_r.
    rewrite <- add_assoc.
    rewrite add_assoc with (x := x * x) (y := x) (z := x * x).
    rewrite add_comm with (x := x) (y := x * x).
    rewrite <- add_assoc.
    rewrite <- mul_1_r with (x := x * x) at 1 2.
    rewrite <- mul_add_distr_l with (x := x * x).
    rewrite add_assoc.
    rewrite add_inv_r.
    rewrite add_0_r.
    rewrite Hmul_assoc.
    rewrite mul_inv.
    rewrite mul_1_r.
    reflexivity.
    apply neq_2_0.

    apply add_assoc.
    apply add_0_r.
    apply add_inv_r.
    apply add_comm.
    apply mul_1_r.
    apply mul_add_distr_l.

    apply add_assoc.
    apply add_0_r.
    apply add_inv_r.
    apply add_comm.
    apply mul_1_r.
    apply mul_add_distr_l.
  Qed.

  (* Example to verify the sum of even and odd parts equals the original polynomial *)
  Example poly_even_odd_sum : forall x : F, poly1 x = add (evenPart F F1 add mul add_inv inv poly1 x) (oddPart F F1 add mul sub add_inv inv poly1 x).
  Proof.
    apply (fIsEvenPlusOdd F 0 1 add mul sub add_inv inv add_assoc add_0_r add_inv_r add_comm mul_1_l mul_1_r mul_inv mul_add_distr_l mul_add_distr_r sub_def mul_sub_distr_r neq_2_0 poly1).
  Qed.

End ApplyFiniteFieldModulo3.
