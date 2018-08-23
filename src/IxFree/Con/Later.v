Require Import Utf8.
Require Import List.
Require Import IxFree.Base.

Definition I_later_func (P : IProp) : nat → Prop :=
  λ n, 
  match n with
  | 0   => True
  | S n => n ⊨ P
  end.
Lemma I_later_func_monotone (P : IProp) :
  monotone (I_later_func P).
Proof.
unfold monotone; unfold I_later_func; simpl; intros n H₁.
destruct n; trivial; apply I_valid_monotone_S; auto.
Qed.

Definition I_later (P : IProp) : IProp :=
  mk_IProp (I_later_func P) (I_later_func_monotone P).

Notation "▷ P" := (I_later P) (at level 30).

Fixpoint IRel_later (l : list Type) : IRel l → IRel l :=
  match l return IRel l → IRel l with
  | nil    => λ R, ▷R
  | A :: l => λ R x, IRel_later l (R x)
  end.

Lemma I_later_zero (P : IProp) : 0 ⊨ ▷P.
Proof.
apply I_valid_intro; constructor.
Qed.

Lemma I_later_shift {n : nat} {P : IProp} :
  (S n ⊨ ▷P) <-> (n ⊨ P).
Proof.
split; intro H.
+ apply I_valid_elim in H; apply H.
+ apply I_valid_intro; apply H.
Qed.

Lemma I_later_intro {n : nat} (P : IProp) :
  (n ⊨ P) → (n ⊨ ▷ P).
Proof.
intro H; destruct n; [ apply I_later_zero | apply I_later_shift ].
apply I_valid_monotone_S; assumption.
Qed.

Lemma I_loeb_induction {n : nat} (P : IProp) :
  (∀ k, k ≤ n → (k ⊨ ▷P) → (k ⊨ P)) → (n ⊨ P).
Proof.
induction n; intro H; apply H; trivial.
+ apply I_later_zero.
+ apply I_later_shift.
  apply IHn; intros k Hle; apply H.
  constructor; assumption.
Qed.

(* ========================================================================= *)
(* Tactics *)

Ltac iintro_later :=
  apply I_later_intro.

Ltac later_shift :=
  match goal with
  | [ |- ?N ⊨ ▷ _ ] =>
    destruct N as [ | N ]; [ apply I_later_zero | apply I_later_shift ];
    repeat match goal with
    | [ H : S N ⊨ ▷ _ |- _ ] => apply (proj1 I_later_shift) in H
    | [ H : S N ⊨ _ |- _ ] => apply I_valid_monotone_S in H
    end
  end.

Ltac loeb_induction_named IH :=
  match goal with
  | [ |- ?N ⊨ ?P ] =>
    apply (@I_loeb_induction N P);
    let K  := fresh "K" in
    let L  := fresh "L" in
    intros K L IH;
    repeat 
      match goal with
      | [ A : N ⊨ ?R |- _ ] => 
        apply (I_valid_monotone R K N L) in A
      end;
    clear L;
    clear N;
    rename K into N
  end.

Tactic Notation "loeb_induction" ident(H) := loeb_induction_named H.
Tactic Notation "loeb_induction" :=
  let LöbIH := fresh "LöbIH" in loeb_induction_named LöbIH.

Lemma step_in_later_aux {P Q : IProp} {n : nat} :
  ((n ⊨ ▷P) → (n ⊨ ▷Q)) → ((n ⊨ ▷P) → (n ⊨ ▷Q)).
Proof.
auto.
Qed.

Ltac step_in_later :=
  match goal with
  | [ |- ?N ⊨ ?Q ] =>
    let HL := fresh "HL" in
    eapply step_in_later_aux; [ intro HL; later_shift | ]
  end.
