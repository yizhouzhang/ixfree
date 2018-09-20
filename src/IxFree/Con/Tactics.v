Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Con.Arrow.
Require Import IxFree.Con.Conj.
Require Import IxFree.Con.Disj.
Require Import IxFree.Con.Iff.
Require Import IxFree.Con.Forall.
Require Import IxFree.Con.Exists.
Require Import IxFree.Con.Later.

Ltac ielim_prop H := apply I_Prop_elim in H.
Ltac icontradict H := ielim_prop H ; contradict H.

Ltac iintro_prop :=
  apply I_Prop_intro.

Ltac iintro_named H :=
  iintro_arrow_named H ||
  iintro_forall_named H.
Ltac iintro_anon :=
  iintro_arrow_anon ||
  iintro_forall_anon ||
  iintro_later ||
  iintro_prop.

Tactic Notation "iintro" ident(H) := iintro_named H.
Tactic Notation "iintro" := iintro_anon.

Ltac iapply H :=
  first [ apply (I_arrow_elim H) | apply (I_forall_elim H) ].

Ltac iespecialize H :=
  repeat (eapply I_forall_elim in H).

Ltac ispecialize_arrow H :=
  let T := type of H in
  match T with
  | (?N ⊨ ?P ⇒ ?Q) =>
    let J := fresh in
    assert (J : N ⊨ Q); [ iapply H | clear H; rename J into H ]
  end.

Ltac ispecialize_forall H X :=
  let T := type of H in
  match T with
  | (?N ⊨ I_forall ?A ?P) =>
    let J := fresh in
    assert (J : N ⊨ P X); 
    [ apply (I_forall_elim H X) 
    | clear H; rename J into H; try (cbv beta in H) 
    ]
  end.

Tactic Notation "ispecialize" hyp(H) := ispecialize_arrow H.
Tactic Notation "ispecialize" hyp(H) constr(X) := ispecialize_forall H X.

Ltac igeneralize H :=
  let T := type of H in
  match T with
  | (?N ⊨ ?P) =>
    match goal with
    | [ |- (N ⊨ ?Q) ] =>
      let J := fresh in
      assert (N ⊨ P ⇒ Q); [ idtac | apply (I_arrow_elim J H) ]
    end
  end.

Tactic Notation "idestruct" hyp(H) "as" ident(x) ident(y) :=
  idestruct_conj H x y || idestruct_disj H x y || idestruct_exists H x y.

(* ========================================================================= *)
(* Tactics for ▷ *)

Lemma I_later_arrow_up {n : nat} {P Q : IProp} :
  (n ⊨ ▷P ⇒ ▷Q) → (n ⊨ ▷(P ⇒ Q)).
Proof.
intro H; destruct n; [ apply I_later_zero | apply I_later_shift ].
apply I_arrow_intro; intros k Hle HP.
apply I_later_shift; eapply I_arrow_elim.
  eapply I_valid_monotone; [ | eassumption ].
  apply Le.le_n_S; eassumption.
apply I_later_shift; assumption.
Qed.

Lemma I_later_forall_up {n : nat} {A : Type} {P : A → IProp} :
  (n ⊨ ∀ᵢ x, ▷ P x) → (n ⊨ ▷ ∀ᵢ x, P x).
Proof.
intro H; destruct n; [ apply I_later_zero | apply I_later_shift ].
iintro x; eapply I_forall_elim in H.
apply I_later_shift; eassumption.
Qed.

Lemma I_later_iff_up {n : nat} {P Q : IProp} :
  (n ⊨ ▷P ⇔ ▷Q) → (n ⊨ ▷(P ⇔ Q)).
Proof.
intro H; idestruct H as H1 H2.
apply I_later_arrow_up in H1.
apply I_later_arrow_up in H2.
later_shift.
isplit ; assumption.
Qed.

Ltac later_down :=
  match goal with
  | [ |- _ ⊨ ▷ I_forall _ _ ] => apply I_later_forall_up
  | [ |- _ ⊨ ▷(_ ⇒ _) ] => apply I_later_arrow_up
  | [ |- _ ⊨ ▷(_ ⇔ _) ] => apply I_later_iff_up
  end.

Lemma I_later_arrow_down {n : nat} {P Q : IProp} :
  (n ⊨ ▷(P ⇒ Q)) → (n ⊨ ▷P ⇒ ▷Q).
Proof.
intro H; iintro HP; later_shift.
iapply H; assumption.
Qed.

Lemma I_later_iff_down {n : nat} {P Q : IProp} :
  (n ⊨ ▷(P ⇔ Q)) → (n ⊨ ▷P ⇔ ▷Q).
Proof.
intro H; isplit; apply I_later_arrow_down; later_shift;
  iintro; apply I_iff_elim_M in H; apply H; assumption.
Qed.

Lemma I_later_forall_down {n : nat} {A : Type} {P : A → IProp} :
  (n ⊨ ▷ ∀ᵢ x, P x) → (n ⊨ ∀ᵢ x, ▷ P x).
Proof.
intro H; iintro x; later_shift; iapply H.
Qed.

Ltac later_up := 
  match goal with
  | [ |- _ ⊨ _ ⇒ _ ] => apply I_later_arrow_down
  | [ |- _ ⊨ I_forall _ _ ] => apply I_later_forall_down
  | [ |- _ ⊨ _ ⇔ _ ] => apply I_later_iff_down
  end.
