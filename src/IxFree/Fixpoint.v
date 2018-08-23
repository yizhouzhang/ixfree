Require Import Utf8.
Require Import List.
Require Import IxFree.Base IxFree.Connectives IxFree.Relations.
Require Import IxFree.UnaryFixpoint IxFree.BinaryFixpoint.
Require Import IxFree.RelationCurry.
Require Import IxFree.Contractive.

Require Import Arith.

Module Private.

Lemma contractive_curry (l : list Type) :
  ∀ (f : IRel l → IRel l), contractive l f → 
  contractive (Prod l :: nil) 
    (λ R, IRel_uncurry _ (f (IRel_curry _ R))).
Proof.
unfold contractive; intros f Hcon R₁ R₂ n.
iintro HR.
iapply (IRel_uncurry_equiv l (f (IRel_curry l R₁)) (f (IRel_curry l R₂)) n).
iapply (Hcon (IRel_curry l R₁) (IRel_curry l R₂) n).
later_shift.
iapply (IRel_curry_equiv l R₁ R₂ n); assumption.
Qed.

Lemma contractive_x_curry {A : Type} (P : A → list Type) :
  ∀ (f : IRel_x P → IRel_x P), contractive_x P f →
  contractive_x (λ x, Prod (P x) :: nil)
    (λ R, IRel_x_uncurry _ (f (IRel_x_curry _ R))).
Proof.
  unfold contractive_x.
  intros f Hcon R₁ R₂ n.
  iintro HR.
  iapply (IRel_x_uncurry_equiv _ (f (IRel_x_curry _ R₁)) (f (IRel_x_curry _ R₂)) n). 
  iapply (Hcon (IRel_x_curry _ R₁) (IRel_x_curry _ R₂) n).
  later_shift.
  iapply (IRel_x_curry_equiv _ R₁ R₂ n); assumption.
Qed.

Lemma contractive_unary {A : Type} (f : IRel_1 A → IRel_1 A) :
  contractive (A :: nil) f → contractive_1 f.
Proof.
unfold contractive; unfold contractive_1.
intros Hcon n R₁ R₂ H x.
specialize (Hcon R₁ R₂ n); ispecialize Hcon.
+ later_shift.
  iintro x'. 
  apply I_iff_intro_M; intros; apply H.
  apply le_lt_n_Sm; assumption.
+ simpl in Hcon.
  apply I_iff_elim_M; iapply Hcon.
Qed.

Lemma contractive_binary {A : Type} {P : A → Type} (f : IRel_2 P → IRel_2 P) :
  contractive_x (λ x, P x :: nil) f → contractive_2 f.
Proof.
  unfold contractive_x; unfold contractive_2.
  intros Hcon n R₁ R₂ H x y.
  specialize (Hcon R₁ R₂ n); ispecialize Hcon.
  + later_shift.
    iintro x' ; iintro y'.
    apply I_iff_intro_M; intros; apply H.
    apply le_lt_n_Sm; assumption.
  + simpl in Hcon.
    apply I_iff_elim_M.
    iespecialize Hcon.
    apply Hcon.
Qed.

Lemma contractive_conv (l : list Type) (f : IRel l → IRel l) :
  contractive l f → contractive_1 (λ R, IRel_uncurry _ (f (IRel_curry _ R))).
Proof.
  intros; apply contractive_unary; apply contractive_curry; assumption.
Qed.

Lemma contractive_x_conv {A : Type} (P : A → list Type) (f : IRel_x P → IRel_x P) :
  contractive_x P f → contractive_2 (λ R, IRel_x_uncurry _ (f (IRel_x_curry _ R))).
Proof.
  intros; apply contractive_binary; apply contractive_x_curry; assumption.
Qed.

End Private.

Definition I_fix (l : list Type) (f : IRel l → IRel l) 
    (p : contractive l f) : IRel l :=
  IRel_curry l (I_fix_1 
    (λ R, IRel_uncurry l (f (IRel_curry l R)))
    (Private.contractive_conv l f p)
  ).

Program Definition I_fix_x {A : Type} (P : A → list Type) (f : IRel_x P → IRel_x P)
    (H : contractive_x P f) : IRel_x P :=
  IRel_x_curry _ (I_fix_2 
    (λ R, IRel_x_uncurry _ (f (IRel_x_curry _ R)))
    (Private.contractive_x_conv _ f H)
  ).

Lemma I_fix_unroll (l : list Type) 
    (f : IRel l → IRel l) (p : contractive l f) :
  I_fix l f p ≾ᵣ f (I_fix l f p).
Proof.
unfold I_fix; simpl.
apply IRel_uncurry_subrel; simpl; intros x n H.
apply (I_fix_1_unroll (λ R, IRel_uncurry l (f (IRel_curry l R)))).
apply IRel_uncurry_curry_id; assumption.
Qed.

Lemma I_fix_x_unroll {A : Type} (P : A → list Type)
    (f : IRel_x P → IRel_x P) (H : contractive_x _ f) :
  subrel_x _ (I_fix_x _ f H) (f (I_fix_x _ f H)).
Proof.
  unfold I_fix_x; simpl.
  apply IRel_x_uncurry_subrel; simpl ; intros x y n H'.
  apply (I_fix_2_unroll (λ R, IRel_x_uncurry _ (f (IRel_x_curry _ R)))).
  apply IRel_uncurry_curry_id; assumption.
Qed.

Lemma I_fix_roll (l : list Type)
    (f : IRel l → IRel l) (p : contractive l f) :
  f (I_fix l f p) ≾ᵣ I_fix l f p.
Proof.
unfold I_fix; simpl.
apply IRel_uncurry_subrel; simpl; intros x n H.
apply IRel_uncurry_curry_id.
apply (I_fix_1_roll (λ R, IRel_uncurry l (f (IRel_curry l R)))).
assumption.
Qed.

Lemma I_fix_x_roll {A : Type} (P : A → list Type)
    (f : IRel_x P → IRel_x P) (H : contractive_x _ f) :
  subrel_x _ (f (I_fix_x _ f H)) (I_fix_x _ f H).
Proof.
  unfold I_fix; simpl.
  apply IRel_x_uncurry_subrel; simpl; intros x y n H'.
  apply IRel_uncurry_curry_id.
  apply (I_fix_2_roll (λ R, IRel_x_uncurry _ (f (IRel_x_curry _ R)))).
  assumption.
Qed.