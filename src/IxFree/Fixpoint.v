Require Import Utf8.
Require Import List.
Require Import IxFree.Base IxFree.Connectives IxFree.Relations.
Require Import IxFree.UnaryFixpoint.
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

Lemma contractive_unary {A : Type} (f : IRel1 A → IRel1 A) :
  contractive (A :: nil) f → contractive1 f.
Proof.
unfold contractive; unfold contractive1.
intros Hcon n R₁ R₂ H x.
specialize (Hcon R₁ R₂ n); ispecialize Hcon.
+ simpl; later_down; iintro y.
  later_shift.
  apply I_iff_intro_M; intros; apply H.
  apply le_lt_n_Sm; assumption.
+ simpl in Hcon.
  apply I_iff_elim_M; iapply Hcon.
Qed.

Lemma contractive_conv (l : list Type) (f : IRel l → IRel l) :
  contractive l f → contractive1 (λ R, IRel_uncurry _ (f (IRel_curry _ R))).
Proof.
intros; apply contractive_unary; apply contractive_curry; assumption.
Qed.

End Private.

Definition I_fix (l : list Type) (f : IRel l → IRel l) 
    (p : contractive l f) : IRel l :=
  IRel_curry l (I_fix1 
    (λ R, IRel_uncurry l (f (IRel_curry l R)))
    (Private.contractive_conv l f p)
  ).

Lemma I_fix_unroll (l : list Type) 
    (f : IRel l → IRel l) (p : contractive l f) :
  I_fix l f p ≾ᵣ f (I_fix l f p).
Proof.
unfold I_fix; simpl.
apply IRel_uncurry_subrel; simpl; intros x n H.
apply (I_fix1_unroll (λ R, IRel_uncurry l (f (IRel_curry l R)))).
apply IRel_uncurry_curry_id; assumption.
Qed.

Lemma I_fix_roll (l : list Type)
    (f : IRel l → IRel l) (p : contractive l f) :
  f (I_fix l f p) ≾ᵣ I_fix l f p.
Proof.
unfold I_fix; simpl.
apply IRel_uncurry_subrel; simpl; intros x n H.
apply IRel_uncurry_curry_id.
apply (I_fix1_roll (λ R, IRel_uncurry l (f (IRel_curry l R)))).
assumption.
Qed.