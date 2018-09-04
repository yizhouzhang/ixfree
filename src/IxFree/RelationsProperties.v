Require Import Utf8.
Require Import List.
Require Import IxFree.Base IxFree.Connectives IxFree.Relations.

Definition I_rel_relation (A : Type) := A → A → IProp.

Section Defs.

Context {A : Type}.

Class Reflexive (r : I_rel_relation A) :=
  reflexivity : ∀ R, ⊨ r R R.

Class Symmetric (r : I_rel_relation A) :=
  symmetric : ∀ R₁ R₂, ⊨ r R₁ R₂ ⇒ r R₂ R₁.

End Defs.


Section I_rel.
Context (l : list Type).

Instance I_rel_equiv_reflexive : Reflexive (I_rel_equiv l) := {}.
Proof.
  intro ; intro n.
  induction l as [ | ? ? IH] ; simpl.
  + unfold I_iff ; isplit ; iintro ; assumption.
  + iintro.
    apply (IH (R x)).
Qed.

Instance I_rel_equiv_symmetric : Symmetric (I_rel_equiv l) := {}.
Proof.
  intros ; intro n.
  iintro H.
  induction l as [ | ? ? IH ] ; simpl in *.
  + idestruct H as H1 H2 ; isplit ; trivial.
  + iintro ; apply IH.
    iespecialize H ; exact H.
Qed.

End I_rel.


Section I_rel_x.
Context {A : Type} (P : A → list Type).

Instance I_rel_x_equiv_reflexive : Reflexive (I_rel_x_equiv P) := {}.
Proof.
  intro ; intro n ; iintro.
  apply I_rel_equiv_reflexive.
Qed.

Instance I_rel_x_equiv_symmetric : Symmetric (I_rel_x_equiv P) := {}.
Proof.
  intros ; intro n ; iintro ; iintro x.
  iapply (I_rel_equiv_symmetric _ (R₁ x) (R₂ x) n).
  iespecialize H ; apply H.
Qed.

End I_rel_x.


Section I_rel_xx.
Context {A B : Type} (P : A → B → list Type).

Instance I_rel_xx_equiv_reflexive : Reflexive (I_rel_xx_equiv P) := {}.
Proof.
  intro ; intro n.
  iintro.
  apply I_rel_x_equiv_reflexive.
Qed.

Instance I_rel_xx_equiv_symmetric : Symmetric (I_rel_xx_equiv P) := {}.
Proof.
  intros ; intro n ; iintro ; iintro x.
  iapply (I_rel_x_equiv_symmetric _ (R₁ x) (R₂ x) n).
  iintro y.
  iespecialize H ; apply H.
Qed.

End I_rel_xx.