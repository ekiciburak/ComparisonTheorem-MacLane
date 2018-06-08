Require Export Categories.

Class Isomorphism {C: Category} (x y : @obj C) : Type := {
  to   : arrow y x;
  from : arrow x y;

  iso_to_from : to o from = @identity C y;
  iso_from_to : from o to = @identity C x
}.

Arguments to {_ _ _} _. 
Arguments from {_ _ _} _.

Lemma iso_split: forall C x y (I1 I2: Isomorphism x y), 
        to I1 = to I2 /\ from I1 = @from C x y I2 -> I1 = I2.
Proof. intros.
       destruct H as (H1, H2).
       destruct I1, I2. simpl in *. subst.
       specialize (proof_irrelevance (to1 o from1 = identity y) iso_to_from0 iso_to_from1); intros.
       specialize (proof_irrelevance (from1 o to1 = identity x) iso_from_to0 iso_from_to1); intros.
       now subst.
Qed.

(** Groupoid is a category with all maps isomorphisms => category of isomorphisms *)
Definition Groupoid (C: Category): Category.
Proof. unshelve econstructor.
       - exact (@obj C).
       - exact Isomorphism.
       - intros. unshelve econstructor.
         + exact (identity a).
         + exact (identity a).
         + now rewrite f_identity.
         + now rewrite f_identity.
      - intros a b c I1 I2.
        unshelve econstructor.
        + destruct I1, I2. exact (to1 o to0).
        + destruct I1, I2. exact (from0 o from1).
        + simpl. destruct I1, I2. rewrite <- iso_to_from1.
          rewrite assoc. repeat apply compose_respects. rewrite <- assoc.
          now rewrite iso_to_from0, f_identity. easy.
        + simpl. destruct I1, I2. rewrite <- iso_from_to0.
          rewrite assoc. repeat apply compose_respects. rewrite <- assoc.
          now rewrite iso_from_to1, f_identity. easy.
      - repeat intro. simpl in *. subst. easy.
      - repeat intro. simpl. destruct f, g,  h. simpl in *.
        apply iso_split. simpl. split; now rewrite assoc.
      - intros. simpl. destruct f. simpl.
        apply iso_split. simpl. split. now rewrite f_identity.
        now rewrite identity_f.
      - intros. destruct f. apply iso_split. simpl.
        split. now rewrite identity_f.
        now rewrite f_identity.
Defined.
Check Groupoid.

Infix "≅" := Isomorphism (at level 40, left associativity).
