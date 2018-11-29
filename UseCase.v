Require Import ECat.Imports.
Require Import ECat.Category.
Require Import ECat.Functor.
Require Import ECat.NaturalTransformation.
Require Import ECat.Monad.
Require Import ECat.Adjunction.
Require Import ECat.Comparison.

Arguments fmap {_} {_} _ _ _ _.
Arguments fobj {_} {_} _ _.

Class Faithful (C D: Category) (F : Functor C D) := {
  fmap_inj {x y} (f g: arrow y x): fmap F _ _ f = fmap F _ _ g -> f = g
}.

Lemma AnniliationOfDualAdjunctions: forall
                {C   : Category}
                (D   : Functor C C)
                (cM  : coMonad C D)
                (cKC := coKleisli_Category C D cM)
                (cKA := comon_cokladj D cM)
                (M   := adj_mon (FD D cM) (GD D cM) cKA)
                (KC  := Kleisli_Category cKC (Compose_Functors (FD D cM) (GD D cM)) M)
                (KA  := mon_kladj (FD D cM) (GD D cM) M),
                exists !L: Functor KC C, 
                  Compose_Functors (FT (Compose_Functors (FD D cM) (GD D cM)) (adj_mon (FD D cM) (GD D cM) cKA)) L = FD D cM /\
                  Compose_Functors L (GD D cM) = GT (Compose_Functors (FD D cM) (GD D cM)) (adj_mon (FD D cM) (GD D cM) cKA) /\
                  Compose_Functors (Compose_Functors (GD D cM) (FT (Compose_Functors (FD D cM) (GD D cM)) (adj_mon (FD D cM) (GD D cM) cKA))) L = D  /\
                  Faithful _ _ L.
Proof. intros.
       exists (Comparison.L (FD D cM) (GD D cM) cKA).
       split. split. eapply commL.
       split. eapply commL.
       split. apply F_split. cbn. easy.
       cbn.
       apply eq_dep_id_JMeq.
       apply EqdepFacts.eq_sigT_iff_eq_dep.
       apply eq_existT_uncurried.
       unfold id in *.
       exists (@eq_refl _ (forall a b : obj, arrow b a -> arrow (fobj D b) (fobj D a))).
       unfold eq_rect.
       extensionality a.
       extensionality b.
       extensionality f.
       rewrite !preserve_comp, preserve_id, identity_f.
       destruct cM as (eps, delta, cc1, cc2, cc3, cc4). cbn in *.
       unfold id in *.
       clear cKC cKA M KC KA.
       repeat rewrite assoc.
       setoid_rewrite <- assoc at 2.
       rewrite <- preserve_comp, cc4, preserve_id, f_identity.
       destruct eps   as (teps,   cc5). cbn in *.
       destruct delta as (tdelta, cc6). cbn in *.
       rewrite <- assoc, cc6.
       now rewrite assoc, cc3, identity_f.
       (** Faithfulness of the functor L *)
       intros.
       unshelve econstructor.
       intros. cbn in H.
       destruct cM as (eps, delta, cc1, cc2, cc3, cc4). cbn in *.
       unfold id in *.
       clear cKC cKA M KC KA.
       destruct eps, delta. cbn in *.
       do 2 rewrite assoc in H.
       rewrite <- !comm_diag, <- !assoc in H.
       now rewrite !cc3, !f_identity in H.
       (**unicity of L *)
       intros.
       apply uniqueL. split.
       destruct H as (Ha, (Hb, Hc)). apply Ha.
       destruct H as (Ha, (Hb, Hc)). apply Hb.
Qed.






