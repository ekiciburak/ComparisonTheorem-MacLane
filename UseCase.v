Require Export Comparison.

Definition FD  {C  : Category}
                (cT  : Functor C C)
                (cM : coMonad C cT)
                (cKC:= (coKleisli_Category C cT cM)): Functor cKC C.
Proof. destruct cM, eps.
        unshelve econstructor.
        - simpl. exact (fobj cT).
        - intros. destruct delta. simpl in *. unfold id in *.
          exact ((Functor.fmap cT f) o trans0 a).
        - repeat intro. subst. easy.
        - intros. destruct delta. unfold id in *. simpl in *.
          now rewrite ccomm_diagram2_b2.
        - intros. simpl. destruct delta. simpl in *. unfold id in *.
          destruct cT. simpl in *.
          rewrite preserve_comp.
          repeat rewrite assoc.
          rewrite preserve_comp.
          rewrite <- assoc.
          rewrite ccomm_diagram1.
          repeat rewrite assoc. apply rcancel.
          do 2 rewrite <- assoc.
          now rewrite comm_diag0.
Defined.
Check FD.

(** right adjoint functor that acts as G_D *)
Definition GD  {C  : Category}
                (cT  : Functor C C)
                (cM : coMonad C cT)
                (cKC:= (coKleisli_Category C cT cM)): Functor C cKC.
Proof. destruct cM, eps.
        unshelve econstructor.
        - exact id.
        - intros. unfold id. simpl. exact (f o trans a).
        - repeat intro. subst. easy.
        - intros. simpl in *. rewrite identity_f. easy.
        - intros. simpl in *. destruct delta. unfold id in *.
          simpl in *. destruct cT. simpl in *.
          rewrite preserve_comp.
          repeat rewrite <- assoc.
          rewrite ccomm_diagram2.
          repeat rewrite assoc, ccomm_diagram2_b1, f_identity.
          now rewrite <- comm_diag, assoc.
Defined.
Check GD.

Theorem comon_cokladj_alt: forall
                    {C  : Category}
                    (D  : Functor C C)
                    (cM : coMonad C D)
                    (FD := FD D cM)
                    (GD := GD D cM), Adjunction FD GD.
Proof. intros.
        unshelve econstructor.
        - unshelve econstructor.
          + intros. simpl. unfold id in *.
            destruct cM, eps, delta. simpl in *.
            apply identity.
          + intros. simpl.
            destruct cM, FD, GD. simpl in *. destruct eps, delta.
            simpl in *. unfold id in *.
            rewrite !identity_f, Functor.preserve_id, f_identity.
            now rewrite <- assoc, ccomm_diagram2_b1, f_identity.
        - unshelve econstructor.
          + intros. simpl. unfold id in *.
            destruct cM, eps, delta. simpl in *.  unfold id in *.
            apply trans.
          + intros. simpl in *.
            destruct cM, FD, GD. destruct eps, delta. simpl in *.
            unfold id in *.
            repeat rewrite assoc.
            rewrite Functor.preserve_comp.
            repeat rewrite assoc.
            repeat rewrite <- assoc.
            now rewrite ccomm_diagram2_b2, f_identity.
        - intros. simpl in *.
          destruct cM, FD, GD, eps, delta. simpl in *.
          unfold id in *.
          rewrite assoc.
          simpl in *.
          now rewrite Functor.preserve_id, f_identity, ccomm_diagram2_b1.
        - intros. simpl in *.
          destruct cM, FD, GD, eps, delta. simpl in *.
          unfold id in *.
          rewrite <- assoc.
          simpl in *.
          now rewrite Functor.preserve_id, identity_f, <- assoc,
          ccomm_diagram2_b1, f_identity.
Defined.
Check comon_cokladj_alt.

Lemma AnniliationOfDualAdjunctions: forall
                {C   : Category}
                (D   : Functor C C)
                (cM  : coMonad C D)
                (cKC := coKleisli_Category C D cM)
                (cKA := comon_cokladj_alt D cM)
                (M   := adj_mon (FD D cM) (GD D cM) cKA)
                (KC  := Kleisli_Category cKC (Compose_Functors (FD D cM) (GD D cM)) M)
                (KA  := mon_kladj (FD D cM) (GD D cM) M),
                exists !L: Functor KC C, 
                  Compose_Functors (FT (FD D cM) (GD D cM) (adj_mon (FD D cM) (GD D cM) cKA)) L = FD D cM /\
                  Compose_Functors L (GD D cM) = GT (FD D cM) (GD D cM) (adj_mon (FD D cM) (GD D cM) cKA) /\
                  Compose_Functors (Compose_Functors (GD D cM) (FT (FD D cM) (GD D cM) (adj_mon (FD D cM) (GD D cM) cKA))) L = D.
Proof. intros.
       exists (Adjunctions.L (FD D cM) (GD D cM) cKA).
       split. split. eapply commL.
       split. eapply commL.
       apply F_split2. cbn. easy.
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
       intros.
       apply uniqueL. split.
       destruct H as (Ha, (Hb, Hc)). apply Ha.
       destruct H as (Ha, (Hb, Hc)). apply Hb.
Qed.

