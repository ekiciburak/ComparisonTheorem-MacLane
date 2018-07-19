Require Export Adjunctions.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.


Theorem L_functor: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (@adj_mon   C D F G A1) in
               let CT := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (LA F G M) in
               let GT := (RA F G M) in
               let A2 := (mon_kladj F G M) in
                 (Compose_Functors FT (L F G A1)) = F /\ (Compose_Functors (L F G A1) G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
       split.  cbn in *.

       unfold M, CT, GT. cbn in *.
       assert (fobj (Compose_Functors FT (L F G A1)) = fobj F).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split C D
         (Compose_Functors FT (L F G A1)) F); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, L.
       simpl in *.
       assert (H = eq_refl).
       {
          specialize (UIP_refl _   (fun a : @obj C => fobj a)); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b. extensionality f.
       rewrite preserve_comp.
       rewrite assoc.
       now rewrite ob1, identity_f.

       simpl in *.
       assert (fobj (Compose_Functors (L F G A1) G) = fobj GT).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split (Kleisli_Category C 
         (Compose_Functors F G) M) C 
         (Compose_Functors (L F G A1) G) GT); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl in *.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, L.
       simpl in *.
       assert (H = eq_refl).
       { 
          specialize (UIP_refl _  
           (fun a : @obj C => fobj0 (fobj a))); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b.
       extensionality f. now rewrite preserve_comp0.
Qed.
Check L_functor.

Arguments fmap {_} {_} _ _ _ _.

(** Equivalence of Functors, inspired by Amin Timany *)
Lemma F_split2: forall
               (C D  : Category)
               (F G  : Functor C D)
               (ObjEq: (fobj F) = (fobj G)),
               JMeq (fmap F) (fmap G) -> F = G.
Proof.

    destruct F; destruct G; simpl; intros; subst; f_equal.
    apply JMeq_eq in H. subst. f_equal.
    now destruct (proof_irrelevance _ fmapP fmapP0).
    now destruct (proof_irrelevance _ preserve_id preserve_id0).
    now destruct (proof_irrelevance _ preserve_comp preserve_comp0).
Defined.

Arguments fmap {_} {_} _ {_} {_} _.

Lemma uniqueL: forall
                   {C D: Category}
                   (F: Functor C D)
                   (G: Functor D C)
                   (A1: Adjunction F G),
                   let  M := (adj_mon   F G A1) in
                   let CT := (Kleisli_Category C (Compose_Functors F G) M) in
                   let FT := (LA F G M) in
                   let GT := (RA F G M) in
                   let A2 := (mon_kladj F G M) in
                   unique
                      (fun L0 : CT → D =>
                       Compose_Functors FT L0 = F /\ Compose_Functors L0 G = GT)
                      (L F G A1).
Proof. intros.
       unfold unique. split.
       specialize (L_functor F G A1); intros. apply H.

       assert (H1: Compose_Functors FT (L F G A1) = F /\ Compose_Functors (L F G A1) G = GT).
       specialize (L_functor F G A1); intros. apply H.
       intros R H. destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       pose proof Ha as Haa.
       pose proof Hb as Hbb.

       rewrite <- H1a in Ha.
       assert (fobj (Compose_Functors FT R) = fobj (Compose_Functors FT (L F G A1))).
       rewrite Ha. easy.
       assert (fobj (Compose_Functors FT R) = fobj R).
       cbn. easy.
       assert (fobj (Compose_Functors FT R) = fobj (L F G A1)).
       cbn in *. easy.
       rewrite H0 in H1.
       symmetry in H1. remember F_split. cbn in  *.
       unfold id in *.

       specialize (@F_split2 _ _ (L F G A1) R H1).

       intros. apply H2.
       cbn in *.
       apply eq_dep_id_JMeq. cbn in *.
       apply EqdepFacts.eq_sigT_iff_eq_dep. cbn in *.
       apply eq_existT_uncurried.
       assert ((forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj F b) (fobj F a)) =
               (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj R b) (fobj R a))).
       { rewrite H1. easy. }
       exists H3.
       unfold eq_rect.
       destruct R. cbn in *. subst.
       assert (H3 = eq_refl).
       {  specialize (UIP_refl _  
          (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj F b) (fobj F a)) ); intros.
          now specialize (H1 H3).
       }
       rewrite H1.
       extensionality a. extensionality b. extensionality f.
       specialize (adjEq10_1 _ _ _ _ A1); intros Hueq1.
       specialize (adjEq10_1 _ _ _ _ A2); intros Hueq2.

       destruct A1, A2. cbn in *. unfold id in *.

       cbn in *. unfold id in *.
       unfold L in *. cbn in *.
       eapply Hueq1 with (f := f).
       rewrite !Functor.preserve_comp, <- !assoc.
       unfold M in *.
       destruct M, unit, unit0, counit0. cbn in *. unfold id in *.
       clear H2 Ha H1b H1a.
       rewrite <- trans_sym.
       rewrite !assoc.
       now rewrite ob2, identity_f.
       unfold M in *.
       destruct M, unit, counit0, unit0. cbn in *. unfold id in *.
       assert (Functor.fmap G (fmap a b f) = Functor.fmap GT f).
       { unfold Compose_Functors, GT, RA, adj_mon in Hb. cbn in Hb. 
         inversion Hb. cbn.
         apply inj_pair2 in H5.
         pose proof (fun x y z => eq_ind_r (fun f => f x y z = _ x y z) eq_refl H5) as H5';
         cbv beta in H5'.
         now specialize (H5' _ _ f).
       }
       rewrite H4.
       cbn.
       rewrite <- assoc, <- trans_sym.
       now rewrite assoc, ob2, identity_f.
Qed.


(** Mac Lane's comparison theorem of 
                               an arbitrary adjunction
                               and the Kleisli adjunction it determines *)
Theorem ComparisonMacLane: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (@adj_mon   C D F G A1) in
               let CT := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (LA F G M) in
               let GT := (RA F G M) in
               let A2 := (mon_kladj F G M) in
               exists !L, (Compose_Functors FT L) = F /\ (Compose_Functors L G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
       exists (L F G A1). apply uniqueL.
Qed.


(** Mac Lane's comparison theorem of 
                               an arbitrary adjunction
                               and the coKleisli adjunction it determines *)
Theorem coComparisonMacLane: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (@adj_comon D C F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                 exists L: Functor CD D,
                   (Compose_Functors GD L) = G /\ (Compose_Functors L F) = FD.
Proof. intros C D F G A1 cM CD FD GD A2.
      (*
       pose proof A2 as A22.
       pose proof A1 as A11.
       apply adjEq10 in A11.
       apply adjEq12 in A22.
      *)
       exists (duL F G A1).
       split. cbn in *.

       unfold cM, CD, FD. cbn in *.
       assert (fobj (Compose_Functors GD (duL F G A1)) = fobj G).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split C D
         (Compose_Functors GD (duL F G A1)) G); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, duL.
       simpl in *.
       assert (H = eq_refl).
       {
          specialize (UIP_refl _   (fun a : @obj C => fobj0 a)); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b. extensionality f.
       rewrite preserve_comp0.
       rewrite <- assoc.
       now rewrite ob2, f_identity.

       simpl in *.
       assert (fobj (Compose_Functors (duL F G A1) F) = fobj FD).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split (coKleisli_Category C 
         (Compose_Functors G F) cM) C 
         (Compose_Functors (duL F G A1) F) FD); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl in *.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, duL.
       simpl in *.
       assert (H = eq_refl).
       { 
          specialize (UIP_refl _  
           (fun a : @obj C => fobj (fobj0 a))); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b.
       extensionality f.
       now rewrite preserve_comp.
Qed.
Check coComparisonMacLane.
