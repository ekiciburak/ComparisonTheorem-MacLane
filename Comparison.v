Require Export Adjunctions.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.


Lemma Khelper: forall
               {C D    : Category}
               (F      : Functor C D)
               (G      : Functor D C) 
               (A1     : Adjunction F G),
               let M   := (adj_mon F G A1) in
               let FTL := (LAEM F G M) in
               (forall a b : obj,arrow b a -> arrow (fobj (Compose_Functors F (K F G A1)) b) (fobj (Compose_Functors F (K F G A1)) a)) =
               (forall a b : obj, arrow b a -> arrow (fobj FTL b) (fobj FTL a)).
Proof. intros.
       assert (fobj (Compose_Functors F (K F G A1)) = fobj FTL).
       {   extensionality a.
           apply eqTA2; easy.
       }
       now rewrite H.
Defined.

Lemma K_functor: forall
               {C D    : Category}
               (F      : Functor C D)
               (G      : Functor D C) 
               (A1     : Adjunction F G),
               let M   := (adj_mon F G A1) in
               let EMC := (EilenbergMooreCategory C (Compose_Functors F G) M) in
               let FTL := (LAEM F G M) in
               let GTL := (RAEM F G M) in
               let A2  := (mon_emadj F G M) in 
                 (Compose_Functors (K F G A1) GTL) = G /\ (Compose_Functors F (K F G A1)) = FTL.
Proof. intros C D F G A1 M EMC FTL GTL A2.
       split.  cbn in *.
       apply F_split2. easy.

       apply eq_dep_id_JMeq. cbn in *.
       apply EqdepFacts.eq_sigT_iff_eq_dep. cbn in *.
       apply eq_existT_uncurried.
       assert ((forall a b : obj, arrow b a -> arrow (fobj G b) (fobj G a)) =
               (forall a b : obj, arrow b a -> arrow (fobj G b) (fobj G a))).
       { easy. }
       exists H.
       unfold eq_rect.
       assert (H = eq_refl).
       { 
          specialize (UIP_refl _  
           ((forall a b : obj, arrow b a -> arrow (fobj G b) (fobj G a)))); intros.
          now specialize (H0 H).
       }
       rewrite H0. easy.

       apply F_split2.
           extensionality a.
           apply eqTA2; easy.
       assert (H: fobj (Compose_Functors F (K F G A1)) = fobj FTL).
           extensionality a.
           apply eqTA2; easy.

       assert ((forall a b : obj,
       Categories.arrow b a -> Categories.arrow (fobj (Compose_Functors F (K F G A1)) b) (fobj (Compose_Functors F (K F G A1)) a)) =
       (forall a b : obj, Categories.arrow b a -> Categories.arrow (fobj FTL b) (fobj FTL a)) ).
       { now rewrite H. }
 
       apply eq_dep_id_JMeq.
       apply EqdepFacts.eq_sigT_iff_eq_dep. 
       apply eq_existT_uncurried.
Admitted.

Lemma commL: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A    : Adjunction F G),
               let M  := (@adj_mon   C D F G A) in
               let CK := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FT F G M) in
               let GT := (GT F G M) in
                 (Compose_Functors FT (L F G A)) = F /\ (Compose_Functors (L F G A) G) = GT.
Proof. intros C D F G A1 M CK FT GT; split.
       - apply F_split2. 
         + easy.
         + apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, eq_existT_uncurried. 
           cbn in *. unfold id in *.
           unfold eq_rect.
           exists (@eq_refl _ (forall a b : obj, arrow b a -> 
                               arrow (fobj F b) (fobj F a))).
           extensionality a.
           extensionality b.
           extensionality f.
           rewrite preserve_comp.
           destruct A1. cbn in *.
           assert ( fmap F f = identity (fobj F b)  o  fmap F f).
           { now rewrite identity_f. }
           rewrite H at 2. rewrite assoc. 
           apply rcancel.
           apply ob1.
       - apply F_split2.
         + easy.
         + apply eq_dep_id_JMeq. 
           apply EqdepFacts.eq_sigT_iff_eq_dep.
           apply eq_existT_uncurried. 
           cbn in *. unfold id in *.
           exists (@eq_refl _ (forall a b : obj, arrow (fobj G (fobj F b)) a -> 
                               arrow (fobj G (fobj F b)) (fobj G (fobj F a)))).
           unfold eq_rect.
           extensionality a.
           extensionality b.
           extensionality f.
           now rewrite preserve_comp.
Qed.
Check commL.

Lemma uniqueL: forall
                   {C D: Category}
                   (F: Functor C D)
                   (G: Functor D C)
                   (A1: Adjunction F G),
                   let  M := (adj_mon   F G A1) in
                   let CK := (Kleisli_Category C (Compose_Functors F G) M) in
                   let FT := (FT F G M) in
                   let GT := (GT F G M) in
                   let A2 := (mon_kladj F G M) in
                     forall R : CK → D, Compose_Functors FT R = F /\ Compose_Functors R G = GT -> (L F G A1) = R.
Proof. intros C D F G A1 M CK FT GT A2 R H.
       assert (H1: Compose_Functors FT (L F G A1) = F /\ Compose_Functors (L F G A1) G = GT).
       specialize (commL F G A1); intros. apply H0.
       destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       apply F_split2.
       - rewrite <- H1a in Ha.
         assert (fobj (Compose_Functors FT R) = fobj (Compose_Functors FT (L F G A1))).
         rewrite Ha. easy.
         easy.
       - cbn in *.
         rewrite <- H1a in Ha.
         assert (fobj (Compose_Functors FT R) = fobj (Compose_Functors FT (L F G A1))).
         rewrite Ha. easy.
         assert (fobj (Compose_Functors FT R) = fobj R).
         cbn. easy.
         assert (fobj (Compose_Functors FT R) = fobj (L F G A1)).
         cbn in *. easy.
         rewrite H0 in H1.
         apply eq_dep_id_JMeq. cbn in *.
         apply EqdepFacts.eq_sigT_iff_eq_dep. cbn in *.
         apply eq_existT_uncurried.
         assert (p: (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj F b) (fobj F a)) =
                    (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj R b) (fobj R a))).
         { rewrite H1. easy. }
         exists p.
         unfold eq_rect.
         destruct R. cbn in *. subst.
         assert (p = eq_refl).
         {  specialize (UIP_refl _  
            (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj F b) (fobj F a)) ); intros.
            now specialize (H1 p).
         }
         rewrite H1.
         extensionality a. extensionality b. extensionality f.
         apply (adjEq10_1 _ _ _ _ A1) with (f := f). 

         rewrite !Functor.preserve_comp, <- !assoc.
         destruct A1, unit. cbn in *. unfold id in *.
         rewrite comm_diag.
         rewrite !assoc.
         now rewrite ob2, identity_f.
         assert (Functor.fmap G (fmap a b f) = Functor.fmap GT f).
         { unfold Compose_Functors, GT, adj_mon in Hb. cbn in Hb. 
           inversion Hb.
           apply inj_pair2 in H3.
           pose proof (fun x y z => eq_ind_r (fun f => f x y z = _ x y z) eq_refl H3) as H3';
           cbv beta in H3'.
           now specialize (H3' _ _ f).
         }
         rewrite H2.
         destruct A1, unit. cbn in *. unfold id in *.
         rewrite <- assoc, comm_diag.
         now rewrite assoc, ob2, identity_f.
Qed.


(** Mac Lane's comparison theorem for the Kleisli Construction *)
Theorem ComparisonMacLane: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (@adj_mon   C D F G A1) in
               let CT := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FT F G M) in
               let GT := (GT F G M) in
               let A2 := (mon_kladj F G M) in
               exists !L, (Compose_Functors FT L) = F /\ (Compose_Functors L G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
       exists (L F G A1). split.
       - apply commL.
       - apply uniqueL.
Qed.
Check ComparisonMacLane.


(** dualizing the theorem *)
Lemma duL_functor: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (@adj_comon D C F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                   (Compose_Functors GD (duL F G A1)) = G /\ (Compose_Functors (duL F G A1) F) = FD.
Proof. intros C D F G A1 cM CD FD GD A2.
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
Check duL_functor.

Lemma uniqueduL: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                 unique
                    (fun L0 : CD → D =>
                     Compose_Functors GD L0 = G /\ Compose_Functors L0 F = FD) 
                    (duL F G A1).
Proof. intros.
       unfold unique. split.
       specialize (duL_functor F G A1); intros. apply H.

       assert (H1: (Compose_Functors GD (duL F G A1) = G /\ Compose_Functors (duL F G A1) F = FD)).
       specialize (duL_functor F G A1); intros. apply H.
       intros R H. destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       pose proof Ha as Haa.
       pose proof Hb as Hbb.

       rewrite <- H1a in Ha.
       assert (fobj (Compose_Functors GD R) = fobj (Compose_Functors GD (duL F G A1))).
       rewrite Ha. easy.
       assert (fobj (Compose_Functors GD R) = fobj R).
       cbn. easy.
       assert (fobj (Compose_Functors GD R) = fobj (duL F G A1)).
       cbn in *. easy.
       rewrite H0 in H1.
       symmetry in H1. remember F_split. cbn in  *.
       unfold id in *.

       specialize (@F_split2 _ _ (duL F G A1) R H1).

       intros. apply H2.
       cbn in *.
       apply eq_dep_id_JMeq. cbn in *.
       apply EqdepFacts.eq_sigT_iff_eq_dep. cbn in *.
       apply eq_existT_uncurried. unfold id in *.
       assert ((forall a b : obj, arrow b (fobj F (fobj G a)) -> arrow (fobj G b) (fobj G a)) =
               (forall a b : obj, arrow b (fobj F (fobj G a)) -> arrow (fobj R b) (fobj R a))).
       { rewrite H1. easy. }
       exists H3.
       unfold eq_rect.
       destruct R. cbn in *. subst.
       assert (H3 = eq_refl).
       {  specialize (UIP_refl _  
          (forall a b : obj, arrow b (fobj F (fobj G a)) -> arrow (fobj G b) (fobj G a)) ); intros.
          now specialize (H1 H3).
       }
       rewrite H1.
       extensionality a. extensionality b. extensionality f.
       specialize (adjEq10_2 _ _ _ _ A1); intros Hueq1.
       specialize (adjEq10_2 _ _ _ _ A2); intros Hueq2.

       destruct A1, A2. cbn in *. unfold id in *.

       cbn in *. unfold id in *.
       unfold duL in *. cbn in *.
       eapply Hueq1 with (f := f).
       rewrite !Functor.preserve_comp, !assoc.
       unfold cM in *.
       destruct cM, unit, unit0, counit. cbn in *. unfold id in *.
       clear H2 Ha H1b H1a.
       rewrite <- comm_diag1.
       rewrite <- !assoc.
       now rewrite ob1, f_identity.
       unfold cM in *.
       destruct cM, unit, counit, unit0. cbn in *. unfold id in *.
       assert (Functor.fmap F (fmap a b f) = Functor.fmap FD f).
       { unfold Compose_Functors, GD, adj_mon in Hb. cbn in Hb. 
         inversion Hb. cbn.
         apply inj_pair2 in H5. unfold id in *.
         pose proof (fun x y z => eq_ind_r (fun f => f x y z = _ x y z) eq_refl H5) as H5';
         cbv beta in H5'. unfold id in *.
         now specialize (H5' _ _ f).
       }
       rewrite H4.
       cbn.
       rewrite assoc, <- comm_diag0.
       now rewrite <- assoc, ob1, f_identity.
Qed.
Check uniqueduL.

(** Mac Lane's comparison theorem for the coKleisli Construction *)
Theorem duaLComparisonMacLane: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                   exists !L, Compose_Functors GD L = G /\ Compose_Functors L F = FD.
Proof. intros C D F G A1 M CT FT GT A2.
       exists (duL F G A1). apply uniqueduL.
Qed.
Check duaLComparisonMacLane.

(*
Lemma K_functor: forall
               {C D    : Category}
               (F      : Functor C D)
               (G      : Functor D C) 
               (A1     : Adjunction F G),
               let M   := (@adj_mon   C D F G A1) in
               let EMC := (EilenbergMooreCategory C (Compose_Functors F G) M) in
               let FT  := (LAEM F G M) in
               let GT  := (RAEM F G M) in
               let A2  := (mon_emadj F G M) in
                 (Compose_Functors FT (K F G A1)) = F /\ (Compose_Functors (K F G A1) G) = GT.
*)
