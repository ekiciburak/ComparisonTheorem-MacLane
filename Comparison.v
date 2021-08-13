Require Import ECat.Imports.
Require Import ECat.Category.
Require Import ECat.Functor.
Require Import ECat.NaturalTransformation.
Require Import ECat.Monad.
Require Import ECat.Adjunction.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.

(** the comparison functor L *)
Definition L: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A     : Adjunction F G),
               let M  := (adj_mon F G A) in
               let CM := (adj_comon F G A) in
               let CK := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FT (Compose_Functors F G) M) in
               let GT := (GT (Compose_Functors F G) M) in Functor CK D.
Proof. intros C D F G A M CM CK FT GT. 
       unshelve econstructor.
       - exact (fobj F).
       - intros a b f.
         destruct CM as (eps, delta, cc1, cc2, cc3, cc4).
         exact (trans eps (fobj F b) o fmap F f).
       - repeat intro. now subst.
       - intros. destruct A, unit, counit.
         cbn in *. now rewrite <- ob1.
       - intros. cbn in *.
         rewrite preserve_comp.
         destruct A, unit, counit. cbn in *.
         do 2 rewrite assoc.
         apply rcancel.
         rewrite <- preserve_comp.
         now rewrite <- comm_diag0.
Defined.

(** the functor L makes the diagram in the theorem statement 
commutative at both directions *)
Lemma commL: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A    : Adjunction F G),
               let M  := (@adj_mon   C D F G A) in
               let CK := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FT (Compose_Functors F G) M) in
               let GT := (GT (Compose_Functors F G) M) in
                 (Compose_Functors FT (L F G A)) = F /\ (Compose_Functors (L F G A) G) = GT.
Proof. intros C D F G A1 M CK FT GT; split.
       - apply F_split. 
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
       - apply F_split.
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

(** uniqueness of the comparison functor L *)
Lemma uniqueL: forall
                   {C D: Category}
                   (F: Functor C D)
                   (G: Functor D C)
                   (A1: Adjunction F G),
                   let  M := (adj_mon   F G A1) in
                   let CK := (Kleisli_Category C (Compose_Functors F G) M) in
                   let FT := (FT (Compose_Functors F G) M) in
                   let GT := (GT (Compose_Functors F G) M) in
                   let A2 := (mon_kladj F G M) in
                     forall R : CK → D, Compose_Functors FT R = F /\ Compose_Functors R G = GT -> (L F G A1) = R.
Proof. intros C D F G A1 M CK FT GT A2 R H.
       assert (H1: Compose_Functors FT (L F G A1) = F /\ Compose_Functors (L F G A1) G = GT).
       specialize (commL F G A1); intros. apply H0.
       destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       apply F_split.
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
         apply (adj_unique_map _ _ _ _ A1) with (f := f).

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
               let FT := (FT (Compose_Functors F G) M) in
               let GT := (GT (Compose_Functors F G) M) in
               let A2 := (mon_kladj F G M) in
               exists !L, (Compose_Functors FT L) = F /\ (Compose_Functors L G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
       exists (L F G A1). split.
       - apply commL.
       - apply uniqueL.
Qed.
Check ComparisonMacLane.

(** dualizing the theorem:
Mac Lane's comparison theorem for the coKleisli Construction *)


(** dualizing the comparison functor L *)
Definition duL: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let  M := (adj_mon   F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (FD (Compose_Functors G F) cM) in
                 let GD := (GD (Compose_Functors G F) cM) in
                 let A2 := (comon_cokladj (Compose_Functors G F) cM) in Functor CD D.
Proof. intros C D F G A1 cM M CD FD GD A2. simpl in *.
       unshelve econstructor.
       - exact (fobj G).
       - intros.
         destruct M, eta.
         exact ((fmap G f) o (trans (fobj G a))).
       - repeat intro. subst. easy.
       - intros. simpl in *. destruct A1. now rewrite ob2.
       - intros. simpl in *. rewrite preserve_comp.
         rewrite <- assoc.
         destruct A1, unit. cbn in *.
         rewrite comm_diag.
         rewrite preserve_comp.
         do 2 rewrite assoc.
         apply rcancel.
         do 2 rewrite <- assoc.
         apply lcancel.
         unfold id in *.
         now rewrite comm_diag.
Defined.

(** the functor duL makes the diagram in the dual theorem statement 
commutative at both directions *)
Lemma commduL: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (@adj_comon D C F G A1) in
                 let cKC:= (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (FD (Compose_Functors G F) cM) in
                 let GD := (GD (Compose_Functors G F) cM) in
                 let A2 := (comon_cokladj (Compose_Functors G F) cM) in
                   (Compose_Functors GD (duL F G A1)) = G /\ (Compose_Functors (duL F G A1) F) = FD.
Proof. intros C D F G A1 cM cKC FD GD A2; split.
       - apply F_split. 
         + easy.
         + apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, eq_existT_uncurried. 
           cbn in *. unfold id in *.
           unfold eq_rect.
           exists (@eq_refl _ (forall a b : obj, arrow b a -> 
                               arrow (fobj G b) (fobj G a))).
           extensionality a.
           extensionality b.
           extensionality f.
           rewrite preserve_comp.
           destruct A1. cbn in *.
           assert ( fmap G f =  fmap G f o identity (fobj G a)).
           { now rewrite f_identity. }
           rewrite H at 2. rewrite <- assoc. 
           apply lcancel.
           apply ob2.
       - apply F_split.
         + easy.
         + apply eq_dep_id_JMeq. 
           apply EqdepFacts.eq_sigT_iff_eq_dep.
           apply eq_existT_uncurried. 
           cbn in *. unfold id in *.
           exists (@eq_refl _  (forall a b : obj, arrow b (fobj F (fobj G a)) -> 
                                arrow (fobj F (fobj G b)) (fobj F (fobj G a)))).
           unfold eq_rect.
           extensionality a.
           extensionality b.
           extensionality f.
           now rewrite preserve_comp.
Qed.

(** uniqueness of the dual comparison functor duL *)
Lemma uniqueduL: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let cKC:= (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (FD (Compose_Functors G F) cM) in
                 let GD := (GD (Compose_Functors G F) cM) in
                 let A2 := (comon_cokladj (Compose_Functors G F) cM) in
                     forall R: cKC → D, Compose_Functors GD R = G /\ Compose_Functors R F = FD -> (duL F G A1) = R.
Proof. intros C D F G A1 cM cKC FD GD A2 R H.
       assert (H1: Compose_Functors GD (duL F G A1) = G /\ Compose_Functors (duL F G A1) F = FD).
       specialize (commduL F G A1); intros. apply H0.
       destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       apply F_split.
       - rewrite <- H1a in Ha.
         assert (fobj (Compose_Functors GD R) = fobj (Compose_Functors GD (duL F G A1))).
         rewrite Ha. easy.
         easy.
       - cbn in *.
         rewrite <- H1a in Ha.
         assert (fobj (Compose_Functors GD R) = fobj (Compose_Functors GD (duL F G A1))).
         rewrite Ha. easy.
         assert (fobj (Compose_Functors GD R) = fobj R).
         cbn. easy.
         assert (fobj (Compose_Functors GD R) = fobj (duL F G A1)).
         cbn in *. easy.
         rewrite H0 in H1.
         apply eq_dep_id_JMeq. cbn in *.
         apply EqdepFacts.eq_sigT_iff_eq_dep. cbn in *.
         apply eq_existT_uncurried. unfold id in *.
         assert (p: (forall a b : obj, arrow b (fobj F (fobj G a)) -> arrow (fobj G b) (fobj G a)) =
                    (forall a b : obj, arrow b (fobj F (fobj G a)) -> arrow (fobj R b) (fobj R a))).
         { rewrite H1. easy. }
         exists p.
         unfold eq_rect.
         destruct R. cbn in *. subst.
         assert (p = eq_refl).
         {  specialize (UIP_refl _  
            (forall a b : obj, arrow b (fobj F (fobj G a)) -> arrow (fobj G b) (fobj G a))); intros.
            now specialize (H1 p).
         }
         rewrite H1.
         extensionality a. extensionality b. extensionality f.
         apply (adj_unique_map_dual _ _ _ _ A1) with (f := f). 

         rewrite !Functor.preserve_comp, !assoc.
         destruct A1, counit. cbn in *. unfold id in *.
         clear Hb Ha H1b H1a.
         rewrite <- comm_diag.
         rewrite <- !assoc.
         now rewrite ob1, f_identity.
         assert (Functor.fmap F (fmap a b f) = Functor.fmap FD f).
         { unfold Compose_Functors, GD, adj_mon in Hb. cbn in Hb. 
           inversion Hb. cbn.
           apply inj_pair2 in H3. unfold id in *.
           pose proof (fun x y z => eq_ind_r (fun f => f x y z = _ x y z) eq_refl H3) as H3';
           cbv beta in H3'. unfold id in *.
           now specialize (H3' _ _ f).
         }
         rewrite H2.
         destruct A1, counit. cbn in *. unfold id in *.
         rewrite assoc, <- comm_diag.
         now rewrite <- assoc, ob1, f_identity.
Qed.

(** Mac Lane's comparison theorem for the coKleisli Construction *)
Theorem duaLComparisonMacLane: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (FD (Compose_Functors G F) cM) in
                 let GD := (GD (Compose_Functors G F) cM) in
                 let A2 := (comon_cokladj (Compose_Functors G F) cM) in
                   exists !L, Compose_Functors GD L = G /\ Compose_Functors L F = FD.
Proof. intros C D F G A1 M CT FT GT A2.
       exists (duL F G A1). split.
       - apply commduL.
       - apply uniqueduL.
Qed.
Check duaLComparisonMacLane.
