Require Export Monads.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.

(** 
- proof obligations:
-- natural transformations to be introduced:
 eta_A: A   -> GFA
 eps_A: FGA -> A
-- diagrams to commute:
 1. eps_FA   o F(eta_A) = id_FA
 2. G(eps_A) o eta_GA   = id_GA
*)
Class Adjunction {C D: Category}
                 (F  : @Functor C D)
                 (G  : @Functor D C): Type :=
  mk_Adj
  {
      unit  : (NaturalTransformation (@Id C) (Compose_Functors F G));
      counit: (NaturalTransformation (Compose_Functors G F) (@Id D));

      ob1   : forall a, (trans counit (fobj F a)) o (fmap F (trans unit a)) 
                        = @identity D (fobj F a);
      ob2   : forall a, (fmap G (trans counit a)) o (trans unit (fobj G a)) 
                        = @identity C (fobj G a)
  }.
Check Adjunction.

Arguments Adjunction {_} {_} _ _.

Definition AdjCompose 
            (C D E: Category) 
            (F    : Functor C D) 
            (G    : Functor D C)
            (F'   : Functor D E) 
            (G'   : Functor E D)
            (A1   : Adjunction F G) 
            (A2   : Adjunction F' G'): Adjunction (Compose_Functors F F') (Compose_Functors G' G).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros. cbn in *.
           destruct A1, A2, unit0, unit1.
           cbn in *. unfold id in *.
           exact (fmap G (trans0 (fobj F a)) o trans a).
         + intros. cbn in *.
           destruct A1, A2, unit0, counit0, unit1, counit1. cbn in *.
           rewrite assoc.
           rewrite <- preserve_comp.
           specialize (comm_diag1 _ _ (fmap F f)).
           rewrite <- assoc.
           rewrite <- comm_diag.
           rewrite assoc.
           rewrite <- preserve_comp.
           apply rcancel.
           apply f_equal. easy.
       - unshelve econstructor.
         + intros. cbn in *.
           destruct A1, A2, counit0, counit1.
           cbn in *. unfold id in *.
           exact (trans0 a o (fmap F' (trans (fobj G' a)))).
         + intros. cbn in *.
           destruct A1, A2, unit0, counit0, unit1, counit1. cbn in *.
           rewrite <- assoc.
           rewrite <- preserve_comp.
           rewrite assoc.
           rewrite comm_diag2.
           rewrite <- assoc.
           rewrite <- preserve_comp.
           apply lcancel.
           apply f_equal.
           now rewrite <- comm_diag0.
       - intros. cbn in *.
         destruct A1, A2, unit0, counit0, unit1, counit1. cbn in *.
         unfold id in *.
         rewrite <- assoc.
         rewrite <- preserve_comp.
         assert ((trans0 (fobj G' (fobj F' (fobj F a))) o 
         fmap F (fmap G (trans1 (fobj F a)) o trans a)) = trans1 (fobj F a)).
         { now rewrite preserve_comp, assoc, <- comm_diag0, <- assoc, ob3, f_identity. }
         now rewrite H, ob5.
       - intros. cbn in *.
         destruct A1, A2, unit0, counit0, unit1, counit1. cbn in *.
         unfold id in *.
         rewrite assoc.
         rewrite <- preserve_comp.
         assert ((fmap G' (trans2 a o fmap F' (trans0 (fobj G' a))) o 
         trans1 (fobj F (fobj G (fobj G' a)))) = trans0 (fobj G' a)).
         { now rewrite preserve_comp, <- assoc, comm_diag1, assoc, ob6, identity_f. }
         now rewrite H, ob4.
Defined.

Class HomAdjunction {C D: Category} (F: Functor D C) (G: Functor C D): Type :=
  mk_Homadj
  {
     ob: @Isomorphism (FunctorCategory (D^op × C) CoqCatT) (BiHomFunctorC F G) (BiHomFunctorD F G)
  }.
Check HomAdjunction.

Theorem adjEq1 (C D: Category) (F: Functor D C) (U: Functor C D): 
Adjunction F U -> HomAdjunction F U.
Proof. intro A.
       unshelve econstructor.
       - unshelve econstructor.
         + cbn in *.
           unshelve econstructor.
           ++ intros. cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              intros. destruct a as (a, b).
              unfold id in *.
              clear comm_diag ob3 ob4.
              specialize (trans a).
              exact ((fmap0 _ _ X) o trans).
           ++ intros.  cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              intros.
              destruct a as (a0, a1).
              destruct b as (b0, b1).
              destruct f as (f, g).
              extensionality a. cbn in *.
              rewrite preserve_comp0.
              specialize (@comm_diag b0 a0 f).
              repeat rewrite <- assoc.
              rewrite assoc.
              rewrite preserve_comp0.
              apply lcancel. easy.
         + cbn in *.
           unshelve econstructor.
           ++ intros. cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              destruct a as (a, b).
              intros.
              clear comm_diag0 ob3 ob4.
              specialize (trans0 b).
              exact (trans0 o (fmap _ _ X)).
           ++ intros.  cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              intros.
              destruct a as (a0, a1).
              destruct b as (b0, b1).
              destruct f as (f, g).
              extensionality a. cbn in *.
              rewrite preserve_comp.
              specialize (@comm_diag b0 a0 f).
              repeat rewrite <- assoc.
              rewrite assoc.
              rewrite preserve_comp.
              repeat rewrite assoc.
              apply rcancel. apply rcancel.
              specialize (@comm_diag0 a1 b1 g). easy.
         + cbn in *.
           apply Nt_split. cbn in *.
           destruct A, F, U, unit0, counit0.
           cbn in *.
           extensionality a.
           extensionality b.
           destruct a as (a0, a1).
           cbn in *. rewrite preserve_id0, f_identity, identity_f.
           rewrite preserve_comp0. unfold id in *.
           specialize (@comm_diag _ _ b).
           rewrite <- assoc. rewrite comm_diag.
           specialize (ob4 a1). rewrite assoc. rewrite ob4.
           now rewrite identity_f.
         + cbn in *.
           apply Nt_split. cbn in *.
           destruct A, F, U, unit0, counit0.
           cbn in *.
           extensionality a.
           extensionality b.
           destruct a as (a0, a1).
           cbn in *. rewrite preserve_id, identity_f, f_identity.
           rewrite preserve_comp. unfold id in *.
           specialize (@comm_diag0 _ _ b).
           rewrite assoc. rewrite <- comm_diag0.
           specialize (ob3 a0). rewrite <- assoc. rewrite ob3.
           now rewrite f_identity.
Defined.

(*
Theorem adjEq2 (C D: Category) (F: Functor D C) (U: Functor C D): 
HomAdjunction F U -> Adjunction F U.
Proof. Admitted.
*)


Definition T2toT: forall
                 {C D: Category}
                 (F  : @Functor C D)
                 (U  : @Functor D C)
                 (T  := (Compose_Functors F U))
                 (T2 := (Compose_Functors T T)),
                  Adjunction F U -> (NaturalTransformation T2 T).
Proof. intros C D F U T T2 A.
       destruct F, U, A, unit0, counit0. simpl in *.
       refine (@mk_nt C
                      C
                      T2
                      T
                      (fun a => fmap0 _  _ (trans0 (fobj a))) _ ).
       intros. unfold T, T2, id in *. simpl in *.
       now rewrite <- !preserve_comp0, comm_diag0.
Defined.

Definition DtoD2: forall
                 {C D: Category}
                 (F  : Functor C D)
                 (U  : Functor D C)
                 (D  := (Compose_Functors U F))
                 (D2 := (Compose_Functors D D)),
                  Adjunction F U -> (NaturalTransformation D D2).
Proof. intros C D F U cT cT2 A.
       destruct F, U, A, unit0, counit0. simpl in *.
       refine (@mk_nt D
                      D
                      cT
                      cT2
                      (fun a => fmap _  _(trans (fobj0 a))) _ ).
       intros. unfold cT, cT2, id in *. simpl in *.
       rewrite <- !preserve_comp.
       now rewrite comm_diag.
Defined.


(** every adjunction gives raise to a monad *)
Theorem adj_mon: forall
                 {C D: Category}
                 (F  : @Functor C D)
                 (U  : @Functor D C),
                 Adjunction F U -> Monad C (Compose_Functors F U).
Proof. intros C D F U A. 
       unshelve econstructor; simpl in *.
       - destruct A. exact unit0.
       - exact (@T2toT C D F U A).
       - intros. destruct A. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         rewrite <- !preserve_comp0. unfold id in *.
         now rewrite <- comm_diag0.
       - intros. destruct A. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         rewrite <- !preserve_comp0. unfold id in *.
         now rewrite ob4, ob3, preserve_id0.
       - intros. destruct A. unfold T2toT. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         (* rewrite <- !preserve_comp0. *) unfold id in *.
         now rewrite <- preserve_comp0, ob3, preserve_id0.
       - intros. destruct A. unfold T2toT. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         (* rewrite <- !preserve_comp0. *) unfold id in *.
         now rewrite ob4.
Defined.
Check adj_mon.

(** every adjunction gives raise to a comonad *)
Theorem adj_comon: forall
                 {C D: Category}
                 (F  : @Functor C D)
                 (U  : @Functor D C),
                 Adjunction F U -> coMonad D (Compose_Functors U F).
Proof. intros C D F U A. 
       unshelve econstructor; simpl in *.
       - destruct A. exact counit0.
       - exact (@DtoD2 C D F U A).
       - intros. destruct A. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         rewrite <- !preserve_comp. unfold id in *.
         now rewrite <- comm_diag.
       - intros. destruct A. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         rewrite <- !preserve_comp. unfold id in *.
         now rewrite ob4, ob3, preserve_id.
       - intros. destruct A. unfold DtoD2. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         (* rewrite <- !preserve_comp0. *) unfold id in *.
         now rewrite ob3.
       - intros. destruct A. unfold T2toT. simpl in *.
         destruct unit0, counit0. simpl in *.
         destruct F, U. simpl in *.
         (* rewrite <- !preserve_comp0. *) unfold id in *.
         rewrite <- preserve_comp.
         now rewrite ob4.
Defined.
Check adj_comon.


Theorem mon_kladj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := LA F G M)
                   (GT := RA F G M), Adjunction FT GT.
Proof. intros.
       unshelve econstructor.
       - unshelve econstructor.
         + intros. simpl. unfold id in *.
           destruct M. simpl in *. destruct eta.
           simpl in *. unfold id in *. apply trans.
         + intros. simpl in *.
           destruct M, FT, GT. destruct eta, mu. simpl in *.
           unfold id in *.
           rewrite <- assoc.
           rewrite comm_diag.
           rewrite assoc.
           rewrite comm_diagram2_b2.
           now rewrite identity_f.
       - unshelve econstructor.
         + intros. simpl. unfold id in *. apply identity.
         + intros. simpl.
           destruct M, FT, GT. simpl in *. destruct mu, eta.
           simpl in *. unfold id in *.
           rewrite f_identity.
           repeat rewrite assoc.
           symmetry.
           assert (trans b o Functor.fmap G 
           (Functor.fmap F f) =
           (@identity C (Functor.fobj G (Functor.fobj F b))) o trans b o 
           Functor.fmap G (Functor.fmap F f) ).
           {
              now rewrite identity_f.
           }
           rewrite H. apply rcancel. apply rcancel.
           rewrite <- assoc.
           rewrite comm_diag0, f_identity.
           now rewrite comm_diagram2_b2.
       - intros. simpl in *.
         destruct M, FT, GT, eta, mu. simpl in *.
         unfold id in *.
         rewrite assoc.
         assert (trans a = (@identity C (Functor.fobj G (Functor.fobj F a))) o  trans a).
         {
            now rewrite identity_f.
         }
         rewrite H.
         rewrite assoc.
         apply rcancel.
         rewrite f_identity.
         rewrite <- assoc.
         rewrite comm_diag, f_identity.
         now rewrite comm_diagram2_b2.
       - intros. simpl in *.
         destruct M, FT, GT, eta, mu. simpl in *.
         unfold id in *.
         rewrite <- assoc.
         rewrite comm_diag, f_identity.
         now rewrite comm_diagram2_b2.
Defined.
Check mon_kladj.

Theorem mon_klhomadj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := LA F G M)
                   (GT := RA F G M), HomAdjunction FT GT.
Proof. intros.
       specialize (mon_kladj F G M); intros.
       apply adjEq1 in X. easy.
Qed.

Theorem comon_cokladj: forall
                   {C D: Category}
                   (F  : Functor D C)
                   (G  : Functor C D)
                   (D  := Compose_Functors G F)
                   (cM : coMonad C D)
                   (FD := cLA F G cM)
                   (GD := cRA F G cM), Adjunction FD GD.
Proof. intros.
       unshelve econstructor.
       - unshelve econstructor.
         + intros. simpl. unfold id in *.
           destruct cM, eps, delta. simpl in *.
           apply identity.
         + intros. simpl.
           destruct cM, FD, GD. simpl in *. destruct eps, delta.
           simpl in *. unfold id in *.
           rewrite identity_f.
           symmetry.
           assert ((trans (Functor.fobj F (Functor.fobj G a))) o 
                    Functor.fmap F (Functor.fmap G (@identity C (Functor.fobj F 
                   (Functor.fobj G a)))) o trans0 a =
                   (@identity C (Functor.fobj F (Functor.fobj G a)))).
           {
              rewrite <- comm_diag. 
              now rewrite identity_f, ccomm_diagram2_b1.
           }
           setoid_rewrite <- assoc at 2.
           setoid_rewrite <- assoc at 1.
           setoid_rewrite H. now rewrite f_identity.
       - unshelve econstructor.
         + intros. simpl. unfold id in *.
           destruct cM, eps, delta. simpl in *.  unfold id in *.
           apply trans.
         + intros. simpl in *.
           destruct cM, FD, GD, F, G. destruct eps, delta. simpl in *.
           unfold id in *.
           repeat rewrite assoc.
           rewrite preserve_comp2, preserve_comp1. 
           rewrite comm_diag.
           repeat rewrite <- assoc.
           now rewrite ccomm_diagram2_b2, f_identity.
       - intros. simpl in *.
         destruct cM, FD, GD, eps, delta. simpl in *.
         unfold id in *.
         rewrite assoc.
         destruct F, G. simpl in *.
         now rewrite preserve_id2, preserve_id1, f_identity, ccomm_diagram2_b1.
       - intros. simpl in *.
         destruct cM, FD, GD, eps, delta. simpl in *.
         unfold id in *.
         rewrite <- assoc.
         destruct F, G. simpl in *.
         now rewrite preserve_id2, preserve_id1, assoc, f_identity, 
         comm_diag, <- assoc, ccomm_diagram2_b2, f_identity.
Defined.
Check comon_cokladj.

Theorem mon_emadj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := LAEM F G M)
                   (GT := RAEM F G M), Adjunction FT GT.
Proof. intros.
       unshelve econstructor.
       - unshelve econstructor.
         + intros. destruct M, eta. cbn in *.
           unfold id in *. apply trans.
         + intros. cbn in *.
           destruct M, eta. cbn in *.
           now rewrite comm_diag.
       - unshelve econstructor.
         + intros. cbn in *.
           unshelve econstructor.
           ++ destruct a. cbn in *.
              exact alg_map.
           ++ destruct a. cbn in *.
              now rewrite alg_act.
         + intros. destruct a, b, f.
           cbn in *. apply eqTAM. cbn.
           now rewrite malg.
       - intros. cbn in *.
         apply eqTAM. cbn.
         unfold T in *.
         destruct M, T. cbn in *.
         now rewrite comm_diagram2_b1.
       - intros. cbn in *.
         destruct a. now cbn in *.
Qed.

Definition L: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (adj_mon F G A1) in
               let CM := (adj_comon F G A1) in
               let CT := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (LA F G M) in
               let GT := (RA F G M) in
               let A2 := (mon_kladj F G M) in Functor CT D.
Proof. intros. cbn in *.
       unshelve econstructor.
       - exact (fobj F).
       - intros.
         destruct CM, eps. cbn in *.
         unfold id in *. 
         exact ((trans (fobj F b)) o fmap F f).
       - repeat intro. now subst.
       - intros. destruct A1, unit0, counit0. cbn in *. now rewrite <- ob3.
       - intros. cbn in *.
         rewrite preserve_comp.
         destruct A1, unit0, counit0. cbn in *.
         do 2 rewrite assoc.
         apply rcancel.
         rewrite <- preserve_comp.
         now rewrite <- comm_diag0.
Defined.
Check L.

(*
Lemma uniqueL: forall
                 {C D: Category}
                 (F: Functor D C)
                 (G: Functor C D)
                 (A1: Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let  M := (adj_mon   F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                 unique
                    (fun L0 : CD → D =>
                     Compose_Functors GD L0 = G /\ Compose_Functors L0 F = FD) 
                    (L F G A1).
Proof. Admitted.
*)

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
                 exists L: Functor CT D,
                   (Compose_Functors FT L) = F /\ (Compose_Functors L G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
      (*
       pose proof A2 as A22.
       pose proof A1 as A11.
       apply adjEq1 in A11.
       apply adjEq1 in A22.
      *)
       exists (L F G A1).
       split. cbn in *.
       
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
       destruct A1, unit0, counit0. simpl in *.
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
       now rewrite ob3, identity_f.

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
       destruct A1, unit0, counit0. simpl in *.
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
       extensionality f.
       now rewrite preserve_comp0.
Qed.
Check ComparisonMacLane.

Definition duL: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let  M := (adj_mon   F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in Functor CD D.
Proof. intros C D F G A1 cM M CD FD GD A2. simpl in *.
       unshelve econstructor.
       - exact (fobj G).
       - intros.
         destruct M, eta.
         exact ((fmap G f) o (trans (fobj G a))).
       - repeat intro. subst. easy.
       - intros. simpl in *. destruct A1. now rewrite ob4.
       - intros. simpl in *. rewrite preserve_comp.
         rewrite <- assoc.
         destruct A1, unit0. cbn in *.
         rewrite comm_diag.
         rewrite preserve_comp.
         do 2 rewrite assoc.
         apply rcancel.
         do 2 rewrite <- assoc.
         apply lcancel.
         unfold id in *.
         now rewrite comm_diag.
Defined.
Check duL.

(*
Lemma uniqueduL: forall
                 {C D: Category}
                 (F: Functor D C)
                 (G: Functor C D)
                 (A1: Adjunction F G),
                 let cM := (adj_comon F G A1) in
                 let  M := (adj_mon   F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                 unique
                    (fun L0 : CD → D =>
                     Compose_Functors GD L0 = G /\ Compose_Functors L0 F = FD) 
                    (L F G A1).
Proof. Admitted.
*)


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
       apply adjEq1 in A11.
       apply adjEq1 in A22.
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
       destruct A1, unit0, counit0. simpl in *.
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
       now rewrite ob4, f_identity.

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
       destruct A1, unit0, counit0. simpl in *.
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



