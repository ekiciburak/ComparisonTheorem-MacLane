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
      unit  : (NaturalTransformation (@IdFunctor C) (Compose_Functors F G));
      counit: (NaturalTransformation (Compose_Functors G F) (@IdFunctor D));

      ob1   : forall a, (trans counit (fobj F a)) o (fmap F (trans unit a)) 
                        = @identity D (fobj F a);
      ob2   : forall a, (fmap G (trans counit a)) o (trans unit (fobj G a)) 
                        = @identity C (fobj G a)
}.

Arguments Adjunction {_} {_} _ _.

(** composing adjunctions *)
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

(** every adjunction gives raise to a monad *)
Theorem adj_mon: forall
                 {C1 C2 : Category}
                 (F     : @Functor C1 C2)
                 (G     : @Functor C2 C1),
                 let T  := (Compose_Functors F G) in
                 let T2 := (Compose_Functors T T) in
                 Adjunction F G -> Monad C1 T.
Proof. intros C1 C2 F G T T2 A. 
       unshelve econstructor; destruct A as (eta, eps, cc1, cc2).
       - exact eta.
       - refine (@mk_nt C1
                      C1
                      T2
                      T
                      (fun a => fmap G (trans eps (fobj F a))) _).
         intros a b f.
         destruct eta, eps. cbn in *.
         now rewrite <- !preserve_comp, <- comm_diag0.
       - intros. simpl in *.
         destruct eta, eps. simpl in *.
         destruct F, G. simpl in *.
         rewrite <- !preserve_comp0. unfold id in *.
         now rewrite <- comm_diag0.
       - intros. simpl in *.
         destruct eta, eps. simpl in *.
         destruct F, G. simpl in *.
         rewrite <- !preserve_comp0. unfold id in *.
         now rewrite cc2, cc1, preserve_id0.
       - intros. simpl in *.
         destruct eps, eta. simpl in *.
         destruct F, G. simpl in *. unfold id in *.
         now rewrite <- preserve_comp0, cc1, preserve_id0.
       - intros. simpl in *.
         destruct eta, eps. simpl in *.
         destruct F, G. simpl in *. unfold id in *.
         now rewrite cc2.
Defined.

(** every adjunction gives raise to a comonad *)
Theorem adj_comon: forall
                 {C1 C2: Category}
                 (F  : @Functor C1 C2)
                 (G  : @Functor C2 C1),
                 let D  := (Compose_Functors G F) in
                 let D2 := (Compose_Functors D D) in
                 Adjunction F G -> coMonad C2 D.
Proof. intros C1 C2 F G D D2 A. 
       unshelve econstructor; destruct A as (eta, eps, cc1, cc2).
       - exact eps.
       - refine (@mk_nt C2
                        C2
                        D
                        D2
                        (fun a => fmap F (trans eta (fobj G a))) _ ).
         intros a b f.
         destruct eta, eps. cbn in *. unfold id in *.
         now rewrite <- !preserve_comp, comm_diag.
       - intros. simpl in *.
         destruct eta, eps. simpl in *.
         rewrite <- !preserve_comp. unfold id in *.
         now rewrite <- comm_diag.
       - intros. destruct eta, eps. simpl in *.
         rewrite <- !preserve_comp. unfold id in *.
         now rewrite cc2, cc1, preserve_id.
       - intros. destruct eta, eps. simpl in *.
         unfold id in *. now rewrite cc1.
       - intros. destruct eta, eps. simpl in *.
         unfold id in *.
         rewrite <- preserve_comp.
         now rewrite cc2, preserve_id.
Defined.

(** every monad gives raise to a Kleisli adjunction *)
Theorem mon_kladj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := FT T M)
                   (GT := GT T M), Adjunction FT GT.
Proof. intros C D F G T M FT GT.
       unshelve econstructor.
       - unshelve econstructor.
         + intro a. destruct M as (eta, mu, cc1, cc2, cc3, cc4).
           exact (trans eta a).
         + intros. simpl in *.
           destruct M, FT, GT. destruct eta, mu. simpl in *.
           unfold id in *.
           rewrite <- assoc.
           rewrite comm_diag.
           rewrite assoc.
           rewrite comm_diagram2_b2.
           now rewrite identity_f.
       - unshelve econstructor.
         + intro a. exact (identity (fobj G (fobj F a))).
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

(** every comonad gives raise to a coKleisli adjunction *)
Theorem comon_cokladj: forall
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
       - intros. destruct A, unit0, counit0.
         cbn in *. now rewrite <- ob3.
       - intros. cbn in *.
         rewrite preserve_comp.
         destruct A, unit0, counit0. cbn in *.
         do 2 rewrite assoc.
         apply rcancel.
         rewrite <- preserve_comp.
         now rewrite <- comm_diag0.
Defined.

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

(** hepler lemma for the uniqueness proof of the comparison functor *)
Lemma adj_unique_map: forall (C D: Category) (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
       (forall (a: @obj C) (b: @obj D) (f: @arrow C (fobj G b) a) (g h: @arrow D b (fobj F a)),
         f = fmap G g o (trans (@unit C D F G A) a) -> 
         f = fmap G h o (trans (@unit C D F G A) a) -> g = h).
Proof. intros C D F G A a b f g h Hg Hh.
       destruct A as (eta, eps, cc1, cc2).
       rewrite Hg in Hh.
       apply (f_equal (fmap F)), (f_equal (fun w => comp((trans eps) _ ) w)) in Hh.
       destruct eps. cbn in *. unfold id in *.
       rewrite !preserve_comp in Hh.
       rewrite !assoc, <- !comm_diag in Hh.
       rewrite <- !assoc in Hh.
       now rewrite !cc1, !f_identity in Hh.
Qed.

(** hepler lemma for the uniqueness proof of the dual comparison functor *)
Lemma adj_unique_map_dual: forall (C D: Category) (F: Functor D C) (G: Functor C D) (A: Adjunction F G),
       (forall (a: @obj C) (b: @obj D) (f: @arrow C a (fobj F b)) (g h: @arrow D (fobj G a) b),
         f = (trans (@counit D C F G A) a) o fmap F g -> 
         f = (trans (@counit D C F G A) a) o fmap F h -> g = h).
Proof. intros. cbn in *.
         destruct A, unit0, counit0. cbn in *.
         unfold id in *.
         rewrite H in H0. remember f_equal.
         apply (f_equal (fmap G)) in H0.
         rewrite !preserve_comp in H0.
         apply (f_equal (fun w => comp w (trans _ ))) in H0.
         rewrite <- !assoc in H0. rewrite !comm_diag in H0.
         rewrite !assoc in H0.
         now rewrite !ob4, !identity_f in H0.
Qed.


(** a simple adjunction example from CIC:
conjunction and implication are adjoint operators *)
Definition FpGp_Adjoint (p: @obj CoqCatP) : Adjunction (Fp p) (Gp p).
Proof. unshelve econstructor.
       - exact (eta_GpFp p).
       - exact (eps_FpGp p).
       - intro a. extensionality H.
         now destruct H.
       - intro a. easy.
Defined.
