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

(*
Definition Eta (p a: Prop) (H: id a) (H1: p): p /\ a := conj H1 H.

Definition Eps (p a: Prop) (H: p /\ (p -> a)): id a :=
  match H with
    | conj x y => y x
  end.
*)

Definition eta_GpFp: forall (p: @obj CoqCatP),
  NaturalTransformation Id (Compose_Functors (Fp p) (Gp p)).
Proof. intro p.
       unshelve econstructor.
       - cbn in *. 
         unfold fobjFp, fobjGp. intro q.
         exact (fun (pq: id q) (pp: p) => conj pp pq).
       - cbn. intros a b f.
         extensionality pa. easy.
Defined.


Definition eps_FpGp: forall (p: @obj CoqCatP),
  NaturalTransformation (Compose_Functors (Gp p) (Fp p)) Id.
Proof. intro p.
       unshelve econstructor.
       - cbn in *.
         unfold fobjFp, fobjGp. intro q.
         exact (fun (H: p /\ (p -> q)) => match H with conj pp ppiq => ppiq pp end).
       - cbn. intros a b f.
         extensionality pp. 
         destruct pp. easy.
Defined.

Definition FpGp_Adjoint (p: @obj CoqCatP) : Adjunction (Fp p) (Gp p).
Proof. unshelve econstructor.
       - exact (eta_GpFp p).
       - exact (eps_FpGp p).
       - intro a. extensionality H.
         now destruct H.
       - intro a. easy.
Defined.

(** no proof? *)
(*
Definition FpGp_Isomorph (p: @obj CoqCatP): @Isomorphism (FunctorCategory CoqCatP CoqCatP) (Fp p) (Gp p).
Proof. unshelve econstructor.
       - cbn in *.
         + unshelve econstructor.
           ++ intros. cbn in *.
              intros. easy.
           ++ intros. cbn in *.
              extensionality H.
              destruct H. easy.
           ++ intros. cbn in *.
              extensionality H.
              destruct H. easy.
      - cbn in *.
         + unshelve econstructor.
           ++ intros. cbn in *.
              intros. split. easy.
           ++ intros. cbn in *.
              extensionality H.
              destruct H. easy.
           ++ intros. cbn in *.
              extensionality H.
              destruct H. easy.
*)

Class Adjunct {C D: Category}
              (F  : @Functor C D)
              (G  : @Functor D C): Type :=
  mk_Adt
  {
      adj_unit    :    (NaturalTransformation (@Id C) (Compose_Functors F G));
      adj_morph_ex     {c: @obj C} {d: @obj D} (f: @arrow C (fobj G d) c): @arrow D d (fobj F c);
      adj_morph_com    {c: @obj C} {d: @obj D} (f: @arrow C (fobj G d) c): f = fmap G (adj_morph_ex f) o (trans (adj_unit) c);
      adj_morph_unique {c: @obj C} {d: @obj D} (f: @arrow C (fobj G d) c) (g h: @arrow D d (fobj F c)):
         f = fmap G g o (trans (adj_unit) c) -> 
         f = fmap G h o (trans (adj_unit) c) -> g = h
  }.

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

Lemma adjEq10_1: forall (C D: Category) (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
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

Lemma adjEq10_2: forall (C D: Category) (F: Functor D C) (G: Functor C D) (A: Adjunction F G),
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

Lemma adjEq10_10: forall (C D: Category) (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
       (forall (a: @obj C) (b: @obj D) (f: @arrow C (fobj G b) a),
        exists !(g: @arrow D b (fobj F a)),
         f = fmap G g o (trans (@unit C D F G A) a)).
Proof. intros. cbn in *.
         destruct A, unit0, counit0. cbn in *.
         unfold id in *.
         exists (trans0 b o fmap F f). 
         unfold unique. split.
         now rewrite preserve_comp, <- assoc, comm_diag, assoc,
         ob4, identity_f.
         intros.
         apply (f_equal (fmap F)) in H.
         rewrite !preserve_comp in H.
         apply (f_equal (fun w => comp(trans0 _ ) w)) in H.
         rewrite !assoc in H. rewrite <- !comm_diag0 in H.
         rewrite <- !assoc in H.
         now rewrite !ob3, !f_identity in H.
Qed.


Definition adjEq10 (C D: Category) (F: Functor C D) (U: Functor D C) (A: Adjunction F U): Adjunct F U.
Proof. unshelve econstructor.
       - destruct A. exact unit0.
       - intros. destruct A, unit0, counit0. cbn in *.
         unfold id in *. exact (trans0 d o fmap F f).
       - cbn. intros. destruct A, unit0, counit0. cbn in *.
         unfold id in *. rewrite preserve_comp.
         rewrite <- assoc. rewrite comm_diag.
         now rewrite assoc, ob4, identity_f.
       - intros. cbn in *.
         destruct A, unit0, counit0. cbn in *.
         unfold id in *.
         rewrite H in H0. remember f_equal.
         apply (f_equal (fmap F)) in H0.
         rewrite !preserve_comp in H0.
         apply (f_equal (fun w => comp(trans0 _ ) w)) in H0.
         rewrite !assoc in H0. rewrite <- !comm_diag0 in H0.
         rewrite <- !assoc in H0.
         now rewrite !ob3, !f_identity in H0.
Defined.

Definition adjEq01 (C D: Category) (F: Functor C D) (U: Functor D C) (A: Adjunct F U): Adjunction F U.
Proof. unshelve econstructor.
       - destruct A. exact adj_unit0.
       - unshelve econstructor.
         + intros. destruct A, adj_unit0. unfold Id. cbn in *. unfold id in *.
           apply adj_morph_ex0. exact (identity (fobj U a)).
         + intros. cbn in *.
           destruct A, adj_unit0. cbn in *. unfold id in *.
           apply adj_morph_unique0 with (f := fmap U f );
           rewrite !preserve_comp.
           now rewrite <- assoc, <- adj_morph_com0, f_identity.
           rewrite <- assoc. rewrite comm_diag.
           now rewrite assoc, <- adj_morph_com0, identity_f.
       - intros. cbn in *.
         destruct A, adj_unit0. cbn in *. unfold id in *.
         apply adj_morph_unique0 with (f := trans a).
         pose proof adj_morph_com0 as adj_morph_com1.
         specialize (adj_morph_com0 (fobj U (fobj F a)) (fobj F a) (identity (fobj U (fobj F a))) ).
         assert (trans a = identity (fobj U (fobj F a))  o trans a).
         { now rewrite identity_f. } rewrite H at 1. 
         rewrite adj_morph_com0 at 1.
         rewrite <- adj_morph_com1.
         rewrite preserve_comp. rewrite <- assoc, comm_diag.
         rewrite assoc. apply rcancel. easy.
         now rewrite preserve_id, identity_f.
       - intros. cbn in *.
         destruct A, adj_unit0. cbn in *. unfold id in *.
         now rewrite adj_morph_com0.
Defined.

Class HomAdjunction {C D: Category} (F: Functor C D) (G: Functor D C): Type :=
  mk_Homadj
  {
     ob: @Isomorphism (FunctorCategory (C^op × D) CoqCatT) (BiHomFunctorC G) (BiHomFunctorD F)
  }.
Check HomAdjunction.

(*
Lemma adjEq12 (C D: Category) (F: Functor C D) (G: Functor D C): 
Adjunction F G -> @Isomorphism (FunctorCategory (C^op × D) CoqCatT) (BiHomFunctorC G) (BiHomFunctorD F).
Proof. intro A.
       unshelve econstructor.
       - unshelve econstructor.
         + cbn in *. intros. cbn in *.
              destruct A, F, G, unit0, counit0.
              cbn in *.
              intros. destruct a as (a, b).
              unfold id in *.
              clear comm_diag0 trans_sym0 ob3 ob4.
              specialize (trans0 b).
              exact (trans0 o (fmap _ _ X)).
           + intros.  cbn in *.
              destruct A, F, G, unit0, counit0.
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
           + intros.  cbn in *.
              destruct A, F, G, unit0, counit0.
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
         - cbn in *.
           unshelve econstructor.
           + intros. cbn in *.
              destruct A, F, G, unit0, counit0.
              cbn in *.
              destruct a as (a, b).
              intros.
              clear comm_diag trans_sym ob3 ob4.
              specialize (trans a).
              exact ((fmap0 _ _ X) o trans).
           + intros.  cbn in *.
              destruct A, F, G, unit0, counit0.
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
           + intros.  cbn in *.
              destruct A, F, G, unit0, counit0.
              cbn in *.
              intros.
              destruct a as (a0, a1).
              destruct b as (b0, b1).
              destruct f as (f, g).
              extensionality a. cbn in *.
              rewrite preserve_comp0.
              specialize (@comm_diag b0 a0 f).
              repeat rewrite <- assoc.
              rewrite !preserve_comp0.
              rewrite <- assoc.
              apply lcancel. apply lcancel.
              now rewrite <- trans_sym.
         - cbn in *.
           apply Nt_split. cbn in *.
           destruct A, F, G, unit0, counit0.
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
         - cbn in *.
           apply Nt_split. cbn in *.
           destruct A, F, G, unit0, counit0.
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
Qed.
*)


Lemma adjEq12 (C D: Category) (F: Functor C D) (U: Functor D C): 
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
           unshelve econstructor.
           ++ intros. cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              destruct a as (a, b).
              intros.
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
Defined.

Lemma adjEq21 (C D: Category) (F: Functor C D) (U: Functor D C): 
HomAdjunction F U -> Adjunction F U.
Proof. intro A.
       unshelve econstructor.
       - unshelve econstructor.
         + intros. cbn in *.
           destruct A, ob0, to, from. cbn in *.
           clear comm_diag iso_to_from comm_diag0 iso_from_to.
           specialize (trans0 (a, (fobj F a))).
           cbn in *. apply trans0.
           exact (identity (fobj F a)).
         + cbn in *. intros.
           destruct A, ob0, to, from. cbn in *.
           clear iso_to_from iso_from_to.
           pose proof comm_diag0 as comm_diag00.
           specialize (comm_diag0 (a, (fobj F a))). cbn in *.
           specialize (comm_diag0 (a, (fobj F b))). cbn in *.
           specialize (comm_diag0 ((identity a), (fmap F f))).
           cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diag0) as H';
           cbv beta in H'.
           specialize (H'  (identity (fobj F a))).
           rewrite !preserve_id, !f_identity in H'.
           
           assert (trans0 (a, fobj F b) (fmap F f) = trans0 (b, fobj F b) (identity (fobj F b)) o f).
           {           
            specialize (comm_diag00 (b, (fobj F b))). cbn in *.
            specialize (comm_diag00 (a, (fobj F b))). cbn in *.
            specialize (comm_diag00 (f, (identity (fobj F b))) ).
            cbn in *. 
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diag00) as H'';
           cbv beta in H''.
           specialize (H''  (identity (fobj F b))).
           rewrite !preserve_id, !f_identity, !identity_f in H''. easy. } 
           rewrite H in H'. easy.
       - unshelve econstructor.
         + intros. cbn in *.
           destruct A, ob0, to, from. cbn in *.
           clear comm_diag iso_to_from comm_diag0 iso_from_to.
           specialize (trans ((fobj U a), a)).
           cbn in *. apply trans.
           exact (identity (fobj U a)).
         + cbn in *. intros.
           destruct A, ob0, to, from. cbn in *.
           clear iso_to_from iso_from_to.
           pose proof comm_diag as comm_diagg.
           specialize (comm_diag ((fobj U a), a)). cbn in *.
           specialize (comm_diag ((fobj U a), b)). cbn in *.
           specialize (comm_diag ((identity (fobj U a)), f)).
           cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diag) as H';
           cbv beta in H'.
           specialize (H'  (identity (fobj U a))).
           rewrite !preserve_id, !f_identity in H'.

           assert (trans (fobj U a, b) (fmap U f) = trans (fobj U b, b) (identity (fobj U b)) o fmap F (fmap U f)).
           {
            specialize (comm_diagg ((fobj U b), b)). cbn in *.
            specialize (comm_diagg ((fobj U a), b)). cbn in *.
            specialize (comm_diagg ((fmap U f), (identity b))).
            cbn in *. 
            pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diagg) as H'';
            cbv beta in H''.
            specialize (H''  (identity (fobj U b))).
            rewrite !preserve_id, !f_identity, !identity_f in H''. easy. } 
           rewrite H in H'. easy.

       - cbn in *. intros.
         destruct A, ob0, to, from. cbn in *.
         pose proof comm_diag as comm_diagg.

         specialize (comm_diagg ((fobj U (fobj F a)), (fobj F a))). cbn in *.
         specialize (comm_diagg (a, (fobj F a))). cbn in *.
         specialize (comm_diagg (trans0 (a, fobj F a) (identity (fobj F a)), (identity (fobj F a)))).
         cbn in *. 
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diagg) as H'';
         cbv beta in H''.
         specialize (H''  (identity (fobj U (fobj F a)))).
         rewrite !preserve_id, !f_identity, !identity_f in H''.
         assert (trans (a, fobj F a) (trans0 (a, fobj F a) (identity (fobj F a))) = identity (fobj F a)).
         { 
           apply Nt_split in iso_to_from. cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl iso_to_from) as H';
           cbv beta in H'.
           specialize (H' (a, (fobj F a))). cbn in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H') as H0;
           cbv beta in H0.
           specialize (H0 (identity (fobj F a))).
           rewrite !identity_f, preserve_id in H0. easy.
          }
         rewrite H in H''. easy.

       - cbn in *. intros.
         destruct A, ob0, to, from. cbn in *.
         pose proof comm_diag0 as comm_diagg.

         specialize (comm_diagg ((fobj U a), (fobj F (fobj U a)))). cbn in *.
         specialize (comm_diagg ((fobj U a), a)). cbn in *.
         specialize (comm_diagg ((identity (fobj U a)), (trans (fobj U a, a) (identity (fobj U a))))).
         cbn in *.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diagg) as H'';
         cbv beta in H''.
         specialize (H''  (identity (fobj F (fobj U a)))).
         rewrite  !preserve_id, !f_identity in H''.
         assert (trans0 (fobj U a, a) (trans (fobj U a, a) (identity (fobj U a))) = identity (fobj U a)).
         { 
           apply Nt_split in iso_from_to. cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl  iso_from_to) as H';
           cbv beta in H'.
           specialize (H' ((fobj U a), a)). cbn in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H') as H0;
           cbv beta in H0.
           specialize (H0 (identity (fobj U a))).
           rewrite !f_identity, preserve_id in H0. easy.
          }
         rewrite H in H''. easy.
Qed.

Definition T2toT: forall
                 {C D: Category}
                 (F  : @Functor C D)
                 (G  : @Functor D C)
                 (T  := (Compose_Functors F G))
                 (T2 := (Compose_Functors T T)),
                  Adjunction F G -> (NaturalTransformation T2 T).
Proof. intros C D F G T T2 A.
       destruct A as (eta, eps, cc1, cc2).
       refine (@mk_nt C
                      C
                      T2
                      T
                      (fun a => fmap G (trans eps (fobj F a))) _).
       intros. unfold T, T2, id in *. simpl in *.
       destruct eta, eps. cbn in *.
       now rewrite <- !preserve_comp, <- comm_diag0.
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
         destruct F, G. simpl in *.
         (* rewrite <- !preserve_comp0. *) unfold id in *.
         now rewrite <- preserve_comp0, cc1, preserve_id0.
       - intros. simpl in *.
         destruct eta, eps. simpl in *.
         destruct F, G. simpl in *.
         (* rewrite <- !preserve_comp0. *) unfold id in *.
         now rewrite cc2.
Defined.
Check adj_mon.


(** every hom-adjunction gives raise to a monad *)
Theorem homadj_mon: forall
                 {C D: Category}
                 (F  : @Functor C D)
                 (U  : @Functor D C),
                 HomAdjunction F U -> Monad C (Compose_Functors F U).
Proof. intros C D F U A. apply adjEq21 in A.
       now apply adj_mon.
Defined.
Check homadj_mon.

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
Check adj_comon.


(** every hom-adjunction gives raise to a comonad *)
Theorem homadj_comon: forall
                 {C D: Category}
                 (F  : @Functor C D)
                 (U  : @Functor D C),
                 HomAdjunction F U -> coMonad D (Compose_Functors U F).
Proof. intros C D F U A. apply adjEq21 in A.
       now apply adj_comon.
Defined.
Check homadj_comon.


Theorem mon_kladj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := FT F G M)
                   (GT := GT F G M), Adjunction FT GT.
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
Check mon_kladj.

Theorem mon_klhomadj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := FT F G M)
                   (GT := GT F G M), HomAdjunction FT GT.
Proof. intros.
       specialize (mon_kladj F G M); intros.
       apply adjEq12 in X. easy.
Defined.

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

Theorem comon_coklhomadj: forall
                   {C D: Category}
                   (F  : Functor D C)
                   (G  : Functor C D)
                   (D  := Compose_Functors G F)
                   (cM : coMonad C D)
                   (FD := cLA F G cM)
                   (GD := cRA F G cM), HomAdjunction FD GD.
Proof. intros. apply adjEq12. 
       apply comon_cokladj.
Defined.

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
         + intros. destruct a. cbn in *.
           unshelve econstructor.
           ++ destruct t. cbn in *.
              exact x0.
           ++ destruct t. cbn in *.
              destruct a.
              now rewrite H0.
         + intros. destruct a, b, f.
           cbn in *. apply eqTAM. cbn in *.
           easy.
       - intros. cbn in *.
         apply eqTAM. cbn.
         unfold T in *.
         destruct M, T. cbn in *.
         now rewrite comm_diagram2_b1.
       - intros. cbn in *.
         destruct a, t. now cbn in *.
Defined.

Theorem mon_emhomadj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := LAEM F G M)
                   (GT := RAEM F G M), HomAdjunction FT GT.
Proof. intros. apply adjEq12.
       apply mon_emadj.
Defined.

Definition L: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A     : Adjunction F G),
               let M  := (adj_mon F G A) in
               let CM := (adj_comon F G A) in
               let CK := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FT F G M) in
               let GT := (GT F G M) in Functor CK D.
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
Check L.

Definition invK: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (adj_mon F G A1) in
               let CM := (adj_comon F G A1) in
               let EMC:= (EilenbergMooreCategory C (Compose_Functors F G) M) in Functor EMC D.
Proof. intros.
       unshelve econstructor.
       - intro a. cbn in *.
         destruct a. exact (fobj F x).
       - intros a b f. destruct a, b, f. cbn in *.
         exact (fmap F x1).
       - repeat intro. now subst.
       - intros. destruct a. cbn in *. now rewrite preserve_id.
       - intros. destruct a, b, c. cbn in *. destruct g, f. now rewrite preserve_comp.
Defined.
Check invK.

Definition K: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (adj_mon F G A1) in
               let EMC:= (EilenbergMooreCategory C (Compose_Functors F G) M) in Functor D EMC.
Proof. intros.
       unshelve econstructor.
       - intro a. cbn in *.
         + unshelve econstructor.
           ++ exact (fobj G a).
           ++ unshelve econstructor.
              +++ exact (fmap G (trans (@counit _ _ _ _ A1) a)).
              +++ split. now rewrite (@ob2 _ _ _ _ A1).
                  destruct A1, counit0. cbn in *.
                  rewrite <- !preserve_comp.
                  now rewrite <- comm_diag.
       - intros. cbn in *.
         + unshelve econstructor.
           ++ exact (fmap G f).
           ++ cbn in *.
              destruct A1, counit0. cbn in *.
              rewrite <- preserve_comp.
              rewrite <- comm_diag.
              now rewrite preserve_comp.
       - repeat intro.
         now subst.
       - intro a. cbn in.
         apply eqTAM. cbn in *.
         now rewrite preserve_id.
       - intros a b c g f.
         apply eqTAM.
         cbn in *.
         now rewrite preserve_comp.
Defined. 
Check K.

(*
Definition K: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (adj_mon F G A1) in
               let EMC:= (EilenbergMooreCategory C (Compose_Functors F G) M) in Functor D EMC.
Proof. intros.
       unshelve econstructor.
       - intro a. cbn in *.
         + unshelve econstructor.
           ++ exact (fobj G a).
           ++ cbn in *. destruct A1, unit0, counit0. cbn in *.
              unfold id in *.
              exact ( (fmap G (trans0 a)) o (fmap G (fmap F (fmap G (trans0 a)))) o 
                                 trans (fobj G (fobj F (fobj G a))) ).
           ++ cbn in *.
              destruct A1, unit0, counit0. cbn in *.
              rewrite <- assoc, <- preserve_comp.
              rewrite <- comm_diag0.
              rewrite preserve_comp.
              rewrite <- ob4. rewrite !assoc. apply rcancel.
              rewrite <- !assoc.
              assert (fmap G (trans0 a) = fmap G (trans0 a) o identity (fobj G (fobj F (fobj G a)))).
              { now rewrite f_identity. }
              symmetry. rewrite H. apply lcancel.
              now rewrite <- ob4.
           ++ cbn in *.
              destruct A1, unit0, counit0. cbn in *.
              symmetry. rewrite <- preserve_comp.
              rewrite <- comm_diag0.
              rewrite preserve_comp.
              repeat setoid_rewrite <- assoc at 1.
              assert (fmap G (trans0 a) o (fmap G (trans0 (fobj F (fobj G a))) o 
              trans (fobj G (fobj F (fobj G a)))) o fmap G (trans0 (fobj F (fobj G a))) = 
              fmap G (trans0 a) o fmap G (trans0 (fobj F (fobj G a)))).
              { rewrite ob4. now rewrite f_identity. }

              assert(fmap G (trans0 a)
              o (fmap G (trans0 (fobj F (fobj G a))) o 
              (trans (fobj G (fobj F (fobj G a))) o 
              fmap G (fmap F (fmap G (trans0 a) o 
              (fmap G (trans0 (fobj F (fobj G a))) o 
              trans (fobj G (fobj F (fobj G a)))))))) =
              fmap G (trans0 a) o fmap G (trans0 (fobj F (fobj G a)))
              ).
              {
                rewrite <- !preserve_comp.
                rewrite !ob4. rewrite !f_identity.
                rewrite <- trans_sym0.
                rewrite !assoc.
                rewrite assoc in H.
                repeat rewrite <- assoc.
                rewrite assoc.
                unfold id in *.
                repeat setoid_rewrite <- assoc at 1.
                setoid_rewrite assoc at 2.
                setoid_rewrite assoc at 1.
                rewrite ob4.
                rewrite !f_identity.
                rewrite preserve_comp.
                easy.
              }
              rewrite <- H in H0.
              rewrite !assoc in *.
              easy.
       - intros. cbn in *. 
         + unshelve econstructor.
           ++ cbn in *. exact (fmap G f).
           ++ cbn in *.
              destruct A1, unit0, counit0. cbn in *.
              remember compose_respects.
              remember fmapP.
              rewrite !assoc.
              rewrite <- preserve_comp.
              rewrite <- comm_diag0.
              rewrite preserve_comp.
              repeat setoid_rewrite <- assoc at 1.
              setoid_rewrite assoc at 2.
              setoid_rewrite assoc at 1.
              symmetry.
              remember compose_respects.
              repeat setoid_rewrite <- assoc at 1.
              setoid_rewrite assoc at 2.
              setoid_rewrite assoc at 1.
              rewrite <- preserve_comp.
              rewrite <- comm_diag0.
              rewrite preserve_comp.
              rewrite assoc.
              repeat setoid_rewrite <- assoc at 1.
              setoid_rewrite assoc at 1.
              assert (fmap G f o fmap G (trans0 a) o 
              (fmap G (trans0 (fobj F (fobj G a))) o 
              trans (fobj G (fobj F (fobj G a)))) = 
              fmap G f o fmap G (trans0 a)
              ).
              { rewrite ob4. now rewrite f_identity. }
              assert (
              fmap G (trans0 b) o (fmap G (trans0 (fobj F (fobj G b))) o 
              (trans (fobj G (fobj F (fobj G b))) o 
              fmap G (fmap F (fmap G f)))) =
              fmap G (trans0 b) o fmap G (fmap F (fmap G f))).
              { repeat setoid_rewrite <- assoc at 1.
                apply lcancel.
                rewrite assoc.
                rewrite ob4.
                now rewrite identity_f.
              }
              assert (fmap G f o fmap G (trans0 a)= 
              fmap G (trans0 b) o fmap G (fmap F (fmap G f))).
              { rewrite <- !preserve_comp.
                apply f_equal. 
                apply comm_diag0.
              }
              rewrite <- H1 in H0.
              rewrite <- H in H0.
              easy.
       - repeat intro.
         now subst.
       - intro a. cbn in.
         apply eqTAM. cbn in *.
         now rewrite preserve_id.
       - intros a b c g f.
         apply eqTAM.
         cbn in *.
         now rewrite preserve_comp.
Defined. (** takes time: ~ 22 secs *)
Check K.
*)

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

Class MapOfAdjunctions {X A X' A': Category} 
  (F : Functor X A)    (G : Functor A X)
  (F': Functor X' A')  (G': Functor A' X')
  (A1: Adjunction F G) (A2: Adjunction F' G'): Type :=
  mk_MOA
  {
     fK     : Functor A A';
     fL     : Functor X X';
     moa_ob1: Compose_Functors F fK = Compose_Functors fL F';
     moa_ob2: Compose_Functors G fL = Compose_Functors fK G';
     moa_ob3: forall a, JMeq (fmap fL (trans (@unit X A F G A1) a)) ((trans (@unit X' A' F' G' A2)) (fobj fL a))
  }.

Lemma moaL: forall
                 {C D: Category}
                 (F: Functor C D)
                 (G: Functor D C)
                 (A1: Adjunction F G),
                 let  M := (adj_mon   F G A1) in
                 let CT := (Kleisli_Category C (Compose_Functors F G) M) in
                 let FT := (FT F G M) in
                 let GT := (GT F G M) in 
                 let A2 := (mon_kladj F G M) in MapOfAdjunctions FT GT F G A2 A1.
Proof. intros.
       unshelve econstructor.
       - exact (L F G A1).
       - exact IdFunctor.
       - unfold M, CT, GT. cbn in *.
         assert (fobj (Compose_Functors FT (L F G A1)) = fobj F).
         { 
             unfold Compose_Functors. simpl in *.
             unfold id in *. easy.
         }
         simpl.
         specialize (F_split C D
           (Compose_Functors FT (L F G A1)) F); intros.
         specialize (H0 H).
         assert (HC: Compose_Functors IdFunctor F = F).
         { now apply ComposeIdl. } 
         rewrite HC.
         apply H0.
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
       - simpl in *.
         assert (fobj (Compose_Functors (L F G A1) G) = fobj GT).
         { 
             unfold Compose_Functors. simpl in *.
             unfold id in *. easy.
         }
         simpl.
         specialize (F_split (Kleisli_Category C 
           (Compose_Functors F G) M) C 
           (Compose_Functors (L F G A1) G) GT); intros.
         specialize (H0 H).
         assert (HC: Compose_Functors GT IdFunctor = GT).
         { now apply ComposeIdr. } 
         rewrite HC. symmetry.
         apply H0.
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
         extensionality f. now rewrite preserve_comp0.
       - intros. destruct A1, A2, unit0, unit1. cbn in *.
         unfold id in *.  apply eq_dep_JMeq.
         apply EqdepFacts.eq_sigT_eq_dep. apply eq_existT_uncurried. cbn.
         exists eq_refl. cbn in *.
        admit.
Admitted.




