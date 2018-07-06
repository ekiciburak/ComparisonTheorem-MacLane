Require Export Functor.

Arguments Compose_Functors {_} {_} {_} _ _.
Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.

Check fobj.

Class NaturalTransformation (C D: Category) 
                            (F  : Functor C D)
                            (G  : Functor C D): Type :=
  mk_nt
  {
    trans    : forall (a: @obj C), (@arrow D (fobj G a) (fobj F a));
    comm_diag: forall {a b: @obj C} (f: arrow  b a), 
               fmap _ f o trans a  = trans b o fmap _ f;
    trans_sym: forall (a b: @obj C) (f: arrow b a),
               trans b o fmap F f = fmap G f o trans a
  }.
Check NaturalTransformation.


Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.


Definition IdNt (C D: Category) 
                (F  : Functor C D): NaturalTransformation F F.
Proof. unshelve econstructor.
       - intros. exact (fmap _(@identity C a)).
       - intros. destruct F. simpl. rewrite !preserve_id.
         now rewrite identity_f, f_identity.
       - intros. cbn. 
         now rewrite !preserve_id, f_identity, identity_f.
Defined.

Program Definition Compose_NaturalTransformations_H 
                          (C D E: Category)
                          (F    : Functor C D)
                          (G    : Functor C D)
                          (H    : Functor D E)
                          (I    : Functor D E)
                          (nt1  : NaturalTransformation F G)
                          (nt2  : NaturalTransformation H I):
                                `(NaturalTransformation (Compose_Functors F H) 
                                                        (Compose_Functors G I)).
Proof. unshelve econstructor.
       - destruct F, G, H, I, nt1, nt2. simpl in *.
         intros. exact (((fmap2 _ _ (trans0 a)) o trans1 (fobj  a))).
       - destruct F, G, H, I, nt1, nt2. simpl in *.
         intros. rewrite !comm_diag1. rewrite assoc.
         rewrite comm_diag1. rewrite <- assoc.
         rewrite <- !preserve_comp1.
         rewrite <- assoc.
         rewrite <- !preserve_comp1. now rewrite comm_diag0.
       - destruct F, G, H, I, nt1, nt2. simpl in *.
         intros. rewrite !comm_diag1. rewrite assoc.
         rewrite comm_diag1. rewrite <- assoc.
         rewrite <- !preserve_comp1. rewrite trans_sym0.
         rewrite !preserve_comp1, assoc. easy.
Defined.

Program Definition Compose_NaturalTransformations 
                      (C D: Category)
                      (F  : @Functor C D)
                      (G  : @Functor C D)
                      (H  : @Functor C D)
                      (nt1: NaturalTransformation F G)
                      (nt2: NaturalTransformation G H): `(NaturalTransformation F H) :=
{|
    trans := fun a: @obj C =>  trans nt2 a o trans nt1 a;
|}.
Next Obligation.
      rewrite assoc.
      rewrite (@comm_diag C D G H nt2 a).
      do 2 rewrite <- assoc.
      rewrite (@comm_diag C D F G nt1 a).
      reflexivity.
Defined.
Next Obligation.
      rewrite <- assoc, !trans_sym.
      now rewrite assoc, trans_sym, assoc.
Defined.

Arguments Compose_NaturalTransformations {_} {_} {_} {_} {_} _ _.

Lemma Nt_split: forall (C D: Category)
                       (F  : @Functor C D) 
                       (G  : @Functor C D)
                       (nt1: NaturalTransformation F G)
                       (nt2: NaturalTransformation F G), trans nt1 = trans nt2 <-> nt1 = nt2.
Proof. intros. split. intros. destruct nt1, nt2, F, G.
       simpl in *. revert comm_diag0 trans_sym0. rewrite H. intros.
       specialize (proof_irrelevance (forall (a b : @obj C) (f : arrow b a),
             fmap0 a b f o trans1 a = trans1 b o fmap a b f) comm_diag0 comm_diag1).
       destruct (proof_irrelevance _ trans_sym0 trans_sym1).
       intros. now rewrite H0.
       intros. rewrite H. easy.
Qed.


Definition FunctorCategory (C D: Category): Category.
(* Proof. refine(@mk_Category (@Functor C D F)
                           NaturalTransformation
                           (IdNt C D F)
                           (Compose_NaturalTransformations)
                            _ _ _ ).
       intros. unfold Compose_NaturalTransformations. simpl.
       destruct a, b, c, d, f, g, h. simpl. f_equal.
*)
Proof.
       unshelve econstructor.
       - exact (Functor C D).
       - intros F G. exact (NaturalTransformation G F).
       - intros. exact (@IdNt C D a).
       - intros F G H nt1 nt2.
         exact (Compose_NaturalTransformations nt2 nt1).
       - repeat intro. now rewrite H, H0.
       - intros. apply Nt_split. simpl.
         destruct f, g, h. simpl.
         extensionality a0. now rewrite assoc.
       - intros. apply Nt_split. simpl.
         destruct f, a, b. simpl.
         extensionality a0.
         now rewrite preserve_id0, identity_f.
       - intros. apply Nt_split. simpl.
         destruct f, a, b. simpl.
         extensionality a0.
         now rewrite preserve_id, f_identity.
Defined.


Definition muT(C D   : Category) 
              (F     : @Functor C D)
              (G     : @Functor D C)
              (T     := (Compose_Functors F G))
              (T2    := (Compose_Functors T T))
              (epstr : (NaturalTransformation T (@Id C))): (NaturalTransformation T2 T).
Proof. destruct epstr, F, G. simpl in *. unfold T in *.
       refine (@mk_nt C
                      C
                      T2
                      T
                      (fun a => fmap0 _ _ (fmap _ _ (trans0 a))) _ _).
       intros. unfold T, T2, id in *. simpl in *.
       now rewrite <- !preserve_comp0, <- !preserve_comp, comm_diag0.
       intros. unfold T, T2, id in *. simpl in *.
       now rewrite <- !preserve_comp0, <- !preserve_comp, <- !trans_sym0.
Defined.

Definition delD (C D  : Category) 
                (F    : @Functor C D)
                (G    : @Functor D C)
                (cT   := (Compose_Functors G F))
                (cT2  := (Compose_Functors cT cT))
                (etatr: (NaturalTransformation (@Id D) cT)): (NaturalTransformation cT cT2).
Proof. destruct etatr, F, G. simpl in *. unfold cT in *.
       refine (@mk_nt D
                      D
                      cT
                      cT2
                      (fun a => fmap _ _ (fmap0 _ _ (trans0 a))) _ _ ).
       intros. unfold cT, cT2, id in *. simpl in *.
       now rewrite <- !preserve_comp, <- !preserve_comp0, comm_diag0.
       intros. unfold cT, cT2, id in *. simpl in *.
       now rewrite <- !preserve_comp, <- !preserve_comp0, trans_sym0.
Defined.



