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
    comm_diag: forall {a b: @obj C} (f: arrow  b a), fmap G f o trans a  = trans b o fmap F f;
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

Arguments Compose_NaturalTransformations {_} {_} {_} {_} {_} _ _.

Lemma Nt_split: forall (C D: Category)
                       (F  : @Functor C D) 
                       (G  : @Functor C D)
                       (nt1: NaturalTransformation F G)
                       (nt2: NaturalTransformation F G), trans nt1 = trans nt2 <-> nt1 = nt2.
Proof. intros. split. intros. destruct nt1, nt2, F, G.
       simpl in *. revert comm_diag0. rewrite H. intros.
       specialize (proof_irrelevance (forall (a b : @obj C) (f : arrow b a),
             fmap0 a b f o trans1 a = trans1 b o fmap a b f) comm_diag0 comm_diag1).
       now destruct (proof_irrelevance _ comm_diag0 comm_diag1).
       intros. rewrite H. easy.
Qed.

Class Cone (C D: Category) (F: Functor C D): Type := mkCone
  {
     cobj: @obj D;
     cobl: NaturalTransformation (ConstantFunctor C D cobj) F
  }.

Class Limit (C D: Category) (F: Functor C D): Type := mkLimit
 {
    limc : Cone C D F;
    limob: forall (a b: @obj C) (Cn: Cone C D F), exists !(u: arrow (@cobj C D F limc) (@cobj C D F Cn)),
            trans (@cobl C D F limc) a o u = trans (@cobl C D F Cn) a /\
            trans (@cobl C D F limc) b o u = trans (@cobl C D F Cn) b 
 }.

Definition has_Limits (D: Category) := forall (C: Category) (F: Functor C D), Limit C D F.

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

Definition Cat: Category.
Proof. unshelve econstructor.
       - exact Category.
       - intros C D. exact (Functor C D).
       - intro C. exact (@Id C).
       - intros E D C F G. exact (Compose_Functors F G).
       - repeat intro. now subst.
       - intros D C B A F G H. exact (FunctorCompositionAssoc F G H).
       - intros D C F. exact (ComposeIdl F).
       - intros D C F. exact (ComposeIdr F).
Defined.

Class IsomorphismFunctorial {C D: Category} : Type := {
  toC   : Functor C D;
  fromC : Functor D C;

  iso_to_fromC : Compose_Functors toC fromC = @Id C;
  iso_from_toD : Compose_Functors fromC toC = @Id D
}.

Class IsomorphismNT {C D: Category} (F G: Functor C D): Type :=
  mk_IsomorphisnNT
  {
     nt1        : NaturalTransformation F G;
     nt2        : NaturalTransformation G F;
     equivnt_ob1: Compose_NaturalTransformations nt1 nt2 = IdNt C D F;
     equivnt_ob2: Compose_NaturalTransformations nt2 nt1 = IdNt C D G
  }.

Lemma eqIso1: forall (C D: @obj Cat), @Isomorphism Cat C D -> @IsomorphismFunctorial C D.
Proof. intros C D I; destruct I; cbn in *.
       unshelve econstructor.
       - exact iso_from_to.
       - exact iso_to_from.
Qed.

Lemma eqIso2: forall (C D: @obj Cat), @IsomorphismFunctorial C D -> @Isomorphism Cat C D.
Proof. intros C D I.
       unshelve econstructor; destruct I; cbn in *.
       - exact fromC0.
       - exact toC0.
       - exact iso_from_toD0.
       - exact iso_to_fromC0.
Qed.

Lemma eqIso3: forall C D (F G: Functor C D), 
                         @Isomorphism (FunctorCategory C D) F G ->
                         @IsomorphismNT C D F G.
Proof. intros C D F G E.
       destruct E; cbn in *.
       - unshelve econstructor.
         + exact iso_from_to.
         + exact iso_to_from.
Qed.

Lemma eqIso4: forall C D (F G: Functor C D),
                         @IsomorphismNT C D F G ->
                         @Isomorphism (FunctorCategory C D) F G.
Proof. intros C D F G I.
       destruct I; unshelve econstructor; cbn in *.
       - exact nt3.
       - exact nt4.
       - exact equivnt_ob4.
       - exact equivnt_ob3.
Qed.

Class EquivalenceCat {C D: Category} (F: Functor C D) (G: Functor D C): Type :=
  mk_EquivalenceCat
  {
     equiv_ob1: @Isomorphism (FunctorCategory C C) (Compose_Functors F G) (@Id C);
     equiv_ob2: @Isomorphism (FunctorCategory D D) (Compose_Functors G F) (@Id D)
  }.

(*
Definition CurryingFunctor (C D E: Category) (F: Functor (Product_Category C D) E):
  Functor C (FunctorCategory D E).
Proof. intros.
       unshelve econstructor.
       - cbn. intro a.
         + unshelve econstructor.
           ++ cbn. destruct F. cbn in *. intro b.
              exact (fobj (a, b)).
           ++ cbn. intros. destruct F. cbn in *.
              clear fmapP preserve_id preserve_comp.
              specialize (fmap (a, a0) (a, b)). cbn in *.
              apply fmap. exact (identity a, f).
           ++ repeat intro. now subst.
           ++ cbn. intros. destruct F. cbn in .
              now rewrite preserve_id.
           ++ cbn. intros. destruct F. cbn in *.
              specialize (preserve_comp (a, a0) (a, b) (a, c)). cbn in *.
              specialize (preserve_comp  (identity a, g) (identity a, f)). cbn in *.
              rewrite identity_f in preserve_comp. now rewrite preserve_comp.
       - intros. cbn.
         unshelve econstructor.
         + intros. cbn. destruct F. cbn in *.
           clear fmapP preserve_id preserve_comp.
           apply fmap. cbn. exact (f, identity a0).
         + intros. cbn. destruct F. cbn in *.
*)

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
                      (fun a => fmap0 _ _ (fmap _ _ (trans0 a))) _).
       intros. unfold T, T2, id in *. simpl in *.
       now rewrite <- !preserve_comp0, <- !preserve_comp, comm_diag0.
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
                      (fun a => fmap _ _ (fmap0 _ _ (trans0 a))) _).
       intros. unfold cT, cT2, id in *. simpl in *.
       now rewrite <- !preserve_comp, <- !preserve_comp0, comm_diag0.
Defined.

