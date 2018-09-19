Require Export NaturalTransformation.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.

Class Monad (C: Category) 
            (T: Functor C C): Type :=
  mk_Monad
  {

    eta : NaturalTransformation Id T;
    mu  : NaturalTransformation (Compose_Functors T T) T;
    comm_diagram1   : forall (a: @obj C), 
                        (trans mu a) o (fmap T (trans mu a)) = 
                        (trans mu a) o (trans mu (fobj T a));
    comm_diagram2   : forall (a: @obj C), 
                        (trans mu a) o (fmap T (trans eta a)) = 
                        (trans mu a) o (trans eta (fobj T a));
    comm_diagram2_b1: forall (a: @obj C), 
                        (trans mu a) o (fmap T (trans eta a)) = 
                        (identity (fobj T a));
    comm_diagram2_b2: forall (a: @obj C), (trans mu a) o (trans eta (fobj T a)) =
                        (identity (fobj T a))
  }.
Check Monad.

Class MonadTransformer (C : Category) 
                       (F : Functor C C)
                       (M1: Monad C F)
                       (Tr: (Functor C C) -> (Functor C C))
                       (M2: Monad C (Tr F)): Type :=
  mk_MonadTransformer
  {
     lift: forall a: @obj C, arrow (fobj (Tr F) a) (fobj F a);
     lob1: forall a: @obj C, lift a o (trans (@eta C F M1) a) = (trans (@eta C (Tr F) M2) a);
     lob2: forall (a b: @obj C) (f: arrow (fobj F b) a),
           lift b o (trans (@mu C F M1) b) o (fmap F f) = (trans (@mu C (Tr F) M2) b) o fmap (Tr F) (lift b o f) o lift a
  }.
Check MonadTransformer.

Arguments MonadTransformer {_ _} _ {_} _.

Class coMonad (C: Category) 
              (D: Functor C C): Type :=
  mk_coMonad
  {
    eps    : NaturalTransformation D Id;
    delta  : NaturalTransformation D (Compose_Functors D D);
    ccomm_diagram1   : forall (a: @obj C),
                       (fmap D (trans delta a)) o (trans delta a) = 
                       (trans delta (fobj D a)) o (trans delta a);
    ccomm_diagram2   : forall (a: @obj C),
                       (fmap D (trans eps a)) o (trans delta a) =
                       (trans eps (fobj D a)) o (trans delta a);
    ccomm_diagram2_b1: forall (a: @obj C),
                       (trans eps (fobj D a)) o (trans delta a) =
                       (identity (fobj D a));
    ccomm_diagram2_b2: forall (a: @obj C),
                       (fmap D (trans eps a)) o (trans delta a) =
                       (identity (fobj D a))
  }.
Check coMonad.

Theorem rcancel:  forall {C: Category} {a b c: @obj C}
                         (f g: arrow c b) (h: arrow b a), 
                          f = g -> f o h = g o h.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem lcancel:  forall {C: Category} {a b c: @obj C}
                         (f g: arrow b a) (h: arrow c b), 
                         f = g -> h o f  = h o g.
Proof. intros. rewrite H. reflexivity. Qed.

Definition Kleisli_Category 
            (C: Category) 
            (T: Functor C C)
            (M: Monad C T) : (Category).
Proof. destruct M. destruct eta0, mu0. simpl in *.
       unshelve econstructor.
       - exact (@obj C).
       - intros a b. exact (@arrow C (fobj T a) b).
       - intros.  exact ((@trans a)).
       - intros a b c g f. simpl in *.
         exact ((@trans0 c) o (fmap T g) o f).
       - repeat intro. now subst.
       - intros. simpl in *. destruct T. simpl in *.
         unfold Id, id in *. simpl in *.
         rewrite preserve_comp.
         rewrite assoc. rewrite preserve_comp. 
         rewrite assoc. do 2 rewrite assoc. rewrite (comm_diagram3 d).
         specialize(@comm_diag0 c (fobj d) h).
         (* rewrite comm_diag1. *) 
         apply rcancel. apply rcancel.
         rewrite <- assoc. rewrite <- assoc.
         rewrite comm_diag0.
         (* unfold Compose_Functors in *. unfold fmap in *. simpl in *. *) 
         reflexivity.
       - intros. unfold id in *. simpl in *. unfold id in *.
         rewrite comm_diagram2_b3. now rewrite identity_f.
       - intros. unfold id in *. simpl in *. unfold id in *.
         specialize (comm_diag0 a (fobj T b) f).
         rewrite <- assoc.
         rewrite comm_diag. rewrite assoc.
         now rewrite comm_diagram2_b4, identity_f.
Defined.
Check Kleisli_Category.

Definition coKleisli_Category 
            (C : Category) 
            (D : Functor C C)
            (cM: coMonad C D) : (Category).
Proof. destruct cM. destruct eps0, delta0. simpl in *.
       unshelve econstructor.
       - exact (@obj C).
       - intros a b. exact (@arrow C (id a) (fobj D b)).
       - intros. unfold id in *. exact ((@trans a)).
       - intros a b c g f. simpl in *.
         exact (g o (fmap D  f) o (trans0 a)).
       - repeat intro. rewrite H, H0 in *. easy.
       - intros. simpl in *. destruct D. simpl in *.
         unfold Id, id in *. simpl in *.
         rewrite preserve_comp.
         rewrite assoc. rewrite preserve_comp. 
         rewrite assoc. rewrite <- assoc. 
         rewrite (ccomm_diagram3 a).
         rewrite assoc. apply rcancel.
         do 2 rewrite <- assoc.
         rewrite comm_diag0.
         now do 2 rewrite assoc.
       - intros. unfold id in *. simpl in *. unfold id in *.
         rewrite <- comm_diag.
         now rewrite <- assoc, ccomm_diagram2_b3, f_identity.
       - intros. unfold id in *. simpl in *. unfold id in *.
         now rewrite <- assoc, ccomm_diagram2_b4, f_identity.
Defined.
Check coKleisli_Category.

(*
Class TAlgebra (C: Category)
               (T: Functor C C)
               (M: Monad C T) :=
  {
     alg_obj: @obj C;
     alg_map: arrow alg_obj (fobj T alg_obj);
     alg_id : alg_map o (trans eta alg_obj) = (@identity C alg_obj);
     alg_act: alg_map o (fmap T (alg_map)) = alg_map o (trans mu alg_obj)
  }.
Check TAlgebra.


Lemma eqTA: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (TA1 TA2: TAlgebra C T M)
                  (objEq  : (@alg_obj C T M TA1) = (@alg_obj C T M TA2)),
                  ((match objEq in _ = V return arrow V (fobj T V) with
                    | eq_refl => (@alg_map C T M TA1)
                   end) = (@alg_map C T M TA2)) -> TA1 = TA2.
Proof. intros.
       destruct TA1, TA2. cbn in *. subst.
       destruct (proof_irrelevance _ alg_id0 alg_id1).
       destruct (proof_irrelevance _ alg_act0 alg_act1).
       easy.
Qed.

(** eqTA with JMeq *)
Lemma eqTA2: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (TA1 TA2: TAlgebra C T M),
                  (@alg_obj C T M TA1) = (@alg_obj C T M TA2) ->
                  JMeq (@alg_map C T M TA1) (@alg_map C T M TA2) -> TA1 = TA2.
Proof. intros.
       destruct TA1, TA2. cbn in *. subst.
       apply JMeq_eq in H0. subst. f_equal. intros. subst.
       easy.
       now destruct (proof_irrelevance _ alg_id0 alg_id1).
       now destruct (proof_irrelevance _ alg_act0 alg_act1).
Qed.

Class TAlgebraMap (C      : Category)
                  (T      : (@Functor C C))
                  (M      : Monad C T)
                  (TA1 TA2: TAlgebra C T M) :=
  {
     tf  : @arrow C (@alg_obj C T M TA1) (@alg_obj C T M TA2);
     malg: (@alg_map C T M TA1) o fmap T tf = tf o (@alg_map C T M TA2)
  }.
Check TAlgebraMap.


Lemma eqTAM: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (TA1 TA2: TAlgebra C T M)
                  (ta1 ta2: TAlgebraMap C T M TA1 TA2)
                  (mapEq  : (@tf C T M TA1 TA2 ta1) = (@tf C T M TA1 TA2 ta2)),
                   ta1 = ta2.
Proof. intros. 
       destruct ta1, ta2, TA1, TA2, T, M. cbn in *.
       subst.
       destruct (proof_irrelevance _ malg0 malg1).
       easy.
Qed.

Definition EilenbergMooreCategory (C: Category) (T: Functor C C) (M: Monad C T): Category.
Proof. unshelve econstructor.
       - exact (TAlgebra C T M).
       - intros TA1 TA2.
         exact (TAlgebraMap C T M TA1 TA2).
       - intros.
         cbn in *.
         unshelve econstructor.
         + destruct a. cbn in *.
           exact (identity (alg_obj0)).
         + cbn in *. now rewrite !preserve_id, f_identity, identity_f.
       - intros.
         cbn in *.
         unshelve econstructor.
         + destruct a, b, c, X, X0. cbn in *.
           exact (tf0 o tf1).
         + cbn in *.
           rewrite preserve_comp.
           destruct T, M, eta0, mu0, a, b, c, X, X0. cbn in *.
           rewrite assoc.
           rewrite malg0. rewrite <- assoc. rewrite malg1.
           now rewrite assoc.
       - repeat intro. subst. easy.
       - cbn in *. intros.
         apply eqTAM. cbn in *. 
         now rewrite assoc.
       - cbn in *. intros.
         apply eqTAM. cbn.
         now rewrite identity_f.
      -  cbn in *. intros.
         apply eqTAM. cbn in *.
         now rewrite f_identity.
Defined.
Check EilenbergMooreCategory.
*)

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition TAlgebra (C: Category) (T: Functor C C) (M: Monad C T) (a: @obj C) :=
  { alg_map: arrow a (fobj T a) |
                alg_map o (trans eta a) = (@identity C a) /\ 
                alg_map o (fmap T (alg_map)) = alg_map o (trans mu a) }.


(** eqTA with JMeq *)
Lemma eqTA: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1 TA2: TAlgebra C T M a), 
                  JMeq (proj1_sig TA1) (proj1_sig TA2) -> TA1 = TA2.
Proof. intros.
       destruct TA1, TA2. cbn in *. subst. f_equal.
       intros. subst. easy.
       now destruct (proof_irrelevance _ a0 a1).
Qed.

Definition TAlgebraMap (C: Category) (T: Functor C C) 
                       (M: Monad C T) (a b: @obj C)
                       (TA1: TAlgebra C T M b) 
                       (TA2: TAlgebra C T M a) :=
  { tf  : @arrow C b a | (proj1_sig TA1) o fmap T tf = tf o (proj1_sig TA2) }.

Lemma eqTAM: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1    : TAlgebra C T M a)
                  (TA2    : TAlgebra C T M b)
                  (ta1 ta2: TAlgebraMap C T M b a TA1 TA2)
                  (mapEq  : (proj1_sig ta1) = (proj1_sig ta2)), ta1 = ta2.
Proof. intros. 
       destruct ta1, ta2, TA1, TA2, T, M. cbn in *.
       subst. f_equal.
       destruct (proof_irrelevance _ e e0).
       easy.
Qed.

Program Definition EilenbergMooreCategory (C: Category) (T: Functor C C) (M: Monad C T): Category.
Proof. unshelve econstructor.
       - exact { a: @obj C & TAlgebra C T M a}.
       - intros.
         exact (TAlgebraMap C T M (projT1 X0) (projT1 X) (projT2 X) (projT2 X0)).
       - intros. cbn. destruct a. cbn.
         unshelve econstructor.
         + exact (identity x).
         + now rewrite preserve_id, f_identity, identity_f.
       - cbn. intros. destruct a, b, c.
         unshelve econstructor.
         + destruct X, X0. cbn in *.
           exact (x2 o x3).
         + cbn. destruct X, X0.
           rewrite preserve_comp. cbn in *.
           rewrite assoc, e.
           now rewrite <- assoc, e0, assoc.
       - cbn. repeat intro. now subst.
       - cbn. intros. destruct a, b, c, d. cbn in *.
         apply eqTAM. cbn. destruct h,g,f. now rewrite assoc.
       - intros. destruct a, b. cbn in *.
         apply eqTAM. cbn. destruct f. now rewrite identity_f.
       - intros. destruct a, b. cbn in *.
         apply eqTAM. cbn. destruct f. now rewrite f_identity.
Defined. 

(*
Record TAlgebra (C: Category)
               (T: Functor C C)
               (M: Monad C T)
               (a: @obj C) :=
  {
     alg_map: arrow a (fobj T a);
     alg_id : alg_map o (trans eta a) = (@identity C a);
     alg_act: alg_map o (fmap T (alg_map)) = alg_map o (trans mu a)
  }.
Check TAlgebra.

(** eqTA with JMeq *)
Lemma eqTA: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1 TA2: TAlgebra C T M a),
                  JMeq (@alg_map C T M a TA1) (@alg_map C T M a TA2) -> TA1 = TA2.
Proof. intros.
       destruct TA1, TA2. cbn in *. subst. f_equal.
       intros. subst. easy.
       now destruct (proof_irrelevance _ alg_id0 alg_id1).
       now destruct (proof_irrelevance _ alg_act0 alg_act1).
Qed.

Record TAlgebraMap (C      : Category)
                  (T      : (@Functor C C))
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1    : TAlgebra C T M b) 
                  (TA2    : TAlgebra C T M a) :=
  {
     tf  : @arrow C b a;
     malg: (@alg_map C T M b TA1) o fmap T tf = tf o (@alg_map C T M a TA2)
  }.
Check TAlgebraMap.


Lemma eqTAM: forall
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1    : TAlgebra C T M a)
                  (TA2    : TAlgebra C T M b)
                  (ta1 ta2: TAlgebraMap C T M b a TA1 TA2)
                  (mapEq  : (@tf C T M b a TA1 TA2 ta1) = (@tf C T M b a TA1 TA2 ta2)),
                   ta1 = ta2.
Proof. intros. 
       destruct ta1, ta2, TA1, TA2, T, M. cbn in *.
       subst.
       destruct (proof_irrelevance _ malg0 malg1).
       easy.
Qed.

Check existT.

Program Definition EilenbergMooreCategory (C: Category) (T: Functor C C) (M: Monad C T): Category.
Proof. unshelve econstructor.
       - exact { a: @obj C & TAlgebra C T M a}.
       - intros.
         exact (TAlgebraMap C T M (projT1 X0) (projT1 X) (projT2 X) (projT2 X0)).
       - intros. cbn. destruct a.
         unshelve econstructor.
         + exact (identity x).
         + now rewrite preserve_id, f_identity, identity_f.
       - cbn. intros. destruct a, b, c.
         unshelve econstructor.
         + destruct X, X0.
           exact (tf0 o tf1).
         + cbn. destruct X, X0.
           rewrite preserve_comp. cbn in *.
           rewrite assoc, malg0.
           now rewrite <- assoc, malg1, assoc.
       - cbn. repeat intro. now subst.
       - cbn. intros. destruct a, b, c, d. cbn in *.
         apply eqTAM. cbn. now rewrite assoc.
       - intros. destruct a, b. cbn in *.
         apply eqTAM. cbn. now rewrite identity_f.
       - intros. destruct a, b. cbn in *.
         apply eqTAM. cbn. now rewrite f_identity.
Defined.
*)

Definition aFT {C: Category}
               (F  : Functor C C)
               (M  : Monad C F)
               (KC := (Kleisli_Category C F M)): Functor C KC.
Proof. destruct M as (eta, mu, cc1, cc2, cc3, cc4).
       unshelve econstructor.
       - exact id.
       - intros a b f. exact (trans eta b o f).
       - repeat intro. subst. easy.
       - intros. simpl in *. rewrite f_identity. easy.
       - intros. simpl in *. 
         rewrite !preserve_comp.
         do 3 rewrite assoc.
         rewrite cc3.
         rewrite identity_f.
         destruct eta. cbn in *.
         now rewrite comm_diag.
Defined.
Check aFT.

(** left adjoint functor that acts as F_T *)
Definition FT {C D: Category}
              (F  : Functor C D)
              (G  : Functor D C)
              (T  := Compose_Functors F G)
              (M  : Monad C T)
              (KC := (Kleisli_Category C T M)): Functor C KC.
Proof. exact (aFT T M). Defined.
(*
 destruct M as (eta, mu, cc1, cc2, cc3, cc4).
       unshelve econstructor.
       - exact id.
       - intros a b f. exact (trans eta b o f).
       - repeat intro. subst. easy.
       - intros. simpl in *. rewrite f_identity. easy.
       - intros. simpl in *. 
         rewrite !preserve_comp.
         do 3 rewrite assoc.
         rewrite cc3.
         rewrite identity_f.
         destruct eta. cbn in *.
         now rewrite comm_diag.
Defined.
*)
Check FT.

(** right adjoint functor that acts as G_T *)
Definition aGT {C  : Category}
               (F  : Functor C C)
               (M  : Monad C F)
               (KC := (Kleisli_Category C F M)): Functor KC C.
Proof. destruct M as (eta, mu, cc1, cc2, cc3, cc4).
       unshelve econstructor; simpl.
       - exact (fobj F).
       - intros a b f. exact (trans mu b o fmap F f).
       - repeat intro. subst. easy.
       - intros. clear KC.
         specialize (cc3 a). easy.
       - intros. unfold id in *.
         destruct mu. simpl in *.
         rewrite !preserve_comp.
         repeat rewrite assoc.
         apply rcancel.
         repeat rewrite assoc.
         rewrite !cc1.
         repeat rewrite <- assoc.
         now rewrite comm_diag.
Defined.
Check aGT.

(** right adjoint functor that acts as G_T *)
Definition GT  {C D: Category}
               (F  : Functor C D)
               (G  : Functor D C)
               (T  := Compose_Functors F G)
               (M  : Monad C T)
               (KC := (Kleisli_Category C T M)): Functor KC C.
Proof. exact (aGT T M). Defined.
(*
 destruct M as (eta, mu, cc1, cc2, cc3, cc4).
       unshelve econstructor; simpl.
       - exact (fobj T).
       - intros a b f. exact (trans mu b o fmap T f).
       - repeat intro. subst. easy.
       - intros. clear KC.
         specialize (cc3 a). easy.
       - intros. unfold id in *.
         destruct mu. simpl in *.
         rewrite !preserve_comp.
         repeat rewrite assoc.
         apply rcancel.
         repeat rewrite assoc.
         rewrite !cc1.
         repeat rewrite <- assoc.
         now rewrite comm_diag.
Defined.
*)
Check GT.

Definition LAEM {C D: Category}
                (F  : Functor C D)
                (G  : Functor D C)
                (T  := Compose_Functors F G)
                (M  : Monad C T)
                (EMC:= (EilenbergMooreCategory C T M)): Functor C EMC.
Proof. unshelve econstructor.
       - intro a. cbn in *.
         unshelve econstructor.
         + exact (fobj T a).
         + unshelve econstructor.
           ++ exact (trans (@mu _ _ M) a).
           ++ clear EMC.
              destruct M. cbn in *.
              now specialize (comm_diagram2_b4 a).
       - intros. cbn in *.
         unshelve econstructor.
         + exact (fmap T f).
         + destruct M. cbn in *.
           destruct eta0, mu0. cbn in *.
           now rewrite comm_diag0.
       - repeat intro. now subst.
       - intros. cbn in *.
         apply eqTAM. cbn.
         now rewrite !preserve_id.
       - intros. cbn in *.
         apply eqTAM. cbn.
         now rewrite !preserve_comp.
Defined.
Check LAEM.

(*
Definition LAEM {C D: Category}
                (F  : Functor C D)
                (G  : Functor D C)
                (T  := Compose_Functors F G)
                (M  : Monad C T)
                (EMC:= (EilenbergMooreCategory C T M)): Functor C EMC.
Proof. unshelve econstructor.
       - intro a. cbn in *.
         unshelve econstructor.
         + exact (fobj T a).
         + exact (trans (@mu _ _ M) a).
         + clear EMC.
           destruct M. cbn in *.
           now specialize (comm_diagram2_b4 a).
         + destruct M. cbn in *.
           now rewrite comm_diagram3.
       - intros. cbn in *.
         unshelve econstructor.
         + exact (fmap T f).
         + destruct M. cbn in *.
           destruct eta0, mu0. cbn in *.
           now rewrite comm_diag0.
       - repeat intro. now subst.
       - intros. cbn in *.
         apply eqTAM. cbn.
         now rewrite !preserve_id.
       - intros. cbn in *.
         apply eqTAM. cbn.
         now rewrite !preserve_comp.
Defined.
Check LAEM.
*)

(** right adjoint functor that acts as G_T *)
Definition RAEM {C D: Category}
                (F  : Functor C D)
                (G  : Functor D C)
                (T  := Compose_Functors F G)
                (M  : Monad C T)
                (EMC:= (EilenbergMooreCategory C T M)): Functor EMC C.
Proof. unshelve econstructor.
       - intros. cbn in *.
         destruct X. exact x.
       - intros. cbn in *.
         destruct a, b, f. cbn in *.
         exact x1.
       - repeat intro. now subst.
       - intros. destruct a. now cbn in *.
       - intros. cbn in *.
         destruct a, b, c, f, g. now cbn in *.
Defined.
Check RAEM.
(*
(** right adjoint functor that acts as G_T *)
Definition RAEM {C D: Category}
                (F  : Functor C D)
                (G  : Functor D C)
                (T  := Compose_Functors F G)
                (M  : Monad C T)
                (EMC:= (EilenbergMooreCategory C T M)): Functor EMC C.
Proof. unshelve econstructor.
       - intros. cbn in *.
         destruct X. exact alg_obj0.
       - intros. cbn in *.
         destruct a, b, f. cbn in *.
         exact tf0.
       - repeat intro. now subst.
       - intros. destruct a. now cbn in *.
       - intros. cbn in *.
         destruct a, b, c, f, g. now cbn in *.
Defined.
Check RAEM.
*)

Definition cLA {C D: Category}
               (F  : Functor C D)
               (G  : Functor D C)
               (cT := Compose_Functors G F)
               (cM : coMonad D cT)
               (cKC:= (coKleisli_Category D cT cM)): Functor cKC D.
Proof. destruct cM, eps0.
       unshelve econstructor.
       - simpl. exact (fobj cT).
       - intros. destruct delta0. simpl in *. unfold id in *.
         exact ((Functor.fmap cT f) o trans0 a).
       - repeat intro. subst. easy.
       - intros. destruct delta0. unfold id in *. simpl in *.
         now rewrite ccomm_diagram2_b4.
       - intros. simpl. destruct delta0. simpl in *. unfold id in *.
         destruct F, G. simpl in *.
         rewrite preserve_comp0, preserve_comp.
         repeat rewrite assoc.
         rewrite preserve_comp0, preserve_comp.
         rewrite <- assoc.
         rewrite ccomm_diagram3.
         repeat rewrite assoc. apply rcancel.
         do 2 rewrite <- assoc.
         now rewrite comm_diag0.
Defined.
Check cLA.

(** right adjoint functor that acts as G_D *)
Definition cRA {C D: Category}
               (F  : Functor C D)
               (G  : Functor D C)
               (cT := Compose_Functors G F)
               (cM : coMonad D cT)
               (cKC:= (coKleisli_Category D cT cM)): Functor D cKC.
Proof. destruct cM, eps0.
       unshelve econstructor.
       - exact id.
       - intros. unfold id. simpl. exact (f o trans a).
       - repeat intro. subst. easy.
       - intros. simpl in *. rewrite identity_f. easy.
       - intros. simpl in *. destruct delta0. unfold id in *.
         simpl in *. destruct F, G. simpl in *.
         rewrite preserve_comp0, preserve_comp.
         repeat rewrite <- assoc.
         rewrite ccomm_diagram4.
         repeat rewrite assoc, ccomm_diagram2_b3, f_identity.
         now rewrite <- comm_diag, assoc.
Defined.
Check cRA.

Definition EtaFs: forall (s: @obj CoqCatT), NaturalTransformation Id (Fs s).
Proof. intro s.
       unshelve econstructor.
       + cbn. intros a v.
         exact (fun st: s => (v, st)).
       + cbn. intros a b f.
         extensionality v. easy.
Defined.

Definition MuFs: forall (s: @obj CoqCatT),
  NaturalTransformation (Compose_Functors (Fs s) (Fs s)) (Fs s).
Proof. intro s.
       unshelve econstructor.
       + cbn. intros a H st.
         destruct H as (f & st').
         exact st. exact (f st').
       + cbn. intros a b f.
         extensionality g. compute.
         extensionality st.
         destruct g. easy.
Defined.

(** State monad *)
Definition Ms: forall (s: @obj CoqCatT), Monad CoqCatT (Fs s).
Proof. intro s.
       unshelve econstructor.
       - exact (EtaFs s).
       - exact (MuFs  s).
       - cbn. intro a.
         extensionality f. compute.
         extensionality st.
         destruct f. easy.
       - cbn. intro a.
         extensionality f. compute.
         extensionality st.
         destruct f. easy.
       - cbn. intro a.
         extensionality f. compute.
         extensionality st.
         destruct f. easy.
       - cbn. intro a.
         extensionality f. compute.
         extensionality st.
         destruct f. easy.
Defined.

Definition EtaFm: NaturalTransformation Id FunctorM.
Proof. unshelve econstructor.
       - intro A. cbn in *.
         intro a. exact (just A a).
       - intros A B f. cbn. easy.
Defined.

Definition fmapFM {A : Type} (i: maybe (maybe A)): maybe A :=
  match i with
    | just _ a => a
    | nothing _ => nothing _
  end.

Definition MuFm: NaturalTransformation (Compose_Functors FunctorM FunctorM) (FunctorM).
Proof. unshelve econstructor.
       - intro A. cbn.
         intro i. cbn in *.
         exact (fmapFM i).
       - intros A B f. cbv.
         extensionality a.
         case_eq a; intros.
         case_eq m; intros.
         easy. easy. easy.
Defined. 

(** Maybe monad *)
Definition Mm: Monad CoqCatT FunctorM.
Proof. unshelve econstructor.
       - exact EtaFm.
       - exact MuFm.
       - cbn. intro a. cbv.
         extensionality b.
         case_eq b; intros; try easy.
       - intro a. cbv.
         extensionality b.
         case_eq b; intros; try easy.
       - intro a. cbv.
         extensionality b.
         case_eq b; intros; try easy.
       - intro a. cbv.
         extensionality b.
         case_eq b; intros; try easy.
Defined.


