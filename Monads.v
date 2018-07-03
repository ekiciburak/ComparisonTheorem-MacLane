Require Export NaturalTransformation.

Arguments fmap {_} {_} _ _ _ _.
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
                        (trans mu a) o (fmap T (fobj T (fobj T a)) (fobj T a) ((trans mu a))) = 
                        (trans mu a) o (trans mu (fobj T a));
    comm_diagram2   : forall (a: @obj C), 
                        (trans mu a) o (fmap T (id a) (fobj T a) (trans eta a)) = 
                        (trans mu a) o (trans eta (fobj T a));
    comm_diagram2_b1: forall (a: @obj C), 
                        (trans mu a) o (fmap T (id a) (fobj T a) (trans eta a)) = 
                        (identity (fobj T a));
    comm_diagram2_b2: forall (a: @obj C), (trans mu a) o (trans eta (fobj T a)) =
                        (identity (fobj T a))
  }.
Check Monad.


Class coMonad (C: Category) 
              (D: Functor C C): Type :=
  mk_coMonad
  {
    eps    : NaturalTransformation D Id;
    delta  : NaturalTransformation D (Compose_Functors D D);
    ccomm_diagram1   : forall (a: @obj C),
                       (fmap D  (fobj D a) (fobj D (fobj D a)) (trans delta a)) o (trans delta a) = 
                       (trans delta (fobj D a)) o (trans delta a);
    ccomm_diagram2   : forall (a: @obj C),
                       (fmap D (fobj D a) (id a) (trans eps a)) o (trans delta a) =
                       (trans eps (fobj D a)) o (trans delta a);
    ccomm_diagram2_b1: forall (a: @obj C),
                       (trans eps (fobj D a)) o (trans delta a) =
                       (identity (fobj D a));
    ccomm_diagram2_b2: forall (a: @obj C),
                       (fmap D (fobj D a) (id a) (trans eps a)) o (trans delta a) =
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
         exact ((@trans0 c) o (fmap T _ _  g) o f).
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
         exact (g o (fmap D _ _  f) o (trans0 a)).
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

Class TAlgebra (C: Category)
               (T: Functor C C)
               (M: Monad C T) :=
  {
     alg_obj: @obj C;
     alg_map: arrow alg_obj (fobj T alg_obj);
     alg_id : alg_map o (trans eta alg_obj) = (@identity C alg_obj);
     alg_act: alg_map o (fmap T (fobj T alg_obj) alg_obj (alg_map)) = alg_map o (trans mu alg_obj)
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

Class TAlgebraMap (C      : Category)
                  (T      : (@Functor C C))
                  (M      : Monad C T)
                  (TA1 TA2: TAlgebra C T M) :=
  {
     tf  : @arrow C (@alg_obj C T M TA1) (@alg_obj C T M TA2);
     malg: (@alg_map C T M TA1) o fmap T _ _  tf = tf o (@alg_map C T M TA2)
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
         destruct T, M, eta0, mu0,a, b, c, d, f, g, h. cbn in *.
         apply eqTAM. cbn in *. 
         now rewrite assoc.
       - cbn in *. intros.
         apply eqTAM. cbn.
         destruct a, b, f. cbn in *.
         now rewrite identity_f.
      -  cbn in *. intros.
         apply eqTAM. cbn in *.
         now rewrite f_identity.
Defined.
Check EilenbergMooreCategory.

(** A monad gives raise to a Kleisli Adjunction *)

(** left adjoint functor that acts as F_T *)
Definition LA {C D: Category}
              (F  : Functor C D)
              (G  : Functor D C)
              (T  := Compose_Functors F G)
              (M  : Monad C T)
              (KC := (Kleisli_Category C T M)): Functor C KC.
Proof. destruct M, T, eta0.
       unshelve econstructor; simpl.
       - exact id.
       - intros a b f. exact (trans b o f).
       - repeat intro. subst. easy.
       - intros. simpl in *. rewrite f_identity. easy.
       - intros. simpl in *. destruct mu0. unfold id in *. simpl in *.
         rewrite preserve_comp. do 2 rewrite assoc.
         rewrite assoc. rewrite comm_diagram2_b3.
         rewrite <- comm_diag. now rewrite identity_f.
Defined.
Check LA.

(** right adjoint functor that acts as G_T *)
Definition RA {C D: Category}
              (F  : Functor C D)
              (G  : Functor D C)
              (T  := Compose_Functors F G)
              (M  : Monad C T)
              (KC := (Kleisli_Category C T M)): Functor KC C.
Proof. destruct M, mu0.
       unshelve econstructor; simpl.
       - exact (fobj T).
       - intros a b f. exact (trans b o fmap T _ _ f).
       - repeat intro. subst. easy.
       - intros. clear KC.
         specialize (comm_diagram2_b3 a). easy.
       - intros. unfold id in *.
         destruct F, G. simpl in *.
         rewrite preserve_comp, preserve_comp0.
         repeat rewrite assoc.
         apply rcancel.
         rewrite preserve_comp, preserve_comp0.
         repeat rewrite assoc.
         rewrite comm_diagram3.
         repeat rewrite <- assoc.
         now rewrite comm_diag.
Defined.
Check RA.

Definition LAEM {C D: Category}
                (F  : Functor C D)
                (G  : Functor D C)
                (T  := Compose_Functors F G)
                (M  : Monad C T)
                (EMC:= (EilenbergMooreCategory C T M)): Functor C EMC.
Proof. destruct M, T, eta0, mu0. cbn in *.
       unshelve econstructor.
       - intros. cbn in *.
         unshelve econstructor.
         + exact (fobj X).
         + cbn in *. exact (trans0 X).
         + cbn in *. clear EMC.
           now specialize (comm_diagram2_b4 X).
         + cbn in *.
           now rewrite comm_diagram3.
       - intros. cbn in *.
         unshelve econstructor.
         + cbn in *. exact (fmap _ _ f).
         + cbn in *.
           now rewrite comm_diag0.
       - repeat intro. now subst.
       - intros. cbn in *.
         apply eqTAM. cbn.
         now rewrite preserve_id.
       - intros. cbn in *.
         apply eqTAM. cbn.
         now rewrite preserve_comp.
Defined.
Check LAEM.

(** right adjoint functor that acts as G_T *)
Definition RAEM {C D: Category}
                (F  : Functor C D)
                (G  : Functor D C)
                (T  := Compose_Functors F G)
                (M  : Monad C T)
                (EMC:= (EilenbergMooreCategory C T M)): Functor EMC C.
Proof. destruct M, T, eta0, mu0. cbn in *.
       unshelve econstructor.
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
         exact ((Functor.fmap cT _ _ f) o trans0 a).
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

