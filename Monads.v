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

    eta : NaturalTransformation IdFunctor T;
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

(** comonads *)
Class coMonad (C: Category) 
              (D: Functor C C): Type :=
  mk_coMonad
  {
    eps    : NaturalTransformation D IdFunctor;
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

(** the Kleisli category of a monad *)
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
         unfold IdFunctor, id in *. simpl in *.
         rewrite preserve_comp.
         rewrite assoc. rewrite preserve_comp. 
         rewrite assoc. do 2 rewrite assoc. rewrite (comm_diagram3 d).
         specialize(@comm_diag0 c (fobj d) h).
         apply rcancel. apply rcancel.
         rewrite <- assoc. rewrite <- assoc.
         rewrite comm_diag0.
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

(** the coKleisli category of a comonad *)
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
         unfold IdFunctor, id in *. simpl in *.
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


(** left adjoint functor that acts as F_T *)
Definition FT {C  : Category}
              (T  : Functor C C)
              (M  : Monad C T)
              (KC := Kleisli_Category C T M): Functor C KC.
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
Check FT.

(** right adjoint functor that acts as G_T *)
Definition GT  {C  : Category}
               (T  : Functor C C)
               (M  : Monad C T)
               (KC := Kleisli_Category C T M): Functor KC C.
Proof. destruct M as (eta, mu, cc1, cc2, cc3, cc4).
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
Check GT.

(** right adjoint functor that acts as F_D *)
Definition FD {C  : Category}
              (cT : Functor C C)
              (cM : coMonad C cT)
              (cKC:= coKleisli_Category C cT cM): Functor cKC C.
Proof. destruct cM, eps0.
        unshelve econstructor.
        - simpl. exact (fobj cT).
        - intros. destruct delta0. simpl in *. unfold id in *.
          exact ((Functor.fmap cT f) o trans0 a).
        - repeat intro. subst. easy.
        - intros. destruct delta0. unfold id in *. simpl in *.
          now rewrite ccomm_diagram2_b4.
        - intros. simpl. destruct delta0. simpl in *. unfold id in *.
          destruct cT. simpl in *.
          rewrite preserve_comp.
          repeat rewrite assoc.
          rewrite preserve_comp.
          rewrite <- assoc.
          rewrite ccomm_diagram3.
          repeat rewrite assoc. apply rcancel.
          do 2 rewrite <- assoc.
          now rewrite comm_diag0.
Defined.
Check FD.

(** left adjoint functor that acts as G_D *)
Definition GD {C  : Category}
              (cT : Functor C C)
              (cM : coMonad C cT)
              (cKC:= coKleisli_Category C cT cM): Functor C cKC.
Proof. destruct cM, eps0.
        unshelve econstructor.
        - exact id.
        - intros. unfold id. simpl. exact (f o trans a).
        - repeat intro. subst. easy.
        - intros. simpl in *. rewrite identity_f. easy.
        - intros. simpl in *. destruct delta0. unfold id in *.
          simpl in *. destruct cT. simpl in *.
          rewrite preserve_comp.
          repeat rewrite <- assoc.
          rewrite ccomm_diagram4.
          repeat rewrite assoc, ccomm_diagram2_b3, f_identity.
          now rewrite <- comm_diag, assoc.
Defined.
Check GD.

(** some basic monad examples from CIC *)

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
