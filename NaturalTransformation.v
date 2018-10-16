Require Import ECat.Imports.
Require Import ECat.Category.
Require Import ECat.Functor.

Arguments Compose_Functors {_} {_} {_} _ _.
Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.

Class NaturalTransformation (C D: Category) 
                            (F  : Functor C D)
                            (G  : Functor C D): Type :=
  mk_nt
  {
    trans    : forall (a: @obj C), (@arrow D (fobj G a) (fobj F a));
    comm_diag: forall {a b: @obj C} (f: arrow  b a), fmap G f o trans a  = trans b o fmap F f;
  }.

Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.

(** sameness of natural transformations *)
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

(** the identity natural transformation *)
Definition IdNt (C D: Category) 
                (F  : Functor C D): NaturalTransformation F F.
Proof. unshelve econstructor.
       - intros. exact (fmap _(@identity C a)).
       - intros. destruct F. simpl. rewrite !preserve_id.
         now rewrite identity_f, f_identity.
Defined.

(** composing natural transformations *)
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

(** the category of all functors defined from the same source to 
the same target category *)
Definition FunctorCategory (C D: Category): Category.
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

(** some basic natural transformation examples from CIC *)

(** natural transformations to form an adjunction between
conjunction and implication of Prop universe *)
Definition eta_GpFp: forall (p: @obj CoqCatP),
  NaturalTransformation IdFunctor (Compose_Functors (Fp p) (Gp p)).
Proof. intro p.
       unshelve econstructor.
       - cbn in *. 
         unfold fobjFp, fobjGp. intro q.
         exact (fun (pq: id q) (pp: p) => conj pp pq).
       - cbn. intros a b f.
         extensionality pa. easy.
Defined.

Definition eps_FpGp: forall (p: @obj CoqCatP),
  NaturalTransformation (Compose_Functors (Gp p) (Fp p)) IdFunctor.
Proof. intro p.
       unshelve econstructor.
       - cbn in *.
         unfold fobjFp, fobjGp. intro q.
         exact (fun (H: p /\ (p -> q)) => match H with conj pp ppiq => ppiq pp end).
       - cbn. intros a b f.
         extensionality pp. 
         destruct pp. easy.
Defined.

(** natural transformations to from state monad *)
Definition EtaFs: forall (s: @obj CoqCatT), NaturalTransformation IdFunctor (Fs s).
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

(** natural transformations to from maybe monad *)
Definition EtaFm: NaturalTransformation IdFunctor FunctorM.
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

