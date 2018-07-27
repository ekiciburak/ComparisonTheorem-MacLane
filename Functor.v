Require Export Iso.

Class Functor `(C: Category) `(D: Category) : Type :=
  mk_Functor
  {
    fobj            : @obj C -> @obj D;
    fmap            : forall {a b: @obj C} (f: arrow b a), (arrow (fobj b) (fobj a));
    fmapP           : forall x y, Proper (eq ==> eq) (@fmap x y);
    preserve_id     : forall {a: @obj C}, fmap (@identity C a) = (@identity D (fobj a));
    preserve_comp   : forall {a b c: @obj C} (g : @arrow C c b) (f: @arrow C b a), 
                             (* fMap a c (g o f) *) fmap (g o f) = (fmap g) o (fmap f)
  }.
Check Functor.


Arguments fmap {_} {_} _ _ _ _.
Arguments fobj {_} {_} _ _.

Definition Compose_Functors (C D E: Category) 
                            (F    : Functor C D) 
                            (G    : Functor D E): (Functor C E).
Proof. unshelve econstructor.
       - exact (fun a => fobj G (fobj F a)).
       - intros. exact ((((@fmap D E G _ _
                               (@fmap C D F a b f))))).
       - repeat intro. subst. easy.
       - intros. destruct F, G. simpl in *.
         now rewrite <- preserve_id1, preserve_id0.
       - intros. destruct F, G. simpl in *.
         now rewrite <- preserve_comp1, preserve_comp0.
Defined.

Arguments Compose_Functors {_} {_} {_} _ _.

Definition IdFunctor {C: Category}: Functor C C.
Proof. unshelve econstructor.
       - exact id.
       - unfold id. intros. exact f.
       - repeat intro. easy.
       - intros. now destruct C.
       - intros. now destruct C.
Defined.

Definition Id {C: Category}: @Functor C C.
Proof. refine (@mk_Functor C C id (fun a b f => f) _ _ _);
       intros; now unfold id.
Defined.

(** sameness of Functors, inspired by Amin Timany *)
Lemma F_split: forall
               (C D  : Category)
               (F G  : Functor C D)
               (ObjEq: (fobj F) = (fobj G)),
               ((fun a b => 
                   match ObjEq in _ = V return ((arrow b a) -> (arrow (V b) (V a))) with
                    | eq_refl => (fmap F a b)
                   end) = fmap G) -> F = G.
Proof.
    destruct F; destruct G; simpl; intros; subst; f_equal.
    now destruct (proof_irrelevance _ fmapP0 fmapP1).
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.

(** F_split with JMeq *)
Lemma F_split2: forall
               (C D  : Category)
               (F G  : Functor C D)
               (ObjEq: (fobj F) = (fobj G)),
               JMeq (fmap F) (fmap G) -> F = G.
Proof.
    destruct F; destruct G; simpl; intros; subst; apply JMeq_eq in H; subst; f_equal.
    now destruct (proof_irrelevance _ fmapP0 fmapP1).
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.

Lemma FunctorCompositionAssoc: forall {D C B A : Category} 
  (F : Functor C D) (G : Functor B C) (H : Functor A B),
  Compose_Functors H (Compose_Functors G F) = Compose_Functors (Compose_Functors H G) F.
Proof. intros.
       assert (fobj (Compose_Functors H (Compose_Functors G F)) = fobj (Compose_Functors (Compose_Functors H G) F)).
       { cbn. easy. }
       specialize (F_split2 _ _ _ _ H0); intros.
       apply H1. cbn. easy.
Defined.

Lemma ComposeIdr: forall {C D: Category} (F: Functor C D),
  Compose_Functors F IdFunctor = F.
Proof. intros.
       assert (fobj (Compose_Functors F IdFunctor) = fobj F).
       { cbn. easy. }
       specialize (F_split _ _ _ _ H); intros.
       apply H0. cbn.
       extensionality a. extensionality b.
       clear H0. cbn in H. unfold id in *.
       assert (H = eq_refl).
       { specialize (UIP_refl _   (fun a : @obj C => fobj F a)); intros.
         now specialize (H0 H).
       } now subst.
Defined.


Lemma ComposeIdl: forall {C D: Category} (F: Functor C D),
  Compose_Functors IdFunctor F = F.
Proof. intros.
       assert (fobj (Compose_Functors IdFunctor F) = fobj F).
       { cbn. easy. }
       specialize (F_split _ _ _ _ H); intros.
       apply H0. cbn.
       extensionality a. extensionality b.
       clear H0. cbn in H. unfold id in *.
       assert (H = eq_refl).
       { specialize (UIP_refl _   (fun a : @obj C => fobj F a)); intros.
         now specialize (H0 H).
       } now subst.
Defined.

Notation " C → D " := (Functor C D) (at level 40, left associativity).


Definition BiHomFunctorC {C D: Category} (G: D → C): C^op × D → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow C (fobj G y) x).
       - intros. cbn in *.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct f as (f1, f2).
         cbn in *. intro g.
         exact ((fmap G _ _ f2) o g o f1).
       - repeat intro. now subst.
       - intros. destruct a as (a1, a2).
         cbn. extensionality f.
         now rewrite f_identity, preserve_id, identity_f.
       - intros.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct c as (c1, c2).
         cbn in *.
         destruct f as (f1, f2).
         destruct g as (g1, g2).
         cbn. extensionality h.
         rewrite preserve_comp.
         now repeat rewrite assoc.
Defined.

Definition BiHomFunctorC_GL {C D E: Category} (G: D → C) (L: E → D): C^op × E → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow C (fobj G (fobj L y)) x).
       - intros. cbn in *.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct f as (f1, f2).
         cbn in *. intro g.
         exact ((fmap G _ _ (fmap L _ _ f2)) o g o f1).
       - repeat intro. now subst.
       - intros. destruct a as (a1, a2).
         cbn. extensionality f.
         now rewrite !preserve_id, f_identity, identity_f.
       - intros.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct c as (c1, c2).
         cbn in *.
         destruct f as (f1, f2).
         destruct g as (g1, g2).
         cbn. extensionality h.
         rewrite !preserve_comp.
         now repeat rewrite assoc.
Defined.

Definition BiHomFunctorD {C D: Category} (F: C → D): (C^op) × D → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow D y (fobj F x)).
       - intros. cbn in *.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct f as (f1, f2).
         cbn in *. intro g.
         exact (f2 o g o (fmap F _ _ f1)).
       - repeat intro. now subst.
       - intros. destruct a as (a1, a2).
         cbn. extensionality f.
         now rewrite identity_f, preserve_id, f_identity.
       - intros.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct c as (c1, c2).
         cbn in *.
         destruct f as (f1, f2).
         destruct g as (g1, g2).
         cbn. extensionality h.
         rewrite preserve_comp.
         now repeat rewrite assoc.
Defined.

Definition BiHomFunctorD_LF_L {C D E: Category} (F: C → D) (L: D → E): (C^op) × D → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow E (fobj L y) (fobj L (fobj F x))).
       - intros. cbn in *.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct f as (f1, f2).
         cbn in *. intro g.
         exact ((fmap L _ _ f2) o g o (fmap L _ _ (fmap F _ _ f1))).
       - repeat intro. now subst.
       - intros. destruct a as (a1, a2).
         cbn. extensionality f.
         now rewrite !preserve_id, identity_f, f_identity.
       - intros.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct c as (c1, c2).
         cbn in *.
         destruct f as (f1, f2).
         destruct g as (g1, g2).
         cbn. extensionality h.
         rewrite !preserve_comp.
         now repeat rewrite assoc.
Defined.

Definition BiHomFunctorD_F_L {C D E: Category} (F: C → D) (L: E → D): (C^op) × E → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow D (fobj L y) (fobj F x)).
       - intros. cbn in *.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct f as (f1, f2).
         cbn in *. intro g.
         exact ((fmap L _ _ f2) o g o (fmap F _ _ f1)).
       - repeat intro. now subst.
       - intros. destruct a as (a1, a2).
         cbn. extensionality f.
         now rewrite !preserve_id, identity_f, f_identity.
       - intros.
         destruct a as (a1, a2).
         destruct b as (b1, b2).
         destruct c as (c1, c2).
         cbn in *.
         destruct f as (f1, f2).
         destruct g as (g1, g2).
         cbn. extensionality h.
         rewrite !preserve_comp.
         now repeat rewrite assoc.
Defined.


(** Some examples *)

(** List functor *)
Fixpoint fmapList {A B: Type} (f: A -> B) (l: list A): list B :=
  match l with
    | nil       => nil
    | cons x xs => cons (f x) (fmapList f xs)
  end.

Definition ListFunctor: Functor CoqCatT CoqCatT.
Proof. unshelve econstructor.
       - intros. exact (list X).
       - intros. cbn in *. intro l.
         exact (@fmapList a b f l).
       - repeat intro. now subst.
       - intros. cbn in *. unfold id.
         extensionality l.
         induction l as [ | xl IHxl ]; intros.
         + now cbn.
         + cbn in *. now rewrite IHIHxl.
       - intros. cbn in *. 
         extensionality l.
         induction l as [ | xl IHxl ]; intros.
         + now cbn.
         + cbn in *. now rewrite IHIHxl.
Defined.

(** Maybe functor *)
Inductive maybe (A: Type) :=
  | just   : A -> maybe A
  | nothing: maybe A.


Definition fmapMaybe {A B: Type} (f: A -> B) (i: maybe A): maybe B:=
  match i with
    | just _ a  => just _ (f a)
    | nothing _ => nothing _
  end.

Definition FunctorM: Functor CoqCatT CoqCatT.
Proof. unshelve econstructor.
       - cbn. intro a. exact (maybe a).
       - intros a b f. cbn. intro g.
         cbn in *.
         exact (fmapMaybe f g).
       - repeat intro. now subst.
       - intros. cbn in *.
         extensionality b. compute.
         case_eq b; intros; easy.
       - cbn. intros.
         extensionality h. cbv in *.
         case_eq h; intros; easy.
Defined.

(** State functor. *)

Definition fobjFs (s a : Type) := s -> (a * s).

Definition fmapFs (s A B: Type) (f: A -> B) (x : fobjFs s A) :=
  fun st =>
    match x st with
      | (a, st') => (f a, st')
    end.

Definition Fs: forall (s: @obj CoqCatT), Functor CoqCatT CoqCatT.
Proof. intro s.
       unshelve econstructor.
       - intros a. exact (fobjFs s a).
       - intros a b f. exact (fmapFs s a b f).
       - repeat intro. now subst.
       - intros. cbn in *.
         extensionality X. compute.
         extensionality st. now destruct X.
       - intros. cbn in *.
         extensionality X. compute.
         extensionality st. now destruct X.
Defined.

(** Two adjoint functors Fp and Gp over Prop forming an adjunction *)

Definition fobjFp (p q: Prop) := p /\ q.

Definition fmapFp (p a b : Prop) (f: a -> b) (H: p /\ a): p /\ b :=
  match H with
    | conj x y => conj x (f y)
  end.

Definition Fp: forall (p: @obj CoqCatP), Functor CoqCatP CoqCatP.
Proof. unshelve econstructor.
       - intro q. exact (fobjFp p q).
       - intros a b f. exact (fmapFp p a b f).
       - repeat intro. now subst.
       - intros. cbn in *. extensionality H. destruct H. easy.
       - intros. cbn in *. extensionality H. destruct H. easy.
Defined.

Definition fobjGp (p q: Prop) := p -> q.

Definition fmapGp (p a b : Prop) (f: a -> b) (H: p -> a): p -> b :=
  fun x: p => f (H x).

Definition Gp: forall (p: @obj CoqCatP), Functor CoqCatP CoqCatP.
Proof. unshelve econstructor.
       - intro q. exact (fobjGp p q).
       - intros a b f. exact (fmapGp p a b f).
       - repeat intro. now subst.
       - intros. cbn in *. extensionality H. easy.
       - intros. cbn in *. extensionality H. easy.
Defined.
