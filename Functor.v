Require Export Category.

Class Functor (C D: Category): Type :=
  mk_Functor
  {
    fobj            : @obj C -> @obj D;
    fmap            : forall {a b: @obj C} (f: arrow b a), (arrow (fobj b) (fobj a));
    fmapP           : forall x y, Proper (eq ==> eq) (@fmap x y);
    preserve_id     : forall {a: @obj C}, fmap (@identity C a) = (@identity D (fobj a));
    preserve_comp   : forall {a b c: @obj C} (g : @arrow C c b) (f: @arrow C b a),
                      fmap (g o f) = (fmap g) o (fmap f)
  }.

Notation " C → D " := (Functor C D) (at level 40, left associativity).

Arguments fmap {_} {_} _ _ _ _.
Arguments fobj {_} {_} _ _.

(** sameness of Functors using heterogenous (John Major's) equality *)
Lemma F_split: forall (C D: Category) (F G: Functor C D),
                 fobj F = fobj G -> JMeq (fmap F) (fmap G) -> F = G.
Proof.
    destruct F; destruct G; cbn; intros; subst; apply JMeq_eq in H0; subst; f_equal.
    now destruct (proof_irrelevance _ fmapP0 fmapP1).
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.

(** Compsing functors *)
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

(** Associativity of functor composition *)
Lemma FunctorCompositionAssoc: forall {D C B A : Category} 
  (F : Functor C D) (G : Functor B C) (H : Functor A B),
  Compose_Functors H (Compose_Functors G F) = Compose_Functors (Compose_Functors H G) F.
Proof. intros.
       apply F_split.
       - easy.
       - apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
         eq_existT_uncurried; cbn.
         now exists (eq_refl 
         (forall a b : obj, arrow b a ->
           arrow (fobj F (fobj G (fobj H b))) (fobj F (fobj G (fobj H a))))).
Defined.

(** the identity functor *)
Definition IdFunctor {C: Category}: Functor C C.
Proof. unshelve econstructor.
       - exact id.
       - unfold id. intros. exact f.
       - repeat intro. easy.
       - intros. now destruct C.
       - intros. now destruct C.
Defined.

(** Identity functors cancels on the right *)
Lemma ComposeIdr: forall {C D: Category} (F: Functor C D),
  Compose_Functors F IdFunctor = F.
Proof. intros.
       apply F_split.
       - easy.
       - apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
         eq_existT_uncurried; cbn.
       unfold id in *.
       now exists (eq_refl 
       (forall a b : obj, arrow b a -> arrow (fobj F b) (fobj F a))).
Defined.

(** Identity functors cancels on the left *)
Lemma ComposeIdl: forall {C D: Category} (F: Functor C D),
  Compose_Functors IdFunctor F = F.
Proof. intros.
       apply F_split.
       - easy.
       - apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
         eq_existT_uncurried; cbn.
       unfold id in *.
       now exists (eq_refl 
       (forall a b : obj, arrow b a -> arrow (fobj F b) (fobj F a))).
Defined.

(** the 2-category Cat *)
Definition Cat: Category.
Proof. unshelve econstructor.
       - exact Category.
       - intros C D. exact (Functor C D).
       - intro C. exact (@IdFunctor C).
       - intros E D C F G. exact (Compose_Functors F G).
       - repeat intro. now subst.
       - intros D C B A F G H. 
         exact (FunctorCompositionAssoc F G H).
       - intros D C F. exact (ComposeIdl F).
       - intros D C F. exact (ComposeIdr F).
Defined.

(** the full-image category of a functor *)
Definition FullImageCategory {C D: Category} (F: Functor C D) 
 (is_inD : forall {a b: @obj C}, @arrow D (fobj F b) (fobj F a) -> Prop)
 (id_in  : forall a, is_inD (fmap F a a (identity a)))
 (comp_in: forall {a b c} (f: arrow b a) (g: arrow c b),
           is_inD (fmap F _ _ f) -> is_inD (fmap F _ _ g) -> is_inD (fmap F _ _ (g o f))): Category.
Proof. unshelve econstructor.
       - exact (@obj C).
       - intros a b. exact { f: @arrow C b a | is_inD a b (fmap F a b f) }.
       - intros. exists (identity a). exact (id_in a).
       - intros a b c g f.
         destruct f as (f & Hf).
         destruct g as (g & Hg).
         exists (f o g).
         now apply comp_in.
       - repeat intro. now subst.
       - intros. cbn in *.
         destruct f as (f & Hf).
         destruct g as (g & Hg).
         destruct h as (h & Hh).
         apply subset_eq_compat.
         now rewrite assoc.
       - intros a b f.
         destruct f as (f & Hf).
         apply subset_eq_compat.
         now rewrite f_identity.
       - intros a b f.
         destruct f as (f & Hf).
         apply subset_eq_compat.
         now rewrite identity_f.
Defined.

(** Some basic functor examples from CIC *)

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
Definition fobjFp := fun p => fun q => p /\ q.

Definition fmapFp:=
  fun p =>
  fun (a b: Prop) (f: a -> b) (H: p /\ a) =>
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

