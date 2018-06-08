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


(** Equivalence of Functors, inspired by Amin Timany *)
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

Notation " C → D " := (Functor C D) (at level 40, left associativity).


Definition BiHomFunctorC {C D: Category} (F: D → C) (G: C → D): (D^op) × C → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow C y (fobj F x)).
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

Definition BiHomFunctorD {C D: Category} (F: D → C) (G: C → D): D^op × C → CoqCatT.
Proof. unshelve econstructor.
       - intros. cbn in *. destruct X as (x, y).
         exact (@arrow D (fobj G y) x).
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

