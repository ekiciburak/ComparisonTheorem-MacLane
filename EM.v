
Global Set Primitive Projections.

Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import JMeq.

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Polymorphic Cumulative Class Category: Type :=
 mk_Category 
 {
     obj       : Type;
     arrow     : obj -> obj -> Type;
     identity  : ∏ a, arrow a a;
     comp      : ∏ {a b c}, (arrow b c) -> (arrow a b) -> (arrow a c);
     assoc     : ∏ {a b c d} (h : arrow c d) (g : arrow b c) (f : arrow a b), 
                              comp h (comp g f) = comp (comp h g) f;
     identity_f: ∏ {a b} (f: arrow a b), comp (@identity b) f = f;
     f_identity: ∏ {a b} (f: arrow a b), comp f (@identity a) = f 
  }.

Notation " g 'o' f " := (@comp _ _ _ _ g f) (at level 40, left associativity).

Class Functor (C D: Category): Type :=
  mk_Functor
  {
    fobj            : @obj C -> @obj D;
    fmap            : ∏ {a b: @obj C} (f: arrow a b), arrow (fobj a) (fobj b);
    preserve_id     : ∏ {a: @obj C}, fmap (@identity C a) = (@identity D (fobj a));
    preserve_comp   : ∏ {a b c: @obj C} (g : @arrow C b c) (f: @arrow C a b),
                        fmap (g o f) = (fmap g) o (fmap f)
  }.


Arguments fmap {_} {_} _ _ _ _.
Arguments fobj {_} {_} _ _.

(** F_split with JMeq *)
Lemma F_split: ∏ (C D  : Category) (F G  : Functor C D), fobj F = fobj G -> JMeq (fmap F) (fmap G) -> F = G.
Proof.
    destruct F; destruct G; cbn; intros; subst; apply JMeq_eq in H0; subst; f_equal.
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.

(** sameness of Functors, inspired by Amin Timany *)
Lemma F_split2: ∏
               (C D  : Category)
               (F G  : Functor C D)
               (ObjEq: (fobj F) = (fobj G)),
               ((fun a b => 
                   match ObjEq in _ = V return ((arrow a b) -> (arrow (V a) (V b))) with
                    | eq_refl => (fmap F a b)
                   end) = fmap G) -> F = G.
Proof.
    destruct F; destruct G; simpl; intros; subst; f_equal.
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.


Definition IdF (C: Category): @Functor C C.
Proof. refine (@mk_Functor C C id (fun a b f => f) _ _);
       intros; now unfold id.
Defined.

Definition Compose_Functors {C D E: Category} 
                            (F    : Functor C D) 
                            (G    : Functor D E): (Functor C E).
Proof. unshelve econstructor.
       - exact (fun a => fobj G (fobj F a)).
       - intros. exact ((((@fmap D E G _ _
                               (@fmap C D F a b f))))).
       - intros. cbn.
         now rewrite !preserve_id.
       - intros. cbn.
         now rewrite !preserve_comp.
Defined.

Arguments Compose_Functors {_} {_} {_} _ _.

Lemma FunctorCompositionAssoc: forall {D C B A : Category} 
  (F : Functor C D) (G : Functor B C) (H : Functor A B),
  Compose_Functors H (Compose_Functors G F) = Compose_Functors (Compose_Functors H G) F.
Proof. intros.
       assert (fobj (Compose_Functors H (Compose_Functors G F)) = 
               fobj (Compose_Functors (Compose_Functors H G) F)).
       { cbn. easy. }
       specialize (F_split _ _ _ _ H0); intros.
       apply H1. cbn. easy.
Defined.

Lemma ComposeIdr: forall {C D: Category} (F: Functor C D),
  Compose_Functors F (IdF D) = F.
Proof. intros.
       assert (fobj (Compose_Functors F (IdF D)) = fobj F).
       { cbn. easy. }
       specialize (F_split _ _ _ _ H); intros.
       apply H0. cbn. easy.
Defined.


Lemma ComposeIdl: forall {C D: Category} (F: Functor C D),
  Compose_Functors (IdF C) F = F.
Proof. intros.
       assert (fobj (Compose_Functors (IdF C) F) = fobj F).
       { cbn. easy. }
       specialize (F_split _ _ _ _ H); intros.
       apply H0. cbn. easy.
Defined.

Arguments Compose_Functors {_} {_} {_} _ _.
Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.

Definition Cat: Category.
Proof. unshelve econstructor.
       - exact Category.
       - intros C D. exact (Functor C D).
       - intro C. exact (@IdF C).
       - intros A B C G F. cbn in *. exact (Compose_Functors F G).
       - intros A B C D H G F. cbn in *.
         exact (symmetry (@FunctorCompositionAssoc _ _ _ _  H G F)).
       - intros D C F. exact (ComposeIdl F).
       - intros D C F. exact (ComposeIdr F).
Defined.

Class NaturalTransformation {C D: Category} (F: Functor C D) (G: Functor C D): Type :=
  mk_NT
  {
    trans    : ∏ (a: @obj C), (@arrow D (fobj F a) (fobj G a));
    comm_diag: ∏ {a b: @obj C} (f: arrow a b), fmap G f o trans a = trans b o fmap F f
  }.

Arguments trans {_} {_} {_} {_} _ _.

Lemma Nt_split: ∏ (C D: Category)
                       (F  : @Functor C D) 
                       (G  : @Functor C D)
                       (nt1: NaturalTransformation F G)
                       (nt2: NaturalTransformation F G), trans nt1 = trans nt2 <-> nt1 = nt2.
Proof. intros. split. intros. destruct nt1, nt2, F, G.
       simpl in *. revert comm_diag0. rewrite H. intros.
       specialize (proof_irrelevance (∏ (a b : @obj C) (f : arrow a b),
             fmap1 a b f o trans1 a = trans1 b o fmap0 a b f) comm_diag0 comm_diag1).
       now destruct (proof_irrelevance _ comm_diag0 comm_diag1).
       intros. rewrite H. easy.
Qed.

Definition IdNt (C D: Category) 
                (F  : Functor C D): NaturalTransformation F F.
Proof. unshelve econstructor.
       - intros. exact (fmap _(@identity C a)).
       - intros. simpl. rewrite !preserve_id.
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
       - intro X.
         exact ( fmap I (trans nt1 X) o trans nt2 (fobj F X) ).
       - cbn. intros X Y f.
         now rewrite assoc, <- !preserve_comp, !comm_diag, <- assoc, preserve_comp.
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

Definition FunctorCategory (C D: Category): Category.
Proof.
       unshelve econstructor.
       - exact (Functor C D).
       - intros F G. exact (NaturalTransformation G F).
       - intros. exact (@IdNt C D a).
       - intros F G H nt1 nt2.
         exact (Compose_NaturalTransformations nt1 nt2).
       - intros. apply Nt_split.
         extensionality X. cbn.
         now rewrite assoc.
       - intros. apply Nt_split.
         extensionality X. cbn.
         now rewrite preserve_id, f_identity.
       - intros. apply Nt_split.
         extensionality X. cbn.
         now rewrite preserve_id, identity_f.
Defined.

Definition equalizer {C : Category} {a b : @obj C} (f g : arrow a b) (E : @obj C) (e : arrow E a) :=
  f o e = g o e /\ 
  ∏ (E' : @obj C) (e' : arrow E' a), f o e' = g o e' -> exists! u : arrow E' E, e o u = e'.

Definition coequalizer {C : Category} {a b : @obj C} (f g : arrow a b) (coE : @obj C) (coe : arrow b coE) :=
  coe o f = coe o g /\ 
  ∏ (coE' : @obj C) (coe' : arrow b coE'), coe' o f = coe' o g -> exists! u : arrow coE coE', u o coe = coe'.

Class hasEqualizers (C: Category) {a b: @obj C} (f g: arrow a b): Type :=
  {
     eqO  : @obj C;
     eqM  : arrow eqO a;
     eqObl: equalizer f g eqO eqM;
  }.

Class hasCoEqualizers (C: Category) {a b: @obj C} (f g: arrow a b): Type :=
  {
     coeqO  : @obj C;
     coeqM  : arrow b coeqO;
     coeqObl: coequalizer f g coeqO coeqM;
  }.

Class hasSplitEqualizers (C: Category) {a b: @obj C} (f g: arrow a b): Type :=
  {
     eqC : hasEqualizers C f g;
     secs: arrow a eqO;
     sect: arrow b a;
     sob1: secs o eqM = identity eqO;
     sob2: sect o g = identity a;
     sob3: sect o f = eqM o secs 
  }.

Class hasSplitCoEqualizers (C: Category) {a b: @obj C} (f g: arrow a b): Type :=
  {
     coeqC   : hasCoEqualizers C f g;
     cosecs  : arrow coeqO b;
     cosect  : arrow b a;
     coeqsob1: coeqM o cosecs = identity coeqO;
     coeqsob2: cosecs o coeqM = g o cosect;
     csob3: f o cosect = identity b 
  }.

Definition preserve_equalizers {C D: Category} {a b: @obj C} {f g: arrow a b} 
                               {p: hasEqualizers _ f g} (F: Functor C D): Type :=
  equalizer (fmap F f) (fmap F g) (fobj F eqO) (fmap F eqM).

Definition preserve_coequalizers {C D: Category} {a b: @obj C} {f g: arrow a b} 
                                 {p: hasCoEqualizers _ f g} (F: Functor C D) : Type :=
  coequalizer (fmap F f) (fmap F g) (fobj F coeqO) (fmap F coeqM).

Definition USplitPairs {C D: Category} (U: Functor D C) {a b: @obj D} (f g: arrow a b): Type :=
  hasSplitCoEqualizers C (fmap U f) (fmap U g).

Definition ReflexivePairs  {C D: Category} (U: Functor D C) {a b: @obj D} (f g: arrow a b): Type :=
  { s: arrow b a | f o s = g o s /\ f o s = identity b }.

Definition Isomorphism {C: Category} {a b: @obj C} (f: arrow a b): Type :=
  {  invf : arrow b a | f o invf = identity b /\ invf o f = identity a }.

Definition IsomorphismReflecting  {C D: Category} (F: Functor C D): Type :=
  ∏ (a b: @obj C) (g: arrow a b), Isomorphism (fmap F g) -> Isomorphism g.

Class Isomorphic {C: Category} (x y : @obj C) : Type := {
  to   : arrow y x;
  from : arrow x y;
  iso_to_from : to o from = @identity C x;
  iso_from_to : from o to = @identity C y
}.

(*
Parameters (C D E: Category) (F G: Functor C D).
(** a functor may be an isomorphism in the category of categories Cat *)
Check @Isomorphism Cat C D F.
(** tw categories may be ismorphic in the category of categories Cat *)
Check @Isomorphic Cat C D.
(** tw categories may be ismorphic in the category of functors FunctorCategory *)
Check @Isomorphic (FunctorCategory C D) F G.
*)

(** equivalence of categories up to natural isomorphism *)
Class EquivalenceCat {C D: Category} (F: Functor C D) (G: Functor D C): Type :=
  mk_EquivalenceCat
  {
     equiv_ob1: @Isomorphic (FunctorCategory C C) (Compose_Functors F G) (IdF C);
     equiv_ob2: @Isomorphic (FunctorCategory D D) (Compose_Functors G F) (IdF D)
  }.

Class Monad (C: Category)
            (T: Functor C C): Type :=
  mk_Monad
  {
    eta             : NaturalTransformation (IdF C) T;
    mu              : NaturalTransformation (Compose_Functors T T) T;
    comm_diagram1   : ∏ (a: @obj C), 
                           (trans mu a o fmap T (trans mu a)) =
                           (trans mu a o trans mu (fobj T a));
    comm_diagram2   : ∏ (a: @obj C), 
                           (trans mu a o fmap T (trans eta a)) =
                           (trans mu a o trans eta (fobj T a));
    comm_diagram2_b1: ∏ (a: @obj C), 
                           (trans mu a o fmap T (trans eta a)) =
                           (identity (fobj T a));
    comm_diagram2_b2: ∏ (a: @obj C), 
                           (trans mu a o trans eta (fobj T a)) =
                           (identity (fobj T a))
  }.

Arguments eta {_ _} _.
Arguments mu  {_ _} _.

(** comonads *)
Class coMonad (C: Category) 
              (D: Functor C C): Type :=
  mk_coMonad
  {
    eps    : NaturalTransformation D (IdF C);
    delta  : NaturalTransformation D (Compose_Functors D D);
    ccomm_diagram1   : ∏ (a: @obj C),
                            (fmap D (trans delta a) o trans delta a) =
                            (trans delta (fobj D a) o trans delta a);
    ccomm_diagram2   : ∏ (a: @obj C),
                            (fmap D (trans eps a) o trans delta a) =
                            (trans eps (fobj D a) o trans delta a);
    ccomm_diagram2_b1: ∏ (a: @obj C),
                            (trans eps (fobj D a) o trans delta a) =
                            (identity (fobj D a));
    ccomm_diagram2_b2: ∏ (a: @obj C),
                            (fmap D (trans eps a) o trans delta a) =
                            (identity (fobj D a))
  }.

Arguments eps   {_ _} _.
Arguments delta {_ _} _.


Class Adjunction {C D: Category}
                 (F  : @Functor C D)
                 (G  : @Functor D C): Type :=
  mk_Adj
  {
      unit  : (NaturalTransformation (IdF C) (Compose_Functors F G));
      counit: (NaturalTransformation (Compose_Functors G F) (IdF D));

      ob1   : ∏ a,  (trans counit (fobj F a) o fmap F (trans unit a)) =
                    (@identity D (fobj F a));
      ob2   : ∏ a,  (fmap G (trans counit a) o trans unit (fobj G a)) =
                    (@identity C (fobj G a))
  }.

Arguments unit {_ _ _ _} _.
Arguments counit {_ _ _ _} _.

Definition TAlgebra {C: Category} {T: Functor C C} (M: Monad C T) (a: @obj C) :=
  { alg_map: arrow (fobj T a) a |
                alg_map o (trans (eta M) a) = (@identity C a) /\ 
                alg_map o (fmap T (alg_map)) = alg_map o (trans (mu M) a) }.


(** eqTA with JMeq *)
Lemma eqTA: ∏
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1 TA2: TAlgebra M a), 
                  JMeq (proj1_sig TA1) (proj1_sig TA2) -> TA1 = TA2.
Proof. intros.
       destruct TA1, TA2. cbn in *. subst. f_equal.
       now destruct (proof_irrelevance _ a0 a1).
Qed.

Definition TAlgebraMap {C: Category} {T: Functor C C}{M: Monad C T} {a b: @obj C}
                       (TA1: TAlgebra M a)(TA2: TAlgebra M b) :=
  { tf: @arrow C a b | tf o (proj1_sig TA1) = (proj1_sig TA2) o fmap T tf }.

Definition idTAlg {C: Category} {T: Functor C C} {M: Monad C T} {X: @obj C}
                  (TA: TAlgebra M X): TAlgebraMap TA TA.
Proof. exists (identity X).
       now rewrite preserve_id, f_identity, identity_f.
Defined.

Proposition TAlgebraMapCompose {C: Category} {T: Functor C C}{M: Monad C T} {a b c: @obj C}
                               {TA: TAlgebra M a} {TB: TAlgebra M b} {TC: TAlgebra M c}
                               (Tf: TAlgebraMap TA TB) (Tg: TAlgebraMap TB TC): TAlgebraMap TA TC.
Proof. exists ((proj1_sig Tg) o (proj1_sig Tf)).
       destruct Tf as (f, ccf).
       destruct Tg as (g, ccg). cbn in *.
       now rewrite preserve_comp, <- assoc, ccf, assoc, ccg, assoc.
Defined.

Lemma eqTAM: ∏
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1    : TAlgebra M a)
                  (TA2    : TAlgebra M b)
                  (ta1 ta2: TAlgebraMap TA1 TA2)
                  (mapEq  : (proj1_sig ta1) = (proj1_sig ta2)), ta1 = ta2.
Proof. intros. 
       destruct ta1, ta2, TA1, TA2, T, M. cbn in *.
       subst. f_equal.
       destruct (proof_irrelevance _ e e0).
       easy.
Qed.

Definition EilenbergMooreCategory {C: Category} {T: Functor C C} (M: Monad C T): Category.
Proof. unshelve econstructor.
       - exact {a: @obj C & TAlgebra M a}.
       - intros TA TB. exact (TAlgebraMap (projT2 TA) (projT2 TB)).
       - intros (a, TA). exact (idTAlg TA).
       - intros TA TB TC Tg Tf. exact (TAlgebraMapCompose Tf Tg).
       - intros. apply eqTAM. cbn. now rewrite assoc.
       - intros. apply eqTAM. cbn in *.
         destruct a as (a, alpha).
         destruct b as (b, beta). cbn in *.
         now rewrite identity_f.
       - intros. apply eqTAM. cbn in *.
         destruct a as (a, alpha).
         destruct b as (b, beta). cbn in *.
         now rewrite f_identity.
Defined.

Definition FT {C  : Category}{T  : Functor C C}(M  : Monad C T)
                (EMC:= (EilenbergMooreCategory M)): Functor C EMC.
Proof. unshelve econstructor.
       - intro X.
         exists (fobj T X).
         exists (trans (mu M) X).
         split.
         + now specialize (comm_diagram2_b2 X).
         + now specialize (comm_diagram1 X).
       - intros X Y f.
         exists (fmap T f).
         + specialize (@comm_diag _ _ _ _ (mu M) _ _ f); intro H.
           cbn in *. now rewrite H.
       - intro a.
         apply eqTAM. cbn.
         now rewrite !preserve_id.
       - intros a b c g f.
         apply eqTAM. cbn.
         now rewrite !preserve_comp.
Defined.
Check FT.

(** right adjoint functor that acts as G_T *)
Definition GT {C  : Category}{T  : Functor C C}(M  : Monad C T)
              (EMC:= (EilenbergMooreCategory M)): Functor EMC C.
Proof. unshelve econstructor.
       - intro X. exact (projT1 X).
       - intros TA TB Tf. exact (proj1_sig Tf).
       - intros (X, alpha). easy.
       - intros a b c g f. easy.
Defined.
Check GT.

Theorem mon_emadj: ∏
                   {C  : Category}
                   {T  : Functor C C}
                   (M  : Monad C T), Adjunction (FT M) (GT M).
Proof. intros.
       unshelve econstructor.
       - unshelve econstructor.
         + intro X. exact (trans (eta M) X).
         + intros X Y f.
           specialize (@comm_diag _ _ _ _ (eta M) _ _ f); intro H.
           cbn in H. exact H.
       - unshelve econstructor.
         + intro TA. cbn in TA.
           unshelve econstructor.
           ++ exact (proj1_sig (projT2 TA)).
           ++ destruct TA as (X, (tf, (cc0, cc1))). cbn in *.
              now rewrite <- cc1.
         + intros a b f. destruct a, b, f.
           apply eqTAM. cbn in *.
           easy.
       - intro a.
         apply eqTAM. cbn.
         specialize (@comm_diagram2_b1 _ _ M a); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro a. cbn.
         destruct a, t. now cbn in *.
Defined.

(** every adjunction gives raise to a monad *)
Theorem adj_mon: ∏ {C1 C2: Category}(F: Functor C1 C2)(G: Functor C2 C1),
                 Adjunction F G -> Monad C1 (Compose_Functors F G).
Proof. intros C1 C2 F G A.
       unshelve econstructor.
       - exact (unit A).
       - unshelve econstructor.
         + intro X. exact (fmap G (trans (counit A) (fobj F X))).
         + intros X Y f. cbn.
           rewrite <- !preserve_comp.
           specialize (@comm_diag _ _ _ _ (counit A) _ _ (fmap F f)); intro H.
           cbn in *.  unfold id in *. now rewrite H.
       - intros X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@comm_diag _ _ _ _ (counit A) _ _ (trans (counit A) (fobj F X))); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A X); intro H1.
         specialize (@ob2 _ _ _ _ A (fobj F X)); intro H2.
         cbn in *.  unfold id in *. 
         now rewrite H2, H1, preserve_id.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A X); intro H1.
         cbn in *.  unfold id in *.
         now rewrite H1, preserve_id.
       - intro X. cbn in *.
         specialize (@ob2 _ _ _ _ A (fobj F X)); intro H2.
         cbn in *.  unfold id in *.
         now rewrite H2.
Defined.
Check adj_mon.

(** every adjunction gives raise to a comonad *)
Theorem adj_comon: ∏ {C1 C2: Category}(F: @Functor C1 C2)(G: @Functor C2 C1),
                 Adjunction F G -> coMonad C2 (Compose_Functors G F).
Proof. intros C1 C2 F G A. 
       unshelve econstructor.
       - exact (counit A).
       - unshelve econstructor.
         + intro X. exact (fmap F (trans (unit A) (fobj G X))).
         + intros X Y f. cbn.
           rewrite <- !preserve_comp.
           specialize (@comm_diag _ _ _ _ (unit A) _ _ (fmap G f)); intro H.
           cbn in *.  unfold id in *. now rewrite H.
       - intros X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@comm_diag _ _ _ _ (unit A) _ _ (trans (unit A) (fobj G X))); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A (fobj G X)); intro H1.
         specialize (@ob2 _ _ _ _ A X); intro H2.
         cbn in *.  unfold id in *. 
         now rewrite H2, H1, preserve_id.
       - intro X. cbn in *.
         specialize (@ob1 _ _ _ _ A (fobj G X)); intro H1.
         cbn in *.  unfold id in *.
         now rewrite H1.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob2 _ _ _ _ A X); intro H2.
         cbn in *.  unfold id in *.
         now rewrite H2, preserve_id.
Defined.
Check adj_comon.

Definition KT: ∏ {C D: Category} (F: Functor C D) (G: Functor D C)(A: Adjunction F G),
                let M   := adj_mon F G A in
                let EMC := EilenbergMooreCategory M in Functor D EMC.
Proof. intros.
       unshelve econstructor.
       - intro X.
         exists (fobj G X).
         exists (fmap G (trans (counit A) X)).
         split.
         + now rewrite (@ob2 _ _ _ _ A).
         + cbn in *.
           rewrite <- !preserve_comp. f_equal.
           specialize (@comm_diag _ _ _ _ (counit A) _ _ (trans (counit A) X)); intro H.
           cbn in *. unfold id in *. now rewrite <- H.
       - intros X Y f. 
         exists (fmap G f).
         cbn in *.
         rewrite <- !preserve_comp. f_equal.
         specialize (@comm_diag _ _ _ _ (counit A) _ _ f); intro H.
         cbn in *. unfold id in *. now rewrite <- H.
       - intro X.
         apply eqTAM. cbn in *.
         now rewrite preserve_id.
       - intros X Y Z g f.
         apply eqTAM.
         cbn in *.
         now rewrite preserve_comp.
Defined.
Check KT.


Inductive eq_dep {U: Type} {P: U -> Type} (p: U) (x: P p): ∏ (q: U), P q -> Prop :=
  | eq_dep_intro : eq_dep p x p x.
  Hint Constructors eq_dep: core.

Lemma eq_sigT_eq_dep: ∏ (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
    existT P p x = existT P q y -> eq_dep p x q y.
Proof.
  intros.
  dependent rewrite H.
  apply eq_dep_intro.
Qed.

Lemma eq_dep_eq_sigT: ∏ (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
    eq_dep p x q y -> existT P p x = existT P q y.
Proof.
  destruct 1; reflexivity.
Qed.

Lemma eq_sigT_iff_eq_dep: ∏ (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
    existT P p x = existT P q y <-> eq_dep p x q y.
Proof.
  split; auto using eq_sigT_eq_dep, eq_dep_eq_sigT.
Qed.

Lemma eq_dep_id_JMeq: ∏ (A: Type) (B:Type) (x:A) (y:B), 
   @eq_dep Type (fun X:Type => X) A x B y -> JMeq x y.
Proof. intros A B x y p. 
       now destruct p.
Qed.

Definition eq_existT_uncurried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
           (pq : { p : u1 = v1 & eq_rect _ P u2 _  p = v2 }): existT _ u1 u2 = existT _ v1 v2.
Proof.
  destruct pq as [p q].
  destruct q; simpl in *.
  destruct p; reflexivity.
Defined.

Lemma commKT: ∏ {C D: Category} (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
               let M   := (adj_mon F G A) in
               let EMC := (EilenbergMooreCategory M) in
                 (Compose_Functors (KT F G A) (GT M)) = G /\ (Compose_Functors F (KT F G A)) = (FT M).
Proof. intros C D F G A M EMC; split. 
       - apply F_split.
         + easy.
         + apply eq_dep_id_JMeq, eq_sigT_iff_eq_dep, eq_existT_uncurried.
           cbn. unfold eq_rect.
           exists eq_refl. easy.
       - apply F_split.
         + cbn. unfold id in *.
           extensionality a.
           apply f_equal.
           apply eqTA; easy.
         + assert (H: fobj (Compose_Functors F (KT F G A)) = fobj (FT M)).
           cbn. unfold id in *.
           extensionality a.
           apply f_equal.
           apply eqTA; easy.

           apply eq_dep_id_JMeq.
           apply eq_sigT_iff_eq_dep.
           apply eq_existT_uncurried.

           assert ((∏ a b : obj,
           arrow a b -> arrow (fobj (Compose_Functors F (KT F G A)) a) 
            (fobj (Compose_Functors F (KT F G A)) b)) =
            (∏ a b : obj, arrow a b -> arrow (fobj (FT M) a) (fobj (FT M) b)) ).
           { now rewrite H. }

           exists H0.
           unfold eq_rect.
           assert (H0 = eq_refl).
           { specialize (UIP_refl _  
               (∏ a b : obj, arrow a b -> arrow (fobj (FT M) a) (fobj (FT M) b))); intros.
             now specialize (H1 H0).
           }
           rewrite H1.
           cbn.

           extensionality x.
           extensionality y.
           extensionality f.
           now apply subset_eq_compat.
Qed.

Lemma K_unique: ∏
               {C D    : Category}
               (F      : Functor C D)
               (G      : Functor D C) 
               (A1     : Adjunction F G),
               let M   := (adj_mon F G A1) in
               let EMC := (EilenbergMooreCategory M) in
               let A2  := (mon_emadj M) in
                 ∏ R : Functor D EMC, Compose_Functors R (GT M) = G /\
                                           Compose_Functors F R = (FT M) -> (KT F G A1) = R.
Admitted.

Class MonadicFunctor {C D: Category} (U: Functor D C): Type :=
  mk_MF
  { 
      LAU : Functor C D;
      MA  : Adjunction LAU U;
      MMF := adj_mon LAU U MA;
      KINV: Functor (EilenbergMooreCategory MMF) D;
      MFOb: EquivalenceCat (KT LAU U MA) KINV
  }.

Class DCOEQUSP_UPCOEQ {C D: Category} {a b: @obj D} (f g: arrow a b) (U: Functor D C): Type :=
  {
      USPCEQ: USplitPairs U f g;
      DCEQ  : hasCoEqualizers D f g;
      UPEQ  : preserve_coequalizers U
  }.

Definition MonadicFunctorBeck {C D: Category} (U: Functor D C): Type :=
  { LAU: Functor C D & (Adjunction LAU U *
                        IsomorphismReflecting U * 
                        ∏ {a b: @obj D} (f g: arrow a b), DCOEQUSP_UPCOEQ f g U)%type }.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

Lemma BeckMonadicity: ∏ {C D: Category} {a b: @obj D} (f g: arrow a b) (U: Functor D C),
  MonadicFunctorBeck U -> MonadicFunctor U.
Admitted.

(*----------------------------------------------------------------------------------------------------*)

(** Coq Universes as categories *)
Notation CoqCat U :=
{|
  obj := U;
  arrow := (fun A B => A -> B);
  identity := (fun _ => id);
  comp :=   (fun A B C (g: B -> C) (f: A -> B) a => g (f a))
|}.

Program Definition CoqCatT: Category := CoqCat Type.
Program Definition CoqCatS: Category := CoqCat Set.
Program Definition CoqCatP: Category := CoqCat Prop.

(** Some basic functor examples from CIC *)

(** Conjuncton -| Implication *)
(** functors Fp and Gp *)
Definition fobjFp := fun p q => p /\ q.

Definition fmapFp:=
  fun p (a b: Prop) (f: a -> b) (H: p /\ a) =>
  match H with
    | conj x y => conj x (f y)
  end.

Definition Fp: forall (p: @obj CoqCatP), Functor CoqCatP CoqCatP.
Proof. unshelve econstructor.
       - intro q. exact (fobjFp p q).
       - intros a b f. exact (fmapFp p a b f).
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
       - intros. cbn in *. extensionality H. easy.
       - intros. cbn in *. extensionality H. easy.
Defined.

(** natural transformations unit_GpFp and counit_GpFp *)
Definition unit_GpFp: forall (p: @obj CoqCatP),
  NaturalTransformation (IdF CoqCatP) (Compose_Functors (Fp p) (Gp p)).
Proof. intro p.
       unshelve econstructor.
       - intro q. exact (fun (pq: id q) (pp: p) => conj pp pq).
       - intros a b f. extensionality pa. easy.
Defined.

Definition counit_FpGp: forall (p: @obj CoqCatP),
  NaturalTransformation (Compose_Functors (Gp p) (Fp p)) (IdF CoqCatP).
Proof. intro p.
       unshelve econstructor.
       - intro q. exact (fun (H: p /\ (p -> q)) => match H with conj pp ppiq => ppiq pp end).
       - cbn. intros a b f.
         extensionality pp. 
         destruct pp. easy.
Defined.

(** Fp and Gp are adjoint *)
Definition FpGp_Adjoint (p: @obj CoqCatP) : Adjunction (Fp p) (Gp p).
Proof. unshelve econstructor.
       - exact (unit_GpFp p).
       - exact (counit_FpGp p).
       - intro a. extensionality H.
         now destruct H.
       - intro a. easy.
Defined.

(** Monad examples *)

(** Option functor *)
Definition fmapOption {A B: Type} (f: A -> B) (i: option A): option B:=
  match i with
    | Some a => Some (f a)
    | None   => None
  end.

Definition FunctorO: Functor CoqCatT CoqCatT.
Proof. unshelve econstructor.
       - intro a. exact (option a).
       - intros a b f g. exact (fmapOption f g).
       - intros. cbn in *.
         extensionality b. compute.
         case_eq b; intros; easy.
       - cbn. intros.
         extensionality h. cbv in *.
         case_eq h; intros; easy.
Defined.

(** natural transformations *)
Definition EtaFo: NaturalTransformation (IdF CoqCatT) FunctorO.
Proof. unshelve econstructor.
       - intros A a. exact (Some a).
       - intros A B f. cbn. easy.
Defined.

Definition multO {A : Type} (i: option (option A)): option A :=
  match i with
    | Some a => a
    | None   => None
  end.

Definition MuFo: NaturalTransformation (Compose_Functors FunctorO FunctorO) (FunctorO).
Proof. unshelve econstructor.
       - intros A i. exact (multO i).
       - intros A B f. cbn in *.
         extensionality a.
         unfold fmapOption, multO.
         case_eq a. intros op H.
         case_eq op. intros op2 H2.
         easy. easy. easy.
Defined.

(** Option monad *)
Definition Mo: Monad CoqCatT FunctorO.
Proof. unshelve econstructor.
       - exact EtaFo.
       - exact MuFo.
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
       - intros. cbn in *.
         extensionality b. compute.
         case_eq b; intros; easy.
       - cbn. intros.
         extensionality h. cbv in *.
         case_eq h; intros; easy.
Defined.

(** natural transformations *)
Definition fmapFM {A : Type} (i: maybe (maybe A)): maybe A :=
  match i with
    | just _ a => a
    | nothing _ => nothing _
  end.

Definition EtaFm: NaturalTransformation (IdF CoqCatT) FunctorM.
Proof. unshelve econstructor.
       - intro A. cbn in *.
         intro a. exact (just A a).
       - intros A B f. cbn. easy.
Defined.

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

(** State functor. *)
Definition fobjFs (s a : Type) := s -> (a * s).

Definition fmapFs (s A B: Type) (f: A -> B) (x : fobjFs s A) :=
  fun st =>
    match x st with
      | (a, st') => (f a, st')
    end.

Definition FunctorS: forall (s: @obj CoqCatT), Functor CoqCatT CoqCatT.
Proof. intro s.
       unshelve econstructor.
       - intros a. exact (fobjFs s a).
       - intros a b f. exact (fmapFs s a b f).
       - intros. cbn in *.
         extensionality X. compute.
         extensionality st. now destruct X.
       - intros. cbn in *.
         extensionality X. compute.
         extensionality st. now destruct X.
Defined.

(** natural transformations *)
Definition EtaFs: forall (s: @obj CoqCatT), NaturalTransformation (IdF CoqCatT) (FunctorS s).
Proof. intro s.
       unshelve econstructor.
       + cbn. intros a v.
         exact (fun st: s => (v, st)).
       + cbn. intros a b f.
         extensionality v. easy.
Defined.

Definition MuFs: forall (s: @obj CoqCatT),
  NaturalTransformation (Compose_Functors (FunctorS s) (FunctorS s)) (FunctorS s).
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
Definition Ms: forall (s: @obj CoqCatT), Monad CoqCatT (FunctorS s).
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

(*----------------------------------------------------------------------------------------------------*)

