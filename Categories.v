Require Export Imports.

Set Universe Polymorphism.

Polymorphic Cumulative Class Category: Type :=
 mk_Category 
 {
     obj       : Type;
     arrow     : obj -> obj -> Type;
     identity  : forall a, arrow a a;
     comp      : forall {a b c}, (arrow c b) -> (arrow b a) -> (arrow c a);
     compose_respects x y z : Proper (eq ==> eq ==> eq) (@comp x y z); 
     assoc     : forall {a b c d} (f : arrow b a) (g : arrow c b) (h : arrow d c), 
                              comp h (comp g f) = comp (comp h g) f;
     identity_f: forall {a b} (f: arrow b a), comp (@identity b) f = f;
     f_identity: forall {a b} (f: arrow b a), comp f (@identity a) = f 
  }.

Notation " g 'o' f " := (@comp _ _ _ _ g f) (at level 40, left associativity).

(** sameness of categories *)
Lemma C_split: forall C D: Category,
               @obj C = @obj D ->
               JMeq (@arrow C) (@arrow D) -> 
               JMeq (@identity C) (@identity D) ->
               JMeq (@comp C) (@comp D) -> C = D.
Proof. intros C D H0 H1 H2 H3.
       destruct C, D. cbn in *. subst.
       apply JMeq_eq in H1. subst. apply JMeq_eq in H2. subst. f_equal.
       now destruct (proof_irrelevance _ compose_respects0 compose_respects1).
       now destruct (proof_irrelevance _ assoc0 assoc1).
       now destruct (proof_irrelevance _ identity_f0 identity_f1).
       now destruct (proof_irrelevance _ f_identity0 f_identity1).
Defined.

(** some example categories *)
Class SubCategory (C: Category): Type :=
  mk_SubCategory
  {
     s_obj     : @obj C -> Type;
     s_arrow   : forall (a b: @obj C), s_obj a -> s_obj b -> @arrow C a b -> Type;
     s_identity: forall (a: @obj C) (sa: s_obj a), s_arrow a a sa sa (@identity C a);
     s_comp    : forall (a b c: @obj C) (sa: s_obj a) (sb: s_obj b) (sc: s_obj c)
                        (f: arrow b c) (g: arrow a b), 
                         s_arrow a b sa sb g -> s_arrow b c sb sc f ->
                         s_arrow a c sa sc (g o f) 
  }.

Definition Product_Category (C D: Category) : Category.
Proof.
  refine (@mk_Category 
           (@obj C * @obj D)%type
           (fun a b => (@arrow C (fst a) (fst b) * @arrow D (snd a) (snd b))%type)
           (fun a => (@identity C (fst a), @identity D (snd a)))
           (fun a b c g f => (fst g o fst f, snd g o snd f))
           _ _ _ _ 
         ).
  - setoid_rewrite <- assoc. reflexivity. 
  - intros. simpl. rewrite !identity_f. destruct f. now simpl.
  - intros. simpl. rewrite !f_identity. destruct f. now simpl.
Defined.

Definition Dual_Category (C: Category) : Category.
Proof. 
  refine (@mk_Category 
           (@obj C)%type
           (fun a b => (@arrow C b a %type))
           (fun a => (@identity C a))
           (fun a b c f1 f2 => f2 o f1)
           _ _ _ _ 
         ).
 - intros. now rewrite <- assoc.
 - intros. now rewrite f_identity.
 - intros. now rewrite identity_f.
Defined.

Notation "C × D ":= (@Product_Category C D) (at level 40, left associativity).
Notation "C ^op" := (@Dual_Category C) (at level 40, left associativity).


(** Coq Universes as categories *)
Notation CoqCat U :=
{|
  obj := U;
  arrow := (fun A B => B -> A);
  identity := (fun _ => id);
  comp :=   (fun A B C (g: B -> C) (f: A -> B) a => g (f a))
|}.

Program Definition CoqCatT: Category := CoqCat Type.
Program Definition CoqCatS: Category := CoqCat Set.
Program Definition CoqCatP: Category := CoqCat Prop.

