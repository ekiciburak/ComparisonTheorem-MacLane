Add LoadPath "/PATH/to/Timany's/library" as Categories.
From Categories Require Import Category Functor NatTrans.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Add LoadPath "/PATH/to/oru/library" as ECat.
From ECat Require Import Category Functor NaturalTransformation.

Notation catE := ECat.Category.Category.
Notation catT := Categories.Category.Category.Category.

Lemma cateql: catE -> catT.
Proof. intro C.
       unshelve econstructor.
       destruct C.
       - exact obj.
       - cbn. exact arrow.
       - intros a b c f g. exact (f o g).
       - exact (identity).
       - intros. cbn. now rewrite assoc.
       - intros. cbn. now rewrite assoc.
       - intros. cbn. now rewrite f_identity.
       - intros. cbn. now rewrite identity_f.
Defined.

Lemma cateqr: catT -> catE.
Proof. intro C.
       unshelve econstructor.
       destruct C.
       - exact Obj.
       - exact Hom.
       - intro a. exact (id a).
       - intros a b c f g. cbn in *. exact (compose f g).
       - repeat intro. now subst.
       - intros. cbn. now rewrite assoc_sym.
       - intros. cbn. now rewrite id_unit_right.
       - intros. cbn. now rewrite id_unit_left.
Defined.

Lemma cateq_opp: forall D, cateql (cateqr D) = D.
Proof. intros. destruct D. cbn in *.
       unfold cateqr, cateql. cbn.
       f_equal.
       extensionality a.
       extensionality b.
       extensionality c.
       extensionality d.
       extensionality f.
       extensionality g.
       extensionality h.
       unfold eq_ind_r, eq_ind, eq_sym. cbn in *.

       generalize dependent (assoc a b c d f g h).
       rewrite assoc_sym.
       intros.
       assert (e = eq_refl).
             {
                specialize (UIP_refl _
                 (compose a b d f (compose b c d g h))); intros.
                now specialize (H e).
             }
       now subst.

       f_equal.
       extensionality a.
       extensionality b.
       extensionality c.
       extensionality d.
       extensionality f.
       extensionality g.
       extensionality h.

       generalize dependent (assoc a b c d f g h).
       rewrite assoc_sym.
       intros. now cbn.

       extensionality a.
       extensionality b.
       extensionality f.
       unfold eq_ind_r, eq_ind, eq_sym. cbn in *.
       now destruct (id_unit_left a b f).

       extensionality a.
       extensionality b.
       extensionality f.
       unfold eq_ind_r, eq_ind, eq_sym. cbn in *.
       now destruct (id_unit_right a b f).
Defined. 


Notation funE := ECat.Functor.Functor.
Notation funT := Categories.Functor.Functor.Functor.


Lemma funceql: forall (C D: catE), funE C D -> funT (cateql C) (cateql D).
Proof. intros C D F.
       destruct F.
       unshelve econstructor.
       - intro a. exact (fobj a).
       - intros a b f. cbn in *. exact (fmap b a f).
       - intros. cbn in *. now rewrite preserve_id.
       - intros. cbn in *. now rewrite preserve_comp.
Defined.

Lemma funceqr: forall (C D: catE), funT (cateql C) (cateql D) -> funE C D.
Proof. intros C D F.
       destruct F.
       unshelve econstructor.
       - intro a. exact (FO a).
       - intros. cbn in *. exact (FA b a f).
       - repeat intro. now subst.
       - intros. cbn in *. now rewrite F_id.
       - intros. cbn in *. now rewrite F_compose.
Defined.

Lemma funceq_opp: forall (D E: catE) (F: funE D E), funceqr D E (funceql D E F) = F.
Proof. intros. destruct F. cbn in *.
       unfold funceql, funceqr. cbn.
       f_equal.
       extensionality a.
       extensionality b.
       extensionality f.
       extensionality g.
       extensionality H. subst. cbn.
       now rewrite UIP_refl.

       extensionality a.
       unfold eq_ind_r, eq_ind, eq_sym. cbn in *.
       now destruct (preserve_id a).

       extensionality a.
       extensionality b.
       extensionality c.
       extensionality g.
       extensionality f.
       unfold eq_ind_r, eq_ind, eq_sym. cbn in *.
       now destruct (preserve_comp a b c g f ).
Defined.


Notation nTE := ECat.NaturalTransformation.NaturalTransformation.
Notation nTT := Categories.NatTrans.NatTrans.NatTrans.

Lemma nattranseql: forall (D E: catE) (F G: funE D E),
@nTE D E F G ->
@nTT (cateql D) (cateql E) (funceql D E G) (funceql D E F).
Proof. intros D E F G n.
       destruct n.
       unshelve econstructor.
       - intro c. cbn in *. exact (trans c).
       - intros c d f. cbn in *. now rewrite comm_diag.
       - intros c d f. cbn in *. now rewrite comm_diag.
Defined.

Lemma nattranseqr: forall (D E: catE) (F G: funE D E),
@nTT (cateql D) (cateql E) (funceql D E G) (funceql D E F) ->
@nTE D E F G.
Proof. intros D E F G n.
       destruct n.
       unshelve econstructor.
       - intro c. cbn in *. exact (Trans c).
       - intros c d f. cbn in *. now rewrite Trans_com.
Defined. 





