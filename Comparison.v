Require Export Adjunctions.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.


(** Mac Lane's comparison theorem of 
                               an arbitrary adjunction
                               and the Kleisli adjunction it determines *)
Theorem ComparisonMacLane: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (@adj_mon   C D F G A1) in
               let CT := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (LA F G M) in
               let GT := (RA F G M) in
               let A2 := (mon_kladj F G M) in
                 exists L: Functor CT D,
                   (Compose_Functors FT L) = F /\ (Compose_Functors L G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
      (*
       pose proof A2 as A22.
       pose proof A1 as A11.
       apply adjEq12 in A11.
       apply adjEq12 in A22.
      *)
       exists (L F G A1).
       split.  cbn in *.
       
       unfold M, CT, GT. cbn in *.
       assert (fobj (Compose_Functors FT (L F G A1)) = fobj F).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split C D
         (Compose_Functors FT (L F G A1)) F); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, L.
       simpl in *.
       assert (H = eq_refl).
       {
          specialize (UIP_refl _   (fun a : @obj C => fobj a)); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b. extensionality f.
       rewrite preserve_comp.
       rewrite assoc.
       now rewrite ob1, identity_f.

       simpl in *.
       assert (fobj (Compose_Functors (L F G A1) G) = fobj GT).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split (Kleisli_Category C 
         (Compose_Functors F G) M) C 
         (Compose_Functors (L F G A1) G) GT); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl in *.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, L.
       simpl in *.
       assert (H = eq_refl).
       { 
          specialize (UIP_refl _  
           (fun a : @obj C => fobj0 (fobj a))); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b.
       extensionality f. now rewrite preserve_comp0.
Qed.
Check ComparisonMacLane.


(** Mac Lane's comparison theorem of 
                               an arbitrary adjunction
                               and the coKleisli adjunction it determines *)
Theorem coComparisonMacLane: forall
                 {C D   : Category}
                 (F     : Functor D C)
                 (G     : Functor C D)
                 (A1    : Adjunction F G),
                 let cM := (@adj_comon D C F G A1) in
                 let CD := (coKleisli_Category C (Compose_Functors G F) cM) in
                 let FD := (cLA F G cM) in
                 let GD := (cRA F G cM) in
                 let A2 := (comon_cokladj F G cM) in
                 exists L: Functor CD D,
                   (Compose_Functors GD L) = G /\ (Compose_Functors L F) = FD.
Proof. intros C D F G A1 cM CD FD GD A2.
      (*
       pose proof A2 as A22.
       pose proof A1 as A11.
       apply adjEq10 in A11.
       apply adjEq12 in A22.
      *)
       exists (duL F G A1).
       split. cbn in *.

       unfold cM, CD, FD. cbn in *.
       assert (fobj (Compose_Functors GD (duL F G A1)) = fobj G).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split C D
         (Compose_Functors GD (duL F G A1)) G); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, duL.
       simpl in *.
       assert (H = eq_refl).
       {
          specialize (UIP_refl _   (fun a : @obj C => fobj0 a)); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b. extensionality f.
       rewrite preserve_comp0.
       rewrite <- assoc.
       now rewrite ob2, f_identity.

       simpl in *.
       assert (fobj (Compose_Functors (duL F G A1) F) = fobj FD).
       { 
           unfold Compose_Functors. simpl in *.
           unfold id in *. easy.
       }
       simpl.
       specialize (F_split (coKleisli_Category C 
         (Compose_Functors G F) cM) C 
         (Compose_Functors (duL F G A1) F) FD); intros.
       specialize (H0 H). apply H0.
       unfold Compose_Functors. simpl in *.
       destruct A1, unit, counit. simpl in *.
       unfold id in *. destruct F, G, duL.
       simpl in *.
       assert (H = eq_refl).
       { 
          specialize (UIP_refl _  
           (fun a : @obj C => fobj (fobj0 a))); intros.
          now specialize (H1 H).
       }
       rewrite H1.
       extensionality a. extensionality b.
       extensionality f.
       now rewrite preserve_comp.
Qed.
Check coComparisonMacLane.
