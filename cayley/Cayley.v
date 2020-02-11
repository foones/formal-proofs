
(* Proof of Cayley's theorem for groups *)

Structure Grupo := mkGrupo {
  C   : Set ;           (* carrier *)
  e   : C ;             (* elemento neutro *)
  op  : C -> C -> C ;   (* operación binaria *)
  inv : C -> C ;        (* inverso *)

  (* axiomas de grupo *)
  assoc  : forall x y z,  op (op x y) z = op x (op y z) ;
  neut_l : forall x,  op e x = x ;
  neut_r : forall x,  op x e = x ;
  inv_r  : forall x,  op x (inv x) = e
}.

Definition carrier (G : Grupo) : Set := C G.

Section Ejemplo_Grupo_ℤ2.
  
  Inductive A : Set :=
    | O : A
    | I : A.
  
  Let f (x : A) (y : A) : A :=
    match x with
    | O => y
    | I => match y with
           | O => I
           | I => O
           end
    end.

   Eval compute in (f (f O I) (f I I)).

   (* f asociativa *)
   Lemma ℤ2_G1 : forall a b c,  f (f a b) c = f a (f b c).
     intros a b c.
     case a; case b; case c; trivial.
   Qed.
   
   (* O neutro a izquierda *)
   Lemma ℤ2_G2 : forall a,  f O a = a.
     trivial.
   Qed.

   (* O neutro a derecha *)
   Lemma ℤ2_G3 : forall a,  f a O = a.
     intros a.
     case a; trivial.
   Qed.

   (* Cada elemento es inverso de sí mismo. *)
   Lemma ℤ2_G4 : forall a,  f a a = O.
     intros a.
     case a; trivial.
   Qed.
   
   Definition ℤ2 : Grupo :=
     mkGrupo
       A            (* carrier *)
       O            (* elemento neutro *)
       f            (* operación binaria *)
       (fun x => x) (* inverso *)
       ℤ2_G1           
       ℤ2_G2
       ℤ2_G3
       ℤ2_G4.

End Ejemplo_Grupo_ℤ2.

Notation "x · y" := (op _ x y) (at level 20).
Notation "x ⁻¹"  := (inv _ x) (at level 5).
Notation "1"     := (e _).

Section Propiedades_Básicas.

    Variable G : Grupo.
    
    Lemma cancel_r :  forall x y z : carrier G,  x·z = y·z  ->  x = y.
      intros x y z H.
      assert ( x·(z·z⁻¹) = y·(z·z⁻¹) ) as H'.
        rewrite <-? assoc.
        rewrite H.
        reflexivity.
      rewrite inv_r, ? neut_r in H'.
      assumption.
    Qed.

    Lemma inv_l : forall x : carrier G,  x⁻¹ · x = 1.
      intros x.
      apply cancel_r with (z := x⁻¹).
      rewrite assoc, inv_r, neut_r, neut_l.
      reflexivity.
    Qed.

    Lemma cancel_l : forall x y z : carrier G,  z·x = z·y  ->  x = y.
      intros x y z H.
      assert ( (z⁻¹·z)·x = (z⁻¹·z)·y ) as H'.
        rewrite ? assoc, H; reflexivity.
      rewrite inv_l, ? neut_l in H'.
      assumption.
    Qed.    

    (* Inverso del neutro *)
    Lemma inv_1 : 1⁻¹ = (1 : carrier G).
      apply cancel_l with 1.
      rewrite inv_r.
      rewrite neut_r.
      reflexivity.
    Qed.

    (* Inverso del producto *)
    Lemma inv_xy : forall x y : carrier G,  (x · y)⁻¹ = y⁻¹ · x⁻¹.
      intros x y.
      apply cancel_l with (x · y).
      rewrite inv_r, assoc. 
      replace (y·(y⁻¹·x⁻¹)) with ((y·y⁻¹)·x⁻¹). 
      rewrite inv_r, neut_l, inv_r.
      reflexivity.
      apply assoc.
    Qed.

    (* Inverso del inverso *)
    Lemma inv_inv : forall x : carrier G, x⁻¹⁻¹ = x.
      intro x.
      apply cancel_l with x⁻¹.
      rewrite inv_r.
      rewrite inv_l.
      reflexivity.
    Qed.
    
End Propiedades_Básicas.

Section Grupo_Simétrico.
  
  Require Import ProofIrrelevance.
  Require Import FunctionalExtensionality.
  Load Defs.

  (* El grupo simétrico depende de un parámetro: un conjunto X *)
  Variable X : Set.
  
  Let composición (f g : X -> X) := fun x => f (g x).

  Let Id (x : X) := x.

  Notation "f ∘ g" := (composición f g) (at level 20).
  
  Lemma composición_id :
    forall f g,  f ∘ g = Id  ->  forall x,  f (g x) = x.
  Proof.
    intros f g H x.
    apply equal_f with x in H.
    compute in H.
    assumption.
  Qed.    

  Let inversas (F G : X -> X) := F ∘ G = Id  /\  G ∘ F = Id.

  (* El siguiente va a ser el carrier del grupo simétrico.
   * Sus elementos son tuplas de la forma (F, G, inv_FG)
   * donde   F G : X -> X
   *         inv_FG : inversas F G
   * (inv_FG es evidencia de que F y G son inversas).   
   *)
  Structure Permutación := mkPerm {
                             F      : X -> X ;
                             G      : X -> X ;
                             inv_FG : inversas F G
                           }.

  (* Lema técnico: toda permutación está determinada por F y G.
   * Usa proof_irrelevance.
   *)
  Lemma perm_eq :
    forall σ τ,
      F σ = F τ  ->  G σ = G τ  ->  σ = τ.
  Proof.
    intros σ τ eq_F eq_G.
    destruct σ as (F1, G1, inv1).
    destruct τ as (F2, G2, inv2).
    assert (F1 = F2) as Fs. assumption.
    assert (G1 = G2) as Gs. assumption.
    destruct Fs, Gs.
    replace inv1 with inv2.
    reflexivity.
    apply proof_irrelevance.
  Qed.

  (* La operación del grupo simétrico es la composición. *)
  Let sym_op (σ τ : Permutación) : Permutación.
    apply mkPerm with (F := F σ ∘ F τ) (G := G τ ∘ G σ).
    split.
      (* F ∘ G *)
      apply functional_extensionality.
      intro x; unfold composición.
      rewrite (composición_id (F τ) (G τ)).
      rewrite (composición_id (F σ) (G σ)).
      reflexivity.
      apply (inv_FG σ).
      apply (inv_FG τ).

      (* G ∘ F *)
      apply functional_extensionality.
      intro x; unfold composición.
      rewrite (composición_id (G σ) (F σ)).
      rewrite (composición_id (G τ) (F τ)).
      reflexivity.
      apply (inv_FG τ).
      apply (inv_FG σ).
  Defined.

  (* El elemento neutro es la identidad. *)
  Let sym_e : Permutación.
    apply mkPerm with (F := Id) (G := Id).
    split; apply functional_extensionality; compute; reflexivity.
  Defined.

  (* La inversa de una permutación. *)
  Let sym_inv (σ : Permutación) : Permutación.
    destruct σ as (F, G, inv_FG).
    apply mkPerm with (F := G) (G := F).
    split.
    apply inv_FG.
    apply inv_FG.
  Defined.

  (* sym_op es asociativa *)
  Lemma sym_G1 : forall σ τ ρ, sym_op (sym_op σ τ) ρ = sym_op σ (sym_op τ ρ).
    intros σ τ ρ.
    apply perm_eq.
    reflexivity.
    reflexivity.
  Qed.
  
  (* sym_e neutro a izquierda *)
  Lemma sym_G2 : forall σ, sym_op sym_e σ = σ.
    intros.
    apply perm_eq.
    reflexivity.
    reflexivity.
  Qed.
  
  (* sym_e neutro a derecha *)
  Lemma sym_G3 : forall σ, sym_op σ sym_e = σ.
    intros.
    apply perm_eq.
    reflexivity.
    reflexivity.
  Qed.

  (* sym_inv inversa a derecha *)
  Lemma sym_G4 : forall σ, sym_op σ (sym_inv σ) = sym_e.
    intros σ.
    destruct σ as (F, G, inv_FG).
    apply perm_eq.
    simpl.
    apply inv_FG.
    apply inv_FG.
  Qed.
  
  (* El grupo simétrico *)
  Definition Sym : Grupo :=
    mkGrupo
       Permutación  (* carrier *)
       sym_e        (* elemento neutro *)
       sym_op       (* operación binaria *)
       sym_inv      (* inverso *)
       sym_G1           
       sym_G2
       sym_G3
       sym_G4.

End Grupo_Simétrico.

Section Morfismos.

    Variable G H : Grupo.

    Definition es_morfismo (f : carrier G -> carrier H) : Prop :=
          f 1 = 1
      /\  forall x y,  f (x · y) = f x · f y
      /\  forall x,  f x⁻¹ = (f x)⁻¹.
    
    Definition es_monomorfismo (f : carrier G -> carrier H) : Prop :=
      es_morfismo f /\
      forall x y,  f x = f y  ->  x = y.

End Morfismos.

Section Teorema_de_Cayley.

  Variable G : Grupo.
  
  Let X := carrier G.

  (* Dado un x, denota la permutación que multiplica a izquierda por x. *)
  Definition μ (x : X) : Permutación X.
    apply mkPerm with (F := fun y => x·y) (G := fun y => x⁻¹·y).
    split.
      (* F ∘ G = Id *)
      apply functional_extensionality; intros y.
      rewrite <- assoc.
      rewrite inv_r.
      rewrite neut_l.
      reflexivity.
      (* G ∘ F = Id *)
      apply functional_extensionality; intros y.
      rewrite <- assoc.
      rewrite inv_l.
      rewrite neut_l.
      reflexivity.
  Defined.
  
  (* μ es homomórfico para el neutro *)
  Lemma μ_hom_e : μ 1 = (1 : carrier (Sym X)).
    apply perm_eq.
    (* multiplicar_por 1 *)
    apply functional_extensionality.
    intro x; simpl.
    apply neut_l.
    (* multiplicar_por 1⁻¹ *)
    apply functional_extensionality.
    intro x; simpl.
    rewrite inv_1.
    apply neut_l.
  Qed.

  (* μ es homomórfico para el producto *)
  Lemma μ_hom_op : forall x y : X,  μ (x · y) = (μ x : carrier (Sym X)) · μ y.
    intros x y.
    apply perm_eq.
    (* multiplicar por (x · y) *)
    apply functional_extensionality.
    intro z.
    simpl.
    apply assoc.

    (* multiplicar por (x · y)⁻¹ *)
    apply functional_extensionality.
    intro z.
    simpl.
    rewrite inv_xy.
    apply assoc.
  Qed.

  (* μ es homomórfico para el inverso *)
  Lemma μ_hom_inv : forall x : X,  μ (x⁻¹) = (μ x : carrier (Sym X))⁻¹.
    intros x.
    apply perm_eq.

    (* multiplicar por x⁻¹ *)
    apply functional_extensionality.
    intros z.
    simpl.
    reflexivity.

    (* multiplicar por (x⁻¹)⁻¹ *)
    apply functional_extensionality.
    intros z.
    simpl.
    rewrite inv_inv.
    reflexivity.
  Qed.

  Theorem Cayley : exists X : Set,
                   exists f,
                     es_monomorfismo G (Sym X) f.
  Proof.
    exists (carrier G).
    exists μ.
    split.

    (* morfismo *)
    split.
    apply μ_hom_e.   (* homomórfico para el neutro *)
    split.
    apply μ_hom_op.  (* homomórfico para el producto *)
    apply μ_hom_inv. (* homomórfico para el inverso *)

    (* monomorfismo *)
    intros x y permx_eq_permy.
    replace x with (F _ (μ x) 1).
    replace y with (F _ (μ y) 1).
    rewrite permx_eq_permy.
    reflexivity.
    simpl. apply neut_r.
    simpl. apply neut_r.
  Qed.

End Teorema_de_Cayley.

