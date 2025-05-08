import MyProject.am7_6
import MyProject.am10_15
import MyProject.AssociatedGradedRing.Module

/-
  # Proposition 10.22
  Let `A` be a Noetherian ring and `a` an ideal of `A`. Then
  i) `Gₐ(A)` is Noetherian.
  ii) `Gₐ(A)` and `Gₐ(Â)` are isomorphic as graded rings.
  iii) If `M` is a finitely-generated `A`-module and `(Mₙ)` is a stable `a`-filtration of `M`,
      then `G(M)` is a finitely-generated graded `Gₐ(A)`-module.
-/

/- Notes for 10.22.i 
Instead of directly following the approach in AM (which relies on an equality involving G(A) which I think will be annoying to make type check), very open for this option if it ends up being easy. I propose the following approach: 

1. Since I is an ideal of a noetherian ring, it is finitely generated, with generating set S : Finset A. 
2. Consider the polynomial ring B = A/I [{x_s}_{s∈ S}], with indeterminates indexed by S. This ring is noetherian since A/I is (quotient) and by Hilberts basis theorem
3. For G(A) to be noetherian, it suffices to give a map B → AssociatedGradedRing I that is a homomorphism and surjective. Such a map is given by sending A/I to the first component I^0/I^1 = A/I, and each variable to the corresponding image of the generator s in the second component I/I^2. 

Progress so far:
The proof is outlined. 
1. Map of scalars: A/I →+* G(A). On paper, we should get this for free with DirectSum.ofZeroRingHom. But the domain for that result needs to be (GradedPiece (CanonicalFiltration I) 0), which is equal to A/I, but one cant just rewrite via this equality. So I have the scalar map as a composition A/I →+* (GradedPiece (CanonicalFiltration I) 0) →+* G(A). Whats missing is the first map, multiplication might be annoying?
2. Map of variables. Mathematically this would be done as so: send a generator s to its equivalence class in I/I^2, then apply the canonical map to end up in G(A) (DirectSum.of (GradedPiece (CanonicalFiltration I)) 1  should work i think)
3. Surjectivity: map needs to be defined first. This will basically amount to proving the equality stated in AM

-/

variable {A : Type u} [CommRing A] [hNA: IsNoetherianRing A] (I : Ideal A)

/- Given an ideal I, returns Polynomial ring over A/I with variables indexed by 
generators of I. Finitely many since A noetherian-/
noncomputable def ideal_to_MvPolynomial : Type u := (MvPolynomial (((isNoetherianRing_iff_ideal_fg A).mp) hNA I).choose (A ⧸ I))

/- Polynomial ring is Noetherian-/
noncomputable instance : Semiring (ideal_to_MvPolynomial I) := by
  unfold ideal_to_MvPolynomial
  infer_instance


noncomputable instance : IsNoetherianRing (ideal_to_MvPolynomial I) := by
  unfold ideal_to_MvPolynomial
  infer_instance

/- Defining map from polynomial ring to associated graded ring
  some useful theorems from mathlib
   DirectSum.ofZeroRingHom (GradedPiece (CanonicalFiltration I)) 
   DirectSum.of (GradedPiece (CanonicalFiltration I)) 0 
  -/
--lemma zeroeth_graded_piece : (GradedPiece (CanonicalFiltration I) 0) = (A ⧸ I) := sorry




#check (CanonicalFiltration I).N 0

def aux1 : A →+ (CanonicalFiltration I).N 0 where
  toFun := (fun a => ⟨ a , by simp ⟩)
  map_zero' := rfl
  map_add' := fun _ _ => rfl





def aux2 : A ⧸ I →+ (GradedPiece (CanonicalFiltration I) 0) := by
  
  --have h₁ : I.toAddSubgroup ≤ AddSubgroup.comap (aux1 I) I.toAddSubgroup := sorry
  apply QuotientAddGroup.map _ _ (aux1 I) _
  · intro x hx
    simp
    exact hx


def zeroeth_morphism : A ⧸ I →+* (GradedPiece (CanonicalFiltration I) 0) where
  toFun := aux2 I
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩ 
    rfl
  map_zero' := AddMonoidHom.map_zero (aux2 I)
  map_add' := fun x y => AddMonoidHom.map_add (aux2 I) x y

def aux_scalar_morphism : (GradedPiece (CanonicalFiltration I) 0) →+* AssociatedGradedRing I := DirectSum.ofZeroRingHom (GradedPiece (CanonicalFiltration I)) 

def scalar_morphism : A ⧸ I →+* AssociatedGradedRing I := (aux_scalar_morphism I).comp (zeroeth_morphism I)

-- Map sending variables to corresponding generator then to image under quotient
noncomputable def auxvar1 : (((isNoetherianRing_iff_ideal_fg A).mp) hNA I).choose → I := by
  intro x
  refine Classical.indefiniteDescription (Membership.mem I) ?_
  sorry


noncomputable def auxvar22 : (I / I ^ 2) → GradedPiece (CanonicalFiltration I) 1 := sorry

noncomputable def auxvar3 :  GradedPiece (CanonicalFiltration I) 1 → AssociatedGradedRing I := fun a ↦ AssociatedGradedRing.of a

noncomputable def variable_morphism : (((isNoetherianRing_iff_ideal_fg A).mp) hNA I).choose → AssociatedGradedRing I := by

  sorry

noncomputable def MvMorphism : (ideal_to_MvPolynomial I) →+* (AssociatedGradedRing I) := MvPolynomial.eval₂Hom (scalar_morphism I) (variable_morphism I)


lemma MvMorphism_surjective : Function.Surjective ⇑(MvMorphism I) := sorry


/-- Associated Graded Ring of a Noetherian Ring is Noetherian-/
instance am10_22_i {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  IsNoetherianRing (AssociatedGradedRing I) := isNoetherianRing_of_surjective (ideal_to_MvPolynomial I) (AssociatedGradedRing I) (MvMorphism I) (MvMorphism_surjective I)





/-
  Note, `I.adicCompletion I` is the `Â`-ideal generated by `I`.
-/

def aux4 (ι : Type*)  (α : ι → Type*) [(i : ι) → AddCommMonoid (α i)]  (β : ι → Type*) [(i : ι) → AddCommMonoid (β i)] : (∀ (i : ι), α i ≃+ β i) → (DirectSum ι α)  ≃+ (DirectSum ι β) := sorry

def aux5 (n:ℕ): (GradedPiece (CanonicalFiltration I) n) ≃+ (GradedPiece (CanonicalFiltration (I.adicCompletion I)) n) := sorry -- use am10_15_iii


/- Need to define AdicCompletion.instCommRing in adic_completion.lean
def aux6 {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  (AssociatedGradedRing I) ≃+ (AssociatedGradedRing (I.adicCompletion I)) := aux4 ℕ (fun n ↦ GradedPiece (CanonicalFiltration I) n) (fun n ↦ GradedPiece (CanonicalFiltration (I.adicCompletion I)) n) fun i ↦ aux5 I i 
-/
  

def am10_22_ii {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  (AssociatedGradedRing I) ≃+* (AssociatedGradedRing (I.adicCompletion I)) := by 
  -- use aux6 above, then prove compatibility with multiplication.
  sorry

instance am10_22_iii {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {F : I.Filtration M} (hF : F.Stable) :
    Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F) := sorry
