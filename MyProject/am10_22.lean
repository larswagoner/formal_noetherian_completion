import MyProject.am7_6
import MyProject.am10_15
import MyProject.AssociatedGradedRing.Module
import MyProject.AssociatedGradedRing.SurjectiveMap
-- import MyProject.AssociatedGradedRing.Components

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

instance : IsNoetherianRing (GradedRingPiece I 0) := sorry

lemma whatever₂ : Module.Finite (GradedRingPiece I 0) (GradedRingPiece I 1) := sorry

lemma GradedRingPiece_FG_of_Noetherian : (⊤ : Submodule (GradedRingPiece I 0) (GradedRingPiece I 1)).FG := sorry

/-- 
  Given `I`, outputs the polynomial ring with scalars in `GradedRingPiece I 0` and variables indexed by the generators of `GradedRingPiece I 1` over the scalars.
  -/
def AssociatedPolynomialRing :  Type u := (MvPolynomial (GradedRingPiece_FG_of_Noetherian I).choose (GradedRingPiece I 0))

/- Polynomial ring is Noetherian-/
noncomputable instance : Semiring (AssociatedPolynomialRing I) := by
  unfold AssociatedPolynomialRing
  infer_instance

noncomputable instance : CommRing (AssociatedPolynomialRing I) := by
  unfold AssociatedPolynomialRing
  infer_instance

instance : IsNoetherianRing (AssociatedPolynomialRing I) := by
  unfold AssociatedPolynomialRing
  infer_instance

/- Defining map from polynomial ring to associated graded ring
  some useful theorems from mathlib
   DirectSum.ofZeroRingHom (GradedPiece (CanonicalFiltration I)) 
   DirectSum.of (GradedPiece (CanonicalFiltration I)) 0 
  -/
--lemma zeroeth_graded_piece : (GradedPiece (CanonicalFiltration I) 0) = (A ⧸ I) := sorry



def scalar_morphism : GradedRingPiece I 0 →+* AssociatedGradedRing I where
  __ := DirectSum.of _ _
  map_one' := by simp 
  map_mul' := by simp

def variable_morphism : (GradedRingPiece_FG_of_Noetherian I).choose → AssociatedGradedRing I := fun ⟨x, _⟩ => DirectSum.of _ 1 x

def MvMorphism : (AssociatedPolynomialRing I) →+* (AssociatedGradedRing I) := MvPolynomial.eval₂Hom (scalar_morphism I) (variable_morphism I)


lemma MvMorphism_surjective : Function.Surjective ⇑(MvMorphism I) := by
  apply AssociatedGradedRing.hom_surjective_of_eq_of_eq (MvMorphism I)
  · ext x
    simp
    unfold MvMorphism
    use MvPolynomial.C x
    have := MvPolynomial.eval₂Hom_C (scalar_morphism I) (variable_morphism I) x
    exact this
    
  · ext x
    simp
    have h₁ : x ∈ Submodule.span (GradedRingPiece I 0) (GradedRingPiece_FG_of_Noetherian I).choose := by
      rw [(GradedRingPiece_FG_of_Noetherian I).choose_spec]
      simp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h₁
    · intro x hx
      use MvPolynomial.X ⟨x, hx⟩
      have := MvPolynomial.eval₂Hom_X' (scalar_morphism I) (variable_morphism I) ⟨x, hx⟩
      unfold MvMorphism
      exact this
    · use 0
      simp
    · intro _ _ _ _ ⟨a , ha⟩ ⟨ b, hb⟩ 
      use a + b
      simp
      rw[ha, hb]
    · intro a x hx ⟨p , hp ⟩
      let a_poly : AssociatedPolynomialRing I := MvPolynomial.C a
      use a_poly * p
      simp
      rw [hp]
      unfold a_poly
      have := MvPolynomial.eval₂Hom_C (scalar_morphism I) (variable_morphism I) a
      congr 1

/-- Associated Graded Ring of a Noetherian Ring is Noetherian-/
instance am10_22_i {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  IsNoetherianRing (AssociatedGradedRing I) := isNoetherianRing_of_surjective (AssociatedPolynomialRing I) (AssociatedGradedRing I) (MvMorphism I) (MvMorphism_surjective I)




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
