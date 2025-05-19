import MyProject.am7_6
import MyProject.am10_15
import MyProject.AssociatedGradedRing.Module
import MyProject.AssociatedGradedRing.SurjectiveMap
import MyProject.AssociatedGradedRing.Components

/-
  # Proposition 10.22
  Let `A` be a Noetherian ring and `a` an ideal of `A`. Then
  i) `Gₐ(A)` is Noetherian.
  ii) `Gₐ(A)` and `Gₐ(Â)` are isomorphic as graded rings.
  iii) If `M` is a finitely-generated `A`-module and `(Mₙ)` is a stable `a`-filtration of `M`,
      then `G(M)` is a finitely-generated graded `Gₐ(A)`-module.
-/

variable {A : Type u} [CommRing A] [hNA: IsNoetherianRing A] (I : Ideal A)


instance : IsNoetherianRing (A ⧸ I) := by
  infer_instance

instance : IsNoetherianRing (GradedRingPiece I 0) := 
  isNoetherianRing_of_ringEquiv (A ⧸ I) (GradedRingPiece_zero_isomorphism I)

instance : Module.Finite A I := by infer_instance
instance : Module (GradedRingPiece I 0) (GradedRingPiece I 1) := by infer_instance


def σ : A →+* (A ⧸ I) where
  toFun := Submodule.Quotient.mk
  map_one' := by simp 
  map_mul' := by simp 
  map_zero' := by simp 
  map_add' := by simp

instance : RingHomSurjective (σ I) := by
  refine { is_surjective := ?_ }
  apply Quotient.mk''_surjective


def auxf₂ : ↥(I^1) →ₛₗ[σ I] (↥(I^1) ⧸ I • (⊤ : Submodule A ↥(I^1))) where
  toFun := Submodule.Quotient.mk
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

instance : Module.Finite (A ⧸ I) (↥(I^1) ⧸ I • (⊤ : Submodule A ↥(I^1))) := by
  apply Module.Finite.of_surjective (auxf₂ I) _
  apply Quotient.mk''_surjective


def σ₂ : (A ⧸ I) →+* GradedRingPiece I 0 := zero_toFun I
instance : RingHomSurjective (σ₂ I) := by 
  refine { is_surjective := ?_ }
  rintro ⟨ b , _⟩
  use b
  rfl

def oneToFun (I : Ideal A) :(↥(I^1) ⧸ I • (⊤ : Submodule A ↥(I^1))) →ₛₗ[σ₂ I] GradedRingPiece I 1 where
  toFun := (GradedRingPiece_m_iso I 1).toFun
  map_add' := by 
    rintro ⟨_⟩ ⟨_⟩ 
    simp
  map_smul' := by
    rintro ⟨_⟩ ⟨_⟩ 
    rfl

instance : Module.Finite (GradedRingPiece I 0) (GradedRingPiece I 1) := by
  apply (LinearMap.finite_iff_of_bijective (oneToFun I) _).mp
  · exact instFiniteQuotientIdealSubtypeMemHPowNatOfNatSubmoduleHSMulTop_myProject I
  · exact GradedRingPiece_m_iso.bijective I 1
   

lemma GradedRingPiece_FG_of_Noetherian : (⊤ : Submodule (GradedRingPiece I 0) (GradedRingPiece I 1)).FG := Module.Finite.fg_top


noncomputable abbrev vars : Finset (GradedRingPiece I 1) := (GradedRingPiece_FG_of_Noetherian I).choose

def embedding : vars I → GradedRingPiece I 1 := by
  rintro ⟨x, hx⟩
  refine ⟦?_⟧ₘ
  sorry

/-- 
  Given `I`, outputs the polynomial ring with scalars in `GradedRingPiece I 0` and variables indexed by the generators of `GradedRingPiece I 1` over the scalars.
-/



/- Polynomial ring is Noetherian-/
instance : IsNoetherianRing (AssociatedGradedRing.AssociatedPolynomialRing I (vars I)) := by
  infer_instance


abbrev scalar_morphism : GradedRingPiece I 0 →+* AssociatedGradedRing I := AssociatedGradedRing.scalar_morphism I

def scalar_morphism₂ : GradedRingPiece I 0 →+* AssociatedGradedRing I where
  __ := DirectSum.of _ _
  map_one' := by simp 
  map_mul' := by simp



--def variable_morphism : (vars I) → AssociatedGradedRing I := AssociatedGradedRing.variable_morphism 
def variable_morphism : (vars I) → AssociatedGradedRing I := fun ⟨x, _⟩ => DirectSum.of _ 1 x


-- call from surjective map
def MvMorphism : (AssociatedGradedRing.AssociatedPolynomialRing I (vars I)) →+* (AssociatedGradedRing I) := 
  MvPolynomial.eval₂Hom (scalar_morphism I) (variable_morphism I)

-- call from surjective map
lemma MvMorphism_surjective : Function.Surjective ⇑(MvMorphism I) := by
  apply AssociatedGradedRing.hom_surjective_of_eq_of_eq _
  · ext x
    simp
    have h₁ : x ∈ Submodule.span (GradedRingPiece I 0) (vars I) := by
      unfold vars
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
      let a_poly : AssociatedGradedRing.AssociatedPolynomialRing I (vars I) := MvPolynomial.C a
      use a_poly * p
      simp
      rw [hp]
      unfold a_poly
      have := MvPolynomial.eval₂Hom_C (scalar_morphism I) (variable_morphism I) a
      congr 1
  · sorry/-ext x -- this is screwed up after changeing scalar_morphism to one in AssociatedGradedRing.scalar_morphism I
    simp
    unfold MvMorphism
    use MvPolynomial.C x
    have := MvPolynomial.eval₂Hom_C (scalar_morphism I) (variable_morphism I) x
    exact this-/
  

/-- Associated Graded Ring of a Noetherian Ring is Noetherian-/
instance am10_22_i {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  IsNoetherianRing (AssociatedGradedRing I) := 
    isNoetherianRing_of_surjective (AssociatedGradedRing.AssociatedPolynomialRing I (vars I)) (AssociatedGradedRing I) (MvMorphism I) (MvMorphism_surjective I)




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