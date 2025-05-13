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

-- construct Polynomial ring over GRP I 0  with variables indexed by generators of GRP I 1, construct surjective morphism, show GRP I 0 noetherian hence polynomial ring is, thus codomain is

variable {A : Type u} [CommRing A] [hNA: IsNoetherianRing A] (I : Ideal A)

instance : IsNoetherianRing (A ⧸ I) := by
  infer_instance

instance : IsNoetherianRing (GradedRingPiece I 0) := isNoetherianRing_of_ringEquiv (A ⧸ I) (GradedRingPiece_zero_isomorphism I)

instance : Module.Finite A I := by infer_instance

--def help : ∃ S, Submodule.span (A ⧸ I) S = (I ⧸ I • (⊤ : Submodule A I) ) := sorry
-- LinearMap.finite_iff_of_bijective
-- Module.Finite.of_surjective
-- R = A, M = I, S = A/I, P = I/I•⊤

 



def σ : A →+* (A ⧸ I) where
  toFun := Submodule.Quotient.mk
  map_one' := by simp 
  map_mul' := by simp 
  map_zero' := by simp 
  map_add' := by simp

instance : RingHomSurjective (σ I) := by
  refine { is_surjective := ?_ }
  apply Quotient.mk''_surjective

def aux₁ : I → (I ⧸ I • (⊤ : Submodule A I) ) := Submodule.Quotient.mk

def auxf₁ : I →ₛₗ[σ I] (I ⧸ I • (⊤ : Submodule A I) ) where
  toFun := aux₁ I
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl


instance : Module.Finite (A ⧸ I) (I ⧸ I • (⊤ : Submodule A I) ) := by
  apply Module.Finite.of_surjective (auxf₁ I) _
  apply Quotient.mk''_surjective


def σ₂ : A →+* GradedRingPiece I 0 := sorry
instance : RingHomSurjective (σ₂ I) := sorry



instance : Module.Finite (GradedRingPiece I 0) (GradedRingPiece I 1) := by
  apply (LinearMap.finite_iff_of_bijective (auxf I) _).mpr
  sorry

lemma GradedRingPiece_FG_of_Noetherian : (⊤ : Submodule (GradedRingPiece I 0) (GradedRingPiece I 1)).FG := Module.Finite.fg_top

-- alternative approach, directly get finset of generators via I.

noncomputable def I_generators : Finset A := (((isNoetherianRing_iff_ideal_fg A).mp) hNA I).choose



lemma hs : Submodule.span A (((isNoetherianRing_iff_ideal_fg A).mp) hNA I).choose = I := (((isNoetherianRing_iff_ideal_fg A).mp) hNA I).choose_spec

-- 
def final_gens : true := sorry

--lemma xx : Submodule.span (GradedRingPiece I 0) final_gens = (GradedRingPiece I 1) := sorry


noncomputable def I_generators_in_I : Finset I := sorry


-- would be nice to have if S generates I, then it generates I/I^2, over A and A/I
noncomputable def  ImodIsq_generators :  Finset (I/I^2) := by
  have I_gens := I_generators_in_I I
  --apply (Finset.image (Submodule.Quotient.mk _ (I^2)) I_gens)

  sorry

noncomputable def vars : Finset (GradedRingPiece I 1) := (GradedRingPiece_FG_of_Noetherian I).choose



/-- 
  Given `I`, outputs the polynomial ring with scalars in `GradedRingPiece I 0` and variables indexed by the generators of `GradedRingPiece I 1` over the scalars.
  -/
def AssociatedPolynomialRing :  Type u := (MvPolynomial (vars I) (GradedRingPiece I 0))

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


def scalar_morphism : GradedRingPiece I 0 →+* AssociatedGradedRing I where
  __ := DirectSum.of _ _
  map_one' := by simp 
  map_mul' := by simp

def variable_morphism : (vars I) → AssociatedGradedRing I := fun ⟨x, _⟩ => DirectSum.of _ 1 x

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
