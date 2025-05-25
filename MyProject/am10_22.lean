import MyProject.am7_6
import MyProject.am10_15
import MyProject.AssociatedGradedRing.Module
import MyProject.AssociatedGradedRing.SurjectiveMap
import MyProject.AssociatedGradedRing.Components
import MyProject.AssociatedGradedRing.Algebra

/-
  # Proposition 10.22
  Let `A` be a Noetherian ring and `a` an ideal of `A`. Then
  i) `Gₐ(A)` is Noetherian.
  ii) `Gₐ(A)` and `Gₐ(Â)` are isomorphic as graded rings.
  iii) If `M` is a finitely-generated `A`-module and `(Mₙ)` is a stable `a`-filtration of `M`,
      then `G(M)` is a finitely-generated graded `Gₐ(A)`-module.
-/

variable {A : Type u} [hCA : CommRing A] [hNA: IsNoetherianRing A] (I : Ideal A) {R : Type u} [CommRing R]


/-- Copyright (c) 2022 Christian Merten-/
lemma Ideal.mem_span_pow' {n : ℕ} (S : Set R) (x : R) :
    x ∈ (Ideal.span S) ^ n ↔ ∃ (p : MvPolynomial S R),
      MvPolynomial.IsHomogeneous p n ∧ MvPolynomial.eval Subtype.val p = x := sorry
/- end of copyright -/


noncomputable def ideal_generators : Set A := (IsNoetherian.noetherian I).choose


instance : IsNoetherianRing (MvPolynomial (ideal_generators I) A) := by
  dsimp [ideal_generators]
  infer_instance


def scalars₁_aux : A →+ (CanonicalFiltration I).N 0 := zero_toFun_aux₁ I

def scalars₁ : A →+* GradedRingPiece I 0 where
  toFun := Submodule.Quotient.mk ∘ scalars₁_aux I
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def scalar_morph : A →+* AssociatedGradedRing I where
  toFun := DirectSum.of _ 0 ∘ scalars₁ I
  map_one' := rfl
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp




def ideal_generator_mem (a : A) (ha: a ∈ ideal_generators I) : a ∈ I := by
  have : Submodule.span A (ideal_generators I) = I := (IsNoetherian.noetherian I).choose_spec
  rw[← this] 
  exact Submodule.mem_span.mpr fun p a_1 ↦ a_1 ha

def oneaux₁ : ideal_generators I → ↥(I) := fun ⟨a, ha⟩ => ⟨a, ideal_generator_mem I a ha⟩

def oneaux₂ : ↥(I) → (CanonicalFiltration I).N 1 := fun x => ⟨x, by simp⟩

def oneaux₃ : (CanonicalFiltration I).N 1 → AssociatedGradedRing I :=  DirectSum.of _ 1 ∘ Submodule.Quotient.mk 

def var_morph : ideal_generators I → AssociatedGradedRing I := fun x =>  ((oneaux₃ I) ∘ (oneaux₂ I) ∘ (oneaux₁ I)) x



def φ (I : Ideal A): (MvPolynomial (↑(ideal_generators I)) A) →ₐ[A] AssociatedGradedRing I :=   MvPolynomial.aeval (var_morph I)

def ideal_to_GRP (n:ℕ) : ↥(I ^ n) → GradedRingPiece I n := (Submodule.Quotient.mk ∘ (Taux I n))



lemma poly_homog_of_not_deg (n k : ℕ) (hkn : k ≠ n) (y : MvPolynomial (↑(ideal_generators I)) A) (hIy : (MvPolynomial.eval Subtype.val) y ∈ I^n) {hy : MvPolynomial.IsHomogeneous y n}  : ((MvPolynomial.aeval (var_morph I)) y) k = 0 := by
  have h₅ := (MvPolynomial.mem_homogeneousSubmodule n y).mpr hy
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported _ _] at h₅
  
  
  have h₆ : (MvPolynomial.homogeneousComponent k) y  = 0 := by
    refine MvPolynomial.homogeneousComponent_eq_zero' k y ?_
    intro d hd
    exact Lean.Grind.ne_of_ne_of_eq_left (h₅ hd) (id (Ne.symm hkn))
  have h₇ : (MvPolynomial.aeval (var_morph I)) ((MvPolynomial.homogeneousComponent k) y) = 0 := by rw[h₆, map_zero]
  

  -- maybe this is enough?
 -- have h₉ : ((MvPolynomial.aeval (var_morph I)) ((MvPolynomial.homogeneousComponent k) y) ) = DirectSum.of _ k (((MvPolynomial.aeval (var_morph I)) y) k) :=  sorry



  have h₈ : ((MvPolynomial.aeval (var_morph I)) y) k = (DirectSum.component A _ _ k ((MvPolynomial.aeval (var_morph I)) ((MvPolynomial.homogeneousComponent k) y) )) := by
    --rw[h₉]
    -- seems like DS.component and DS.of should cancel eachother out
    
    sorry
  
  rw [h₈, h₇, map_zero]


--- notes: 
-- look at theorem MvPolynomial.IsHomogeneous.add for proving that mul by x increases degree by 1
-- would be nice to have ((MvPolynomial.aeval (var_morph I)) y) i =( aeval _ homogcomponent y i) proj i
 -- theorem MvPolynomial.IsHomogeneous.coeff_eq_zero seem super great!
    -- MvPolynomial.homogeneousComponent_eq_zero'
    -- MvPolynomial.homogeneousComponent_of_mem {σ : Type u_1} {R : Type u_3} [CommSemiring R] us this one then eval 0 = 0

  -- DirectSum.of_eq_of_ne useful


lemma φ.Surjective : Function.Surjective (φ I) := by
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · use 0
    simp
  · rintro n x
    obtain  ⟨⟨z,hz⟩, rfl⟩ := Submodule.mkQ_surjective _  x 
    simp at hz
    have h₁ : I = Ideal.span (ideal_generators I) := (IsNoetherian.noetherian I).choose_spec.symm
    rw [h₁] at hz
    have ⟨y, hy₁, hy₂⟩ := (@Ideal.mem_span_pow' A hCA n (ideal_generators I) z).mp hz

    use y    
    unfold φ
 
    rw[← hy₂, ← h₁] at hz

  
    have h₃: (MvPolynomial.aeval (var_morph I)) y  = (DirectSum.of (GradedPiece (CanonicalFiltration I)) n) (ideal_to_GRP I n ⟨((MvPolynomial.eval Subtype.val) y), hz⟩) := by
      --dsimp [ideal_to_GRP, Taux]
      apply DirectSum.ext
      intro k
      by_cases hkn : k = n
      · subst hkn
        simp [DirectSum.of_eq_same]
        /-
       
        have : (MvPolynomial.aeval (var_morph I)) y ∈ GradedRingPiece I n := 
          aeval_homogeneous_in_component n y hy₁
        
        sorry
       
        
       -- rw [hkn]
       -- simp
        induction y using MvPolynomial.induction_on 
        · --by_cases hazero : a✝ = 0

          sorry
        · sorry
        · sorry
        induction' n with n ih
        ·sorry
        · sorry
         -/
        sorry
      · rwa [DirectSum.of_eq_of_ne n k _ (id (Ne.symm hkn)), ← poly_homog_of_not_deg I n k hkn y hz]
     
  
      --induction y using MvPolynomial.induction_on -- maybe not induction here now. induction outside of homogeneous setting
    
    simp [h₃, ideal_to_GRP, Taux, hy₂]

  
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    use a+b
    rw [map_add, ha, hb]


instance am10_22_i {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] : IsNoetherianRing (AssociatedGradedRing I) := by 
  exact isNoetherianRing_of_surjective (MvPolynomial (ideal_generators I) A) (AssociatedGradedRing I) (φ I) (φ.Surjective I)


noncomputable def am10_22_ii {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
    AssociatedGradedRing I ≃+* AssociatedGradedRing (I.adicCompletion I) :=
  AssociatedGradedRingIso_of_grp_iso (am10_15_iii_commute I)

instance am10_22_iii {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {F : I.Filtration M} (hF : F.Stable) :
    Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F) := sorry