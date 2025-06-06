import MyProject.AssociatedGradedRing.Map
import Mathlib.RingTheory.MvPolynomial.Homogeneous


import MyProject.am7_6
import MyProject.am10_15
import MyProject.AssociatedGradedRing.Module
import MyProject.AssociatedGradedRing.Components

namespace AssociatedGradedRing

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] {I : Ideal A} {φ : R →+* AssociatedGradedRing I}

/-- Copyright (c) 2022 Christian Merten-/
lemma Ideal.mem_span_pow' {n : ℕ} (S : Set R) (x : R) :
    x ∈ (Ideal.span S) ^ n ↔ ∃ (p : MvPolynomial S R),
      MvPolynomial.IsHomogeneous p n ∧ MvPolynomial.eval Subtype.val p = x := sorry
/- end of copyright -/


/- SECTION I -/
universe u v w

variable {vars : Type v} {embedding : vars → GradedRingPiece I 1}  {embedded_vars_generate : Submodule.span (GradedRingPiece I 0) (Set.range embedding) = ⊤} {identification₂ : vars → (CanonicalFiltration I).N 1} {identification : vars → I} {compatibility : embedding = GradedPiece_mk ∘ identification₂} {identified_vars_generate : Submodule.span A (Set.range identification) = ⊤}

abbrev AssociatedPolynomialRing (I : Ideal A) (vars : Type v) : Type (max u v) := MvPolynomial (vars) (GradedRingPiece I 0)

noncomputable instance : Semiring (AssociatedPolynomialRing I vars) := by
  unfold AssociatedPolynomialRing
  infer_instance

noncomputable instance : CommRing (AssociatedPolynomialRing I vars) := by
  unfold AssociatedPolynomialRing
  infer_instance


def scalar_morphism (I : Ideal A): GradedRingPiece I 0 →+* AssociatedGradedRing I where
  __ := DirectSum.of _ _
  map_one' := by simp 
  map_mul' := by simp


def variable_morphism (embedding : vars → GradedRingPiece I 1): (vars) → AssociatedGradedRing I := DirectSum.of _ 1 ∘ embedding

def MvMorphism (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1) : 
    (AssociatedPolynomialRing I vars) →+* (AssociatedGradedRing I) := 
      MvPolynomial.eval₂Hom (scalar_morphism I) (variable_morphism embedding)


/- `A/I[yᵢ] → G(A)` is surjective -/
/- APPROACH 1-/
def AuxiliaryPolynomialRing (A : Type u) [CommRing A] (vars : Type v):= MvPolynomial vars A

noncomputable instance : Semiring (AuxiliaryPolynomialRing A vars) := by
  unfold AuxiliaryPolynomialRing
  infer_instance
noncomputable instance : CommRing (AuxiliaryPolynomialRing A vars) :=  by
  unfold AuxiliaryPolynomialRing
  infer_instance


-- `φ : A[xᵢ] → AssociatedPolynomialRing I vars`
def aux_constant_morphism (I : Ideal A) : A →+* GradedRingPiece I 0 where
  toFun := GradedPiece_mk ∘ zero_toFun_aux₁ I
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


noncomputable def constant_map_phi : A →+* AssociatedPolynomialRing I vars where
  toFun := MvPolynomial.C ∘ (aux_constant_morphism I)
  map_one' := rfl
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

noncomputable def phi (I: Ideal A) (vars : Type v) : (AuxiliaryPolynomialRing A vars) →+* (AssociatedPolynomialRing I vars) :=  MvPolynomial.eval₂Hom (constant_map_phi) MvPolynomial.X



-- `ψ : A[xᵢ] → AssociatedGradedRing I`
def constant_map_psi : A →+* AssociatedGradedRing I where
  toFun := (scalar_morphism I) ∘ (zero_toFun I)∘ (Ideal.Quotient.mk I)
  map_one' := rfl
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add'  _ _ := by simp

def psi (I: Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1): AuxiliaryPolynomialRing A vars →+* AssociatedGradedRing I := MvPolynomial.eval₂Hom constant_map_psi (variable_morphism embedding)

/- `ψ` surjective (use Christian's lemma) -/
lemma psi.Surjective (I: Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1): Function.Surjective (psi I vars embedding) := by
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · use 0 
    rfl
  · intro n
    rintro ⟨a, ha⟩ 
    simp
    have := (@Ideal.mem_span_pow' A _ n (⊤) a).mp sorry
    rcases this with ⟨p, p₁, p₂⟩
    
    have : (⟨a, ha⟩ : (CanonicalFiltration I).N n) = ⟨(MvPolynomial.eval Subtype.val) p, by sorry⟩ :=  Subtype.mk_eq_mk.mpr ((Eq.symm p₂))
    rw[this]
    
    sorry
  · intro r s ⟨c, hc⟩ ⟨d, hd⟩
    use (c + d)
    simp only [map_add]
    rw [hc, hd]
    

/- `MvMorphism I vars embedding ∘ φ = ψ` -/

lemma auxiliary_composition: psi I vars embedding = (MvMorphism I vars embedding) ∘ (phi I vars) := by
  ext b
  simp
  unfold psi phi MvMorphism
  simp
  unfold constant_map_psi constant_map_phi
  
  
  sorry


/- `MvMorphism I vars embedding` surjective -/
lemma MvMorphism.Surjective (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1) : Function.Surjective ⇑(MvMorphism I vars embedding) := by
  have h₁ : psi I vars embedding = (MvMorphism I vars embedding) ∘ (phi I vars) := by
    rw [auxiliary_composition]
  have h₂: Function.Surjective ((MvMorphism I vars embedding) ∘ (phi I vars)) := by 
    rw[← h₁]
    exact psi.Surjective I vars embedding

  exact Function.Surjective.of_comp h₂


/- APPROACH 2 -/

lemma MvMorphism.Surjective₂ (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1) : Function.Surjective ⇑(MvMorphism I vars embedding) := by
  unfold Function.Surjective
  intro x

  refine DirectSum.induction_on x ?_ ?_ ?_
  · use 0 
    simp only [map_zero]
  · intro n y
    let z' := ((GradedRingPiece_m_iso I n).symm.toFun) y
    have hy : ((GradedRingPiece_m_iso I n).toFun) z' = y := by
      unfold z'
      simp
    rw[← hy]
    simp
    let z:= z'.out


    sorry
  · rintro y z ⟨a, ha⟩ ⟨b, hb⟩
    use a + b
    simp only [map_add]
    rw [ha, hb]


/- SECTION II -/
noncomputable instance : Algebra (GradedRingPiece I 0) (AssociatedPolynomialRing I vars) := by
  infer_instance


instance GRPalg1 : Algebra (GradedRingPiece I 0) (AssociatedGradedRing I) where
  smul a x := (scalar_morphism I a)*x
  algebraMap := scalar_morphism I
  commutes' r x := CommMonoid.mul_comm ((scalar_morphism I) r) x
  smul_def' _ _ := rfl


noncomputable instance GRPalg2 : Algebra (GradedRingPiece I 0) (AssociatedGradedRing I) where
  smul a x := (MvMorphism I vars embedding (MvPolynomial.C a)) * x
  algebraMap := sorry -- ∘ (MvMorphism I vars embedding)
  commutes' := sorry
  smul_def' := sorry



noncomputable def var_aux₁ : vars → AssociatedPolynomialRing I vars := MvPolynomial.X


/-- `G(A)` as `A/I`-algebra is generated by images of `xᵢ` -/
-- pull back via MvMorphism with Algebra.mem_adjoin_of_map_mul, have AssociatedPolynomial Ring I (vars) as A/I algebra
def f (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1)  :  (AssociatedPolynomialRing I vars) →ₗ[GradedRingPiece I 0] (AssociatedGradedRing I) := sorry


lemma AssociatedGradedRing_generated (embedding : vars → GradedRingPiece I 1): Algebra.adjoin (GradedRingPiece I 0) (⇑(f I vars embedding)'' (((MvPolynomial.X)'' (Set.univ : Set vars)) ∪ {1})) = ⊤ := by
  ext x
  simp only [Set.image_univ, Set.union_singleton, Algebra.mem_top, iff_true]
  have ⟨a, ha⟩ := MvMorphism.Surjective I vars embedding x
  rw[← ha]
  sorry

lemma AssociatedGradedRing_generated₂ (embedding : vars → GradedRingPiece I 1) : Algebra.adjoin (GradedRingPiece I 0) (Set.range (variable_morphism embedding)) = ⊤ := by
  ext x
  simp
  have ⟨a, ha⟩ := MvMorphism.Surjective I vars embedding x
  rw[← ha]
  unfold MvMorphism
  simp

  sorry
  
  

def AssociatedGradedRing_generated₃ (embedding : vars → GradedRingPiece I 1): 
    Algebra.adjoin (GradedRingPiece I 0) (Set.range (variable_morphism embedding)) ≃ₐ[GradedRingPiece I 0] AssociatedGradedRing I := sorry



/- SECTION III -/


lemma hom_surjective_of_eq_of_eq (h₀ : (DirectSum.of (GradedRingPiece I) 0) ⁻¹' (φ '' ⊤) = ⊤) 
    (h₁ :(DirectSum.of (GradedRingPiece I) 1) ⁻¹' (φ '' ⊤) = ⊤) {embedding : vars → GradedRingPiece I 1} : Function.Surjective φ := by

  unfold Function.Surjective
  let h₃ := AssociatedGradedRing_generated₃ embedding
  intro b
  let z := h₃.symm b
  have hb : (h₃).toAlgHom z = b :=
    by exact h₃.apply_symm_apply b
  rw[← hb]
      
  sorry



end AssociatedGradedRing 