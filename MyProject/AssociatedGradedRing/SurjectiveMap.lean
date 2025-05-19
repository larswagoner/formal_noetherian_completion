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



/-
--okey doke, here is the plan. Let vars be a set of generators of I (variable), construct map from polynomial ring to associated graded ring, show that this one is surjective (maybe the map can be given by eval polynomial) using chris' lemma. Then as a corrollary we have finiteness as algebra, then we can deduce main lemma. this is all independent of noetherian ness. so in am_10_22.lean we import this file, and then use as input the finite generating set.

Pracitcally, this lemma wont be used in 10_22.... right? i guess we could keep it, or we could use the surjection from polynomial ring directly... can decide later.

-/


/- SECTION I -/
universe u v w

variable {vars : Type v} {embedding : vars → GradedRingPiece I 1}  {vars_generate : Submodule.span (GradedRingPiece I 0) (Set.range embedding) = ⊤} {identification : vars → (CanonicalFiltration I).N 1} {compatibility : embedding = GradedPiece_mk ∘ identification}
-- might need to add vars → I or I^1 or (CanonicalFiltration I).N 1 then a proof that that and embedding commute

-- when applying this in am_10_22.lean, choose vars wisely... probably in terms of generators of GRP 1, if i want to do stuff with `A[xᵢ]` use generators of (CanonicalFiltration I).N 1

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

/- `A/I[xᵢ] → G(A)` is surjective -/

-- have vars be a subset of I? or first embed in I then in GRP 1?

/- APPROACH 1-/

def AuxiliaryPolynomialRing (A : Type u) [CommRing A] (vars : Type v):= MvPolynomial vars A

-- `φ : A[xᵢ] → AssociatedPolynomialRing I vars`


--zero_toFun_aux₁ : A →+ (CanonicalFiltration I).N 0 

def aux_scalar_morphism (I : Ideal A) : A →+* GradedRingPiece I 0 where
  toFun := GradedPiece_mk ∘ zero_toFun_aux₁ I
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


noncomputable def phi (I: Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1): (AuxiliaryPolynomialRing A vars) → (AssociatedPolynomialRing I vars) := by
  refine MvPolynomial.eval₂ ?_ MvPolynomial.X
  · --exact MvPolynomial.C ∘ (aux_scalar_morphism₂ I)
    
    sorry -- first go to GRP 0 via iso, then do scalar morphism 
 


#check DirectSum.of _ 0 ∘ (aux_scalar_morphism I)

-- `ψ : A[xᵢ] → AssociatedGradedRing I`
def psi (I: Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1): AuxiliaryPolynomialRing A vars → AssociatedGradedRing I := by
  refine MvPolynomial.eval₂ ?_ (variable_morphism embedding)

  -- zero_toFun_aux₁ composed with the direct sum of?
  sorry

-- `μ : AssociatedPolynomialRing I vars → AssociatedGradedRing := MvMorphism I vars embedding`


/- `ψ` surjective (use Christian's lemma) -/
def psi.Surjective (I: Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1): Function.Surjective (psi I vars embedding) := sorry

/- `μ ∘ φ = ψ` -/
def auxiliary_composition (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1) : psi I vars embedding = (MvMorphism I vars embedding) ∘ (phi I vars embedding) := sorry


/- `μ` surjective -/
lemma MvMorphism.Surjective (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1) : Function.Surjective ⇑(MvMorphism I vars embedding) := by
  have h₁ : psi I vars embedding = (MvMorphism I vars embedding) ∘ (phi I vars embedding) := by
    rw [auxiliary_composition I vars embedding]
  have h₂: Function.Surjective ((MvMorphism I vars embedding) ∘ (phi I vars embedding)) := by 
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

-- maybe define this in terms of MvMorphism... or doesnt matter. 
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


--- scratch
noncomputable def var_aux₁ : vars → AssociatedPolynomialRing I vars := MvPolynomial.X

-- S is MvPolynomial''(vars)
-- f is MvMorphism
--- end of scratch


/-- `G(A)` as `A/I`-algebra is generated by images of `xᵢ` -/
-- pull back via MvMorphism with Algebra.mem_adjoin_of_map_mul, have AssociatedPolynomial Ring I (vars) as A/I algebra
def f (I : Ideal A) (vars : Type v) (embedding : vars → GradedRingPiece I 1)  :  (AssociatedPolynomialRing I vars) →ₗ[GradedRingPiece I 0] (AssociatedGradedRing I) := sorry


lemma AssociatedGradedRing_generated (embedding : vars → GradedRingPiece I 1): Algebra.adjoin (GradedRingPiece I 0) (⇑(f I vars embedding)'' (((MvPolynomial.X)'' (Set.univ : Set vars)) ∪ {1})) = ⊤ := by
  ext x
  simp only [Set.image_univ, Set.union_singleton, Algebra.mem_top, iff_true]
  have ⟨a, ha⟩ := MvMorphism.Surjective I vars embedding x
  rw[← ha]
/-
  apply Algebra.mem_adjoin_of_map_mul (GradedRingPiece I 0) 
  · sorry
  · sorry
 
   
  #check @Algebra.mem_adjoin_of_map_mul (GradedRingPiece I 0) (AssociatedPolynomialRing I vars) (AssociatedGradedRing I) _ _ _ _ (((MvPolynomial.X)'' (Set.univ : Set vars))) _ _ (f I vars embedding) _ _  
  apply @Algebra.mem_adjoin_of_map_mul (GradedRingPiece I 0) (AssociatedPolynomialRing I vars) (AssociatedGradedRing I) _ _ _ _ (((MvPolynomial.X)'' (Set.univ : Set vars))) _ _ (f I vars embedding) _ _  
 
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  -/

  --refine @Algebra.mem_adjoin_of_map_mul (GradedRingPiece I 0) (AssociatedPolynomialRing I vars) (AssociatedGradedRing I) {f I vars embedding} ?_ ?_
  /-
  
  refine Algebra.mem_adjoin_of_map_mul (GradedRingPiece I 0) ?_ ?_ 
  · sorry
  · sorry

-/

 -- exact Algebra.mem_adjoin_of_map_mul (GradedRingPiece I 0)  _ _
  sorry

lemma AssociatedGradedRing_generated₂ (embedding : vars → GradedRingPiece I 1) : Algebra.adjoin (GradedRingPiece I 0) (Set.range (variable_morphism embedding)) = ⊤ := by
  ext x
  simp
  have ⟨a, ha⟩ := MvMorphism.Surjective I vars embedding x
  rw[← ha]
  unfold MvMorphism
  simp

  sorry
  
  

def AssociatedGradedRing_generated₃ (embedding : vars → GradedRingPiece I 1): Algebra.adjoin (GradedRingPiece I 0) (Set.range (variable_morphism embedding)) ≃ₐ[GradedRingPiece I 0] AssociatedGradedRing I := by 
  --rw[AssociatedGradedRing_generated embedding₃]
  --exact Subalgebra.topEquiv
  sorry



/- SECTION III -/

-- use induction here Algebra.adjoin_induction
lemma hom_surjective_of_eq_of_eq (h₀ : (DirectSum.of (GradedRingPiece I) 0) ⁻¹' (φ '' ⊤) = ⊤) 
    (h₁ :(DirectSum.of (GradedRingPiece I) 1) ⁻¹' (φ '' ⊤) = ⊤) {embedding : vars → GradedRingPiece I 1} : Function.Surjective φ := by

  unfold Function.Surjective
  let h₃ := AssociatedGradedRing_generated₃ embedding
  intro b
  let z := h₃.symm b
  have hb : (h₃).toAlgHom z = b :=
    by exact h₃.apply_symm_apply b

  --- i want to chagne the goal to ∃c such that fφ a = z. so now this is in the subalgebra generated by ... 

  rw[← hb]

  --refine Algebra.adjoin_induction₂ 
  
      
  sorry



end AssociatedGradedRing 