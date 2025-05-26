import MyProject.am7_6
import MyProject.am10_15
import MyProject.AssociatedGradedRing.Module
import MyProject.GradedStarRing.SurjectiveMap
import MyProject.GradedStarRing.Algebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-
  # Proposition 10.22
  Let `A` be a Noetherian ring and `a` an ideal of `A`. Then
  i) `Gₐ(A)` is Noetherian.
  ii) `Gₐ(A)` and `Gₐ(Â)` are isomorphic as graded rings.
  iii) If `M` is a finitely-generated `A`-module and `(Mₙ)` is a stable `a`-filtration of `M`,
      then `G(M)` is a finitely-generated graded `Gₐ(A)`-module.
-/

variable {A : Type u} [hCA : CommRing A] [hNA: IsNoetherianRing A] (I : Ideal A) {R : Type u} [CommRing R]

instance hCSA : CommSemiring A := by infer_instance
instance hCSG : CommSemiring (GradedStarRing I) := by infer_instance
instance hAG : Algebra A (GradedStarRing I) := by exact instAlgebraGradedStarRing I

/-- Copyright (c) 2022 Christian Merten-/
axiom Ideal.mem_span_pow' {n : ℕ} (S : Set R) (x : R) :
    x ∈ (Ideal.span S) ^ n ↔ ∃ (p : MvPolynomial S R),
      MvPolynomial.IsHomogeneous p n ∧ MvPolynomial.eval Subtype.val p = x
/- end of copyright -/


noncomputable def ideal_generators : Set A := (IsNoetherian.noetherian I).choose

instance : IsNoetherianRing (MvPolynomial (ideal_generators I) A) := by
  dsimp [ideal_generators]
  infer_instance

def scalars₁ : A →+* ↥(I^0) where
  toFun := fun x ↦ ⟨x, by simp⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def scalar_morph : A →+* GradedStarRing I where
  toFun := DirectSum.of _ 0 ∘ scalars₁ I
  map_one' := rfl
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

def ideal_generator_mem (a : A) (ha: a ∈ ideal_generators I) : a ∈ I := by
  have : Submodule.span A (ideal_generators I) = I := (IsNoetherian.noetherian I).choose_spec
  rw[← this]
  exact Submodule.mem_span.mpr fun p a_1 ↦ a_1 ha

def var_morph : ideal_generators I → GradedStarRing I := fun ⟨a, ha⟩ => DirectSum.of _ 1 ⟨a, by simp [ideal_generator_mem I a ha]⟩

def φ (I : Ideal A): (MvPolynomial (↑(ideal_generators I)) A) →ₐ[A] GradedStarRing I := MvPolynomial.aeval (var_morph I)

lemma homogenous_polynomial_mem (n : ℕ) (p : MvPolynomial (↑(ideal_generators I)) A) (hp : p.IsHomogeneous n) :
    p.eval Subtype.val ∈ I ^ n := by
      have h₁: p.eval Subtype.val ∈ (Ideal.span (ideal_generators I)) ^ n := by
        apply (@Ideal.mem_span_pow'  A hCA n ((ideal_generators I)) (p.eval Subtype.val)).mpr
        use p
      have : Ideal.span (ideal_generators I) = I := (IsNoetherian.noetherian I).choose_spec
      rwa [this] at h₁


lemma homogenous_component_mem (n : ℕ) (p : MvPolynomial (↑(ideal_generators I)) A) :
   (p.homogeneousComponent n).eval Subtype.val ∈ I ^ n := by
  apply homogenous_polynomial_mem
  exact MvPolynomial.homogeneousComponent_isHomogeneous n p

instance : CoeOut ↥(I ^ 0) A := ⟨Subtype.val⟩


lemma polynomial_aeval_deg_zero : ∀ p : MvPolynomial (↑(ideal_generators I)) A,
    (p.aeval (var_morph I)) 0 = ⟨p.coeff 0, by simp⟩ := by
  intro p
  induction' p using MvPolynomial.induction_on with a p q hp hq p i hp
  · simp
    rfl
  · simp [hp, hq]
  · have h₁: MvPolynomial.constantCoeff (p * MvPolynomial.X i) = 0 := by
      rw[map_mul]
      simp
    have h : ((MvPolynomial.aeval (var_morph I)) (p * MvPolynomial.X i)) 0 = 0 := by
      rw[map_mul]
      have := gradedStarRing_mul_0 ((MvPolynomial.aeval (var_morph I)) p) (DirectSum.component A _ _ 1 ((@MvPolynomial.aeval A (GradedStarRing I) (↑(ideal_generators I)) hCSA (hCSG I) (hAG I) (var_morph I)) (MvPolynomial.X i)))
      have h₂:  ((@MvPolynomial.aeval A (GradedStarRing I) (↑(ideal_generators I)) hCSA (hCSG I) (hAG I) (var_morph I)) (MvPolynomial.X i)) = GradedStarRing_mk  (DirectSum.component A _ _ 1 ((@MvPolynomial.aeval A (GradedStarRing I) (↑(ideal_generators I)) hCSA (hCSG I) (hAG I) (var_morph I)) (MvPolynomial.X i))) := by
        dsimp [GradedStarRing_mk]
        simp
        rfl
      rw[h₂, this]
    rw[h]
    have h₃: MvPolynomial.coeff 0 (p * MvPolynomial.X i) = 0 := h₁
    rw[h₃]
    rfl

section

variable {σ : Type*} {R : Type*} [CommSemiring R]

lemma MvPolynomial.mul_homComp_eq_homComp_mul_of_hom (p q : MvPolynomial σ R) (n m : ℕ) (hq : q.IsHomogeneous m) :
    (p * q).homogeneousComponent (n + m) = p.homogeneousComponent n * q := by
  nth_rw 1 [←MvPolynomial.sum_homogeneousComponent p]
  rw [Finset.sum_mul]
  rw [map_sum]

  have : ∀ i, (p.homogeneousComponent i * q).homogeneousComponent (n + m) = if n = i then (p.homogeneousComponent n * q) else 0 := by
    intro i
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.IsHomogeneous.mul (MvPolynomial.homogeneousComponent_isHomogeneous i p) (hq))]
    refine if_ctx_congr ?_ ?_ (congrFun rfl)
    · exact Nat.add_right_cancel_iff
    · rintro ⟨rfl⟩
      rfl

  simp [this]
  intro h
  simp [MvPolynomial.homogeneousComponent_eq_zero n p h]
end

lemma aeval_proj_eq_hom_comp_eval : ∀ n : ℕ, ∀ p : MvPolynomial (↑(ideal_generators I)) A,
  (p.aeval (var_morph I)) n =
    ⟨(p.homogeneousComponent n).eval Subtype.val, homogenous_component_mem I n p⟩ := by

  intro n
  induction' n with n ih
  · intro p
    rw [polynomial_aeval_deg_zero]
    congr
    simp
  · intro p
    induction' p using MvPolynomial.induction_on with a p q hp hq p i hp
    · have h₂ : ((MvPolynomial.aeval (var_morph I)) (MvPolynomial.C a)) (n + 1) = 0  := by simp ; rfl
      rw [h₂]
      have h₃: (MvPolynomial.eval Subtype.val) ((MvPolynomial.homogeneousComponent (n + 1)) (@MvPolynomial.C A (↑(ideal_generators I)) hCSA a)) = 0 := by
        have h₆ :=  MvPolynomial.isHomogeneous_C (↑(ideal_generators I)) a
        have : n+1 ≠ 0 := by linarith
        rw [MvPolynomial.homogeneousComponent_of_mem h₆]
        simp

      exact SetLike.coe_eq_coe.mp (id (Eq.symm h₃))
    · simp [hp, hq]
    · have h₂ := (ih p)
      have Xi_homog := MvPolynomial.isHomogeneous_X A i

      have h₄ := MvPolynomial.mul_homComp_eq_homComp_mul_of_hom p (MvPolynomial.X i) n 1 Xi_homog
      
      have : (MvPolynomial.eval Subtype.val) ((MvPolynomial.homogeneousComponent (n + 1)) (p * MvPolynomial.X i)) = (MvPolynomial.eval Subtype.val) ((MvPolynomial.homogeneousComponent n) p * MvPolynomial.X i) := by
          congr
      
      nth_rw 2 [map_mul] at this
      nth_rw 1 [map_mul]

      have q₁ := gradedStarRing_mul_succ ((MvPolynomial.aeval (var_morph I)) p) (DirectSum.component A _ _ 1 ((@MvPolynomial.aeval A (GradedStarRing I) (↑(ideal_generators I)) hCSA (hCSG I) (hAG I) (var_morph I)) (MvPolynomial.X i))) n

      have q₂:  ((@MvPolynomial.aeval A (GradedStarRing I) (↑(ideal_generators I)) hCSA (hCSG I) (hAG I) (var_morph I)) (MvPolynomial.X i)) = GradedStarRing_mk  (DirectSum.component A _ _ 1 ((@MvPolynomial.aeval A (GradedStarRing I) (↑(ideal_generators I)) hCSA (hCSG I) (hAG I) (var_morph I)) (MvPolynomial.X i))) := by
        dsimp [GradedStarRing_mk]
        simp
        rfl

      rw[← q₂] at q₁
      rw[q₁]
      
      congr
      simp
      
      sorry


lemma φ.Surjective : Function.Surjective (φ I) := by
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · use 0
    simp
  · rintro n ⟨z,hz⟩
    have h₁ : I = Ideal.span (ideal_generators I) := (IsNoetherian.noetherian I).choose_spec.symm
    rw [h₁] at hz
    obtain ⟨y, hy₁, rfl⟩ := (@Ideal.mem_span_pow' A hCA n (ideal_generators I) z).mp hz

    use y
    unfold φ
    rw[←h₁] at hz

    apply DirectSum.ext
    intro k
    rw [aeval_proj_eq_hom_comp_eval]
    by_cases hkn : k = n
    · rw [hkn]
      rw [DirectSum.of_eq_same]
      congr
      rw[MvPolynomial.homogeneousComponent_of_mem hy₁]
      simp

    · rw [DirectSum.of_eq_of_ne n k _ (Ne.symm hkn)]
      simp
      have h₅ := (MvPolynomial.mem_homogeneousSubmodule n y).mpr hy₁
      have h₆ : (MvPolynomial.homogeneousComponent k) y  = 0 := by
        refine MvPolynomial.homogeneousComponent_eq_zero' k y ?_
        intro d hd
        have : d.degree = n := by
          rw[MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ] at h₅
          exact h₅ hd
        exact Lean.Grind.ne_of_ne_of_eq_left this fun a ↦ hkn (id (Eq.symm a))

      rw [h₆, map_zero]

  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    use a+b
    rw [map_add, ha, hb]



instance am10_22_i {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] : IsNoetherianRing (AssociatedGradedRing I) := by
  suffices : IsNoetherianRing (GradedStarRing I)
  exact isNoetherianRing_of_surjective _ _ _ (GradedStarRing_to_AssociatedGradedRingHom_surjective I)
  exact isNoetherianRing_of_surjective (MvPolynomial (ideal_generators I) A) (GradedStarRing I) (φ I) (φ.Surjective I)

noncomputable def am10_22_ii {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
    AssociatedGradedRing I ≃+* AssociatedGradedRing (I.adicCompletion I) :=
  AssociatedGradedRingIso_of_grp_iso (am10_15_iii_commute I)

instance am10_22_iii {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {F : I.Filtration M} (hF : F.Stable) :
    Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F) := sorry