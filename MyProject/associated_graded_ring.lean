import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.GradedAlgebra.Basic

-- define associated graded module, then associated graded ring in terms of that.

/- # Associated Graded Ring
  Consider a ring `A` and an ideal `I : Ideal A`.

  Given an `A`-module `M` and an `I`-filtration `(Mₙ)`, define the associated graded module
    `G(M) = ⊕ₙ Mₙ/Mₙ₊₁`
  This has a natural group structure.

  In the case that `M = A` and `Mₙ = Iⁿ`, we obtain the associated graded ring of `A`
    `G(A) = ⊕ₙ Iⁿ/Iⁿ⁺¹`
  Multiplication is defined by `[xₙ] ⬝ [xₘ] = [xₙ ⬝ xₘ] ∈ Iⁿ⁺ᵐ/Iⁿ⁺ᵐ⁺¹`.

  Now `G(M)` is a `G(A)`-module in a natural way.
-/



open DirectSum

/--
  The `n`-th summand of `G(M)` is given by `Mₙ/Mₙ₊₁`. We use Submodule.comap to pull back the
  submodule `F.N (n + 1) = Mₙ₊₁ ⊆ M` along the map `(F.N n).subtype : Mₙ ⟶ M`.
-/
def GradedPiece {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ):
    Type u := (F.N n) ⧸ (Submodule.comap (F.N n).subtype (F.N (n + 1)))

/- 
  `Mₙ/Mₙ₊₁` is an abelian group and an `A`-module
-/


instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    AddCommGroup (GradedPiece F n) := by
    unfold GradedPiece
    infer_instance

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    Module A (GradedPiece F n) := by
    unfold GradedPiece
    infer_instance


/--
  This should be defined by `Gₐ(M) = ⊕ₙ Mₙ/Mₙ₊₁`
-/
def AssociatedGradedModule {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Type u := ⨁ n : ℕ, GradedPiece F n

  
/-
  `Gₐ(M)` is an abelian group and an `A`-module
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M]
    [Module A M] (F : I.Filtration M) : AddCommGroup (AssociatedGradedModule F) :=
  inferInstanceAs (AddCommGroup (Π₀ n : ℕ, GradedPiece F n))

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M]
    [Module A M] (F : I.Filtration M) : Module A (AssociatedGradedModule F) := by
    unfold AssociatedGradedModule
    infer_instance


/-
  This should be defined by `Gₐ(A) = ⊕ₙ aⁿ/aⁿ⁺¹`
-/
def AssociatedGradedRing {A : Type u} [CommRing A] (I : Ideal A) : Type u :=
  AssociatedGradedModule (I.stableFiltration (⊤ : Submodule A A))

/-
  `Gₐ(A)` is an abelian group and an `A`-module
-/

instance {A : Type u} [CommRing A] (I : Ideal A) : AddCommMonoid (AssociatedGradedRing I):= by
  unfold AssociatedGradedRing
  infer_instance

instance {A : Type u} [CommRing A] (I : Ideal A) : Module A (AssociatedGradedRing I):= by
  unfold AssociatedGradedRing
  unfold AssociatedGradedModule
  infer_instance

/-
  Defining multiplication on `Gₐ(A)`
        : (h : GradedPiece I m) component_map : GradedPiece I n → GradedPiece I n+m
-/
noncomputable def graded_mul  {A : Type u} [CommRing A] (I : Ideal A) {m n :ℕ} : (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) m) → 
    (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) n) →  (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) (m+n)) := by  
  intro x y 
  let x_rep := Quotient.out x 
  let y_rep := Quotient.out y 

  let z := (x_rep : A) * (y_rep : A)

  have h₁ : z ∈ I ^ (m + n) := by 
    have m_equiv : (I.stableFiltration ⊤).N m = I ^ m := by simp only [Ideal.stableFiltration_N,
        smul_eq_mul, Ideal.mul_top]
    have n_equiv : (I.stableFiltration ⊤).N n = I ^ n := by simp only [Ideal.stableFiltration_N,
        smul_eq_mul, Ideal.mul_top]

    apply SetLike.mul_mem_graded
    · rw[← m_equiv]
      exact x_rep.prop
    · rw[← n_equiv]
      exact y_rep.prop
    
  let hz : ↥(I ^ (m + n)) := ⟨z, h₁⟩  

  apply Submodule.Quotient.mk
  simp only [Ideal.stableFiltration_N, smul_eq_mul, Ideal.mul_top]
  
  exact hz





/--
  The map `ℕ → Type` given by `GradedPiece (I.stableFiltration (⊤ : Submodule A A))` defines a
  graded ring structure.
-/
noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GCommRing (GradedPiece (I.stableFiltration (⊤ : Submodule A A))) where
  mul := (graded_mul I)
  mul_zero := sorry
  zero_mul := sorry
  mul_add := sorry
  add_mul := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  intCast := sorry
  intCast_ofNat := sorry
  intCast_negSucc_ofNat := sorry
  mul_comm := sorry
  




/-
  `Gₐ(A)` should be proven to be a commutative ring
-/

instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) := {
  instAddCommGroupAssociatedGradedModule (I.stableFiltration (⊤ : Submodule A A)) with
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  neg := sorry
  sub := sorry
  sub_eq_add_neg := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  mul_comm := sorry
}


/-
  `Gₐ(A)` should be an `A`-algebra
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : Algebra A (AssociatedGradedRing I) := sorry

/-
  `Gₐ(M)` should be an `Gₐ(A)`-module
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Module (AssociatedGradedRing I) (AssociatedGradedModule F) := sorry




/-
  This should be the map `ℕ → Submodule Gₐ(A) Gₐ(M)` where `n ↦ Mₙ/Mₙ`
-/
def AssociatedGradedModule_degMap {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    ℕ → Submodule (AssociatedGradedRing I) (AssociatedGradedModule F) := by
    intro n

    --exact LinearMap.range (lof (AssociatedGradedRing I) ℕ (fun n => (GradedPiece F n)) n) -- Gₐ(A) needs to be a ring! Maybe prove it is a graded ring first?
    sorry

/-
  This should be the map `ϕ : ℕ → Submodule A Gₐ(A)` where `n ↦ aⁿ/aⁿ⁺¹`
-/
def AssociatedGradedRing_degMap {A : Type u} [CommRing A] (I : Ideal A) :
    ℕ → Submodule A (AssociatedGradedRing I) := by 
  intro n
  exact LinearMap.range (lof A ℕ (fun n => (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) n)) n)


/-
  With above indexing map, `Gₐ(A) ≅ ⊕ₙ ϕ(n)` should hold, making `Gₐ(A)` into a graded ring.
-/

-- Need Gₐ(A) is (semi)-ring 
instance {A : Type u} [CommRing A] (I : Ideal A) : GradedRing (AssociatedGradedRing_degMap I) where
  one_mem := by 
    sorry
  mul_mem := sorry
  decompose' := sorry
  left_inv := sorry
  right_inv := sorry



/-
  `Gₐ(M)` should be a graded `Gₐ(A)`-module
-/
-- instance : ??? := sorry