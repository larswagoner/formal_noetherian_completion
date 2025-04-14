import Mathlib

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


/-
  This should be defined by `Gₐ(M) = ⊕ₙ Mₙ/Mₙ₊₁`
-/
def AssociatedGradedModule {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M]
  [Module A M] (F : I.Filtration M):
    Type u := sorry

/-
  `Gₐ(M)` should be an abelian group
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M]
  [Module A M] (F : I.Filtration M) : AddCommGroup (AssociatedGradedModule F) := sorry

/-
  This should be defined by `Gₐ(A) = ⊕ₙ aⁿ/aⁿ⁺¹`
-/
def AssociatedGradedRing {A : Type u} [CommRing A] (I : Ideal A) : Type u :=
  AssociatedGradedModule (I.stableFiltration (⊤ : Submodule A A))

/-
  `Gₐ(A)` should be proven to be a commutative ring
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) := sorry

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
    ℕ → Submodule (AssociatedGradedRing I) (AssociatedGradedModule F) := sorry

/-
  This should be the map `ϕ : ℕ → Submodule A Gₐ(A)` where `n ↦ aⁿ/aⁿ⁺¹`
-/
def AssociatedGradedRing_degMap {A : Type u} [CommRing A] (I : Ideal A) :
    ℕ → Submodule A (AssociatedGradedRing I) := sorry

/-
  With above indexing map, `Gₐ(A) ≅ ⊕ₙ φ(n)` should hold, making `Gₐ(A)` into a graded ring.
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : GradedRing (AssociatedGradedRing_degMap I) := sorry


/-
  `Gₐ(M)` should be a graded `Gₐ(A)`-module
-/
-- instance : ??? := sorry
