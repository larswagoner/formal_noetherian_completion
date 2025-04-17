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
  `Gₐ(A)` should be proven to be a commutative ring
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) := by sorry

  


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
/-- I broke this, will try to fix it...

-- Need Gₐ(A) is (semi)-ring 
instance {A : Type u} [CommRing A] (I : Ideal A) : GradedRing (AssociatedGradedRing_degMap I) where
  one_mem := by 
    sorry
  mul_mem := sorry
  decompose' := sorry
  left_inv := sorry
  right_inv := sorry

-/
/-
  `Gₐ(M)` should be a graded `Gₐ(A)`-module
-/
-- instance : ??? := sorry
lemma A : true := sorry -- also ignor this.