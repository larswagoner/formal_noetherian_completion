import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-
  # Proposition 10.13
  Let `A` be a ring an `M` a finitely generated `A`-module.
  Then
  i) `Â ⨂A M ⟶ M̂` is surjective
  ii) If `A` is Noetherian, `Â ⨂A M ⟶ M̂` is an isomorphism
-/

/-
  Note: the natural `Â`-module morphism `Â ⨂ M ⟶ M̂` is given by
    `AdicCompletion.ofTensorProduct I M`
-/

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

section
open AdicCompletion

lemma am10_13_i : Function.Surjective (ofTensorProduct I M) :=
  ofTensorProduct_surjective_of_finite I M

noncomputable def am10_13_ii [IsNoetherianRing A] :
  TensorProduct A (AdicCompletion I A) M ≃ₗ[AdicCompletion I A] AdicCompletion I M :=
  ofTensorProductEquivOfFiniteNoetherian I M

end
