import Mathlib.RingTheory.Jacobson.Ideal

/-
  # Proposition 1.9
  Let `A` be a ring and `J` its Jacobson radical. Let `x ∈ A`.
  Then `x ∈ J` if and only if `1 - xy ∈ A*` for all `y ∈ A`.
-/

lemma am1_9 {R : Type*} [CommRing R] (x : R) :
  x ∈ (⊥ : Ideal R).jacobson ↔ ∀ (y : R), IsUnit (1 - x * y) := by
  rw [Ideal.mem_jacobson_bot]
  constructor
  · intro h y
    convert h (-y) using 1
    ring
  · intro h y
    convert h (-y) using 1
    ring
