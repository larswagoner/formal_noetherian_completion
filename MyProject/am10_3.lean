import MyProject.am10_2
import MyProject.Filtration.Constructions
import MyProject.Completion.FiltrationCompletion
import Mathlib.Algebra.Exact

/-
  # Corollary 10.3
  Let `0 ⟶ G' ⟶ G ⟶p G'' ⟶ 0` be an exact sequence of groups.
  Let `G` have the topology defined by a sequence `{Gₙ}` of subgroups and
  give `G', G''` the induced topologies, i.e. by `{G' ∩  Gₙ}, {pGₙ}`.
  Then `0 ⟶ Ĝ' ⟶ Ĝ ⟶ Ĝ'' ⟶ 0` is exact.
-/

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M N O : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup O] [Module A O]
variable (q : M →ₗ[A] N) (p : N →ₗ[A] O) (F : I.Filtration N)

def map₁ : (FiltrationCompletion (PullbackFiltration q F)) →ₗ[A] (FiltrationCompletion F) :=
  FiltrationCompletionHom.of_comap_le (fun n ↦ by rfl)

def map₂ : (FiltrationCompletion F) →ₗ[A] (FiltrationCompletion (PushforwardFiltration p F)) :=
  FiltrationCompletionHom.of_comap_le (fun n ↦ Submodule.le_comap_map p (F.N n))

-- TODO: How to mention exactness?
variable (h₁ : Function.Injective q)
variable (h₂ : Function.Exact q p)
variable (h₃ : Function.Surjective p)

lemma am10_3_inj : Function.Injective (map₁ q F) := sorry
lemma am10_3_exact : Function.Exact (map₁ q F) (map₂ p F) := sorry
lemma am10_3_surj : Function.Surjective (map₂ p F) := sorry
