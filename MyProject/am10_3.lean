import MyProject.am10_2
import MyProject.Filtration.FConstructions
import MyProject.Completion.OurFiltrationCompletion
import Mathlib.Algebra.Exact

/-
  # Corollary 10.3
  Let `0 ⟶ G' ⟶ G ⟶p G'' ⟶ 0` be an exact sequence of groups.
  Let `G` have the topology defined by a sequence `{Gₙ}` of subgroups and
  give `G', G''` the induced topologies, i.e. by `{G' ∩  Gₙ}, {pGₙ}`.
  Then `0 ⟶ Ĝ' ⟶ Ĝ ⟶ Ĝ'' ⟶ 0` is exact.
-/

variable {G₁ G₂ G₃ : Type*} [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
variable (q : G₁ →+ G₂) (p : G₂ →+ G₃) (F : OurFiltration G₂)

def map₁ : (OurFiltrationCompletion (PullbackOurFiltration q F)) →+ (OurFiltrationCompletion F) :=
  OurFiltrationCompletionHom.of_comap_le (fun n ↦ by rfl)

def map₂ : (OurFiltrationCompletion F) →+ (OurFiltrationCompletion (PushforwardOurFiltration p F)) :=
  OurFiltrationCompletionHom.of_comap_le (fun n ↦ AddSubgroup.le_comap_map p (F.N n))

-- TODO: How to mention exactness?
variable (h₁ : Function.Injective q)
variable (h₂ : Function.Exact q p)
variable (h₃ : Function.Surjective p)

lemma am10_3_inj : Function.Injective (map₁ q F) := sorry
lemma am10_3_exact : Function.Exact (map₁ q F) (map₂ p F) := sorry
lemma am10_3_surj : Function.Surjective (map₂ p F) := sorry
