import MyProject.am10_2
import MyProject.AssociatedGradedRing.Map
import MyProject.Completion.FiltrationCompletion

/-
  # Lemma 10.23
  Let `φ : A → B` be a homomorphism of filtered groups, i.e. `φ(Aₙ) ⊆ Bₙ`,
  and let `G(φ) : G(A) → G(B)`, `̂ϕ, Â → B̂` be the induced homomorphisms of
  the associated graded an completed groups. Then:
  i) `G(φ)` injective => `̂ϕ` injective
  ii) `G(φ)` surjective => `̂ϕ` surjective
-/

/-
 Option 1: restrict to rings. Pros: easy, cons: too easy? -- indeed.
 Option 2: look at modules, look at I-adic completions of modules. Pros: general enough, not much harder than option 1, can use AdicCompletion.map no problem.
 Option 2b: Look at stable I-filtrations
 Option 3: modules with any I-filtration. cons: phi hat needs to be defined. Could be easy, could be hard.
 Option 4: prove it for any filtered group. cons: need to define stuff for group.

-/

-- AdicCompletion.map https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdicCompletion/Functoriality.html#AdicCompletion.map

-- take particular case of I adic completions of A and B.

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
variable {F : I.Filtration M} {F' : I.Filtration M'} {φ : M →ₗ[A] M'}

lemma am10_23_i (hφ : ∀ n, F.N n ≤ (F'.N n).comap φ) :
  Function.Injective (GradedModuleHom hφ) → Function.Injective (FiltrationCompletionHom.of_comap_le hφ) := sorry

lemma am10_23_ii (hφ : ∀ n, F.N n ≤ (F'.N n).comap φ) :
  Function.Surjective (GradedModuleHom hφ) → Function.Surjective (FiltrationCompletionHom.of_comap_le hφ) := sorry
