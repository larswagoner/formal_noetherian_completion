import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.RingTheory.Filtration

@[ext]
structure OurFiltration (G : Type u) [AddCommGroup G] : Type u  where
  N : ℕ → AddSubgroup G
  mono : ∀ i, N (i + 1) ≤ N i


lemma OurFiltration_antitone {G : Type u} [AddCommGroup G] (F : OurFiltration G) :
    Antitone F.N :=
  antitone_nat_of_succ_le F.mono

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]

def Ideal.Filtration.toOurFiltration (F : I.Filtration M) : OurFiltration M where
  N := fun n ↦ (F.N n).toAddSubgroup
  mono := fun n ↦ F.mono n

def Ideal.Filtration.ofOurFiltration (F : OurFiltration M)
  (h₁ : ∀ n : ℕ, ∀ (c : A) {x : M}, x ∈ F.N n → c • x ∈ F.N n)
  (h₂ : ∀ n : ℕ, I • ({ toAddSubmonoid := (F.N n).toAddSubmonoid, smul_mem' := h₁ n } : Submodule A M) ≤ { toAddSubmonoid := (F.N (n+1)).toAddSubmonoid, smul_mem' := h₁ (n+1) })
    :
    I.Filtration M where
  N := fun n ↦ {
    __ := F.N n
    smul_mem' := h₁ n
  }
  mono := fun n ↦ F.mono n
  smul_le := h₂

end
