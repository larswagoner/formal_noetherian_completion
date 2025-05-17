import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.RingTheory.Filtration

@[ext]
structure OurFiltration (G : Type u) [AddCommGroup G] : Type _  where
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

end
