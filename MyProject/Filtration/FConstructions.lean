import MyProject.Filtration.OurFiltration
import Mathlib.LinearAlgebra.SModEq

section

variable {G H : Type*} [AddCommGroup G] (F : OurFiltration G)

/--
  Let `G` be a group with a filtration `{Gₙ}ₙ`. Then for any `m : ℕ` we can form the filtration
  given by `{Gₙ₋ₘ}ₙ`.
-/
def OffsetOurFiltration (m : ℕ) : OurFiltration G where
  N := fun n ↦ F.N (n - m)
  mono := by
    intro i
    by_cases h : i < m
    · rw [Nat.sub_eq_zero_of_le h]
      rw [Nat.sub_eq_zero_of_le (le_of_lt h)]
    · push_neg at h
      rw [Nat.sub_add_comm h]
      exact F.mono (i - m)

@[simp]
lemma offsetOurFiltration_eval_add (m n : ℕ) :
    (OffsetOurFiltration F m).N (n + m) = F.N n := by
  unfold OffsetOurFiltration
  simp

@[simp]
lemma offsetOurFiltration_eval_le {m n : ℕ} (h : n ≤ m) :
    (OffsetOurFiltration F m).N n = F.N 0 := by
  unfold OffsetOurFiltration
  simp
  rw [Nat.sub_eq_zero_of_le h]

/--
  Let `G` be a group with a filtration `{Gₙ}ₙ`. Then for any `m : ℕ` we can form the filtration
  given by `{Gₙ₊ₘ}ₙ`.
-/
def OffsetPosOurFiltration (m : ℕ) : OurFiltration G where
  N := fun n ↦ F.N (n + m)
  mono := by
    intro i
    convert F.mono (i + m) using 2
    abel

@[simp]
lemma offsetPosOurFiltration_eval_sub_of_le (m n : ℕ) (h : m ≤ n) :
    (OffsetPosOurFiltration F m).N (n - m) = F.N n := by
  unfold OffsetPosOurFiltration
  simp
  rw [Nat.sub_add_cancel h]

end

section

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H)

/--
  Given two `A`-modules `M` and `N` and a map `φ : M →ₗ[A] N`, one can pullback a filtration `F` on `N`
  to a filtration on `M` given by `Mₙ = φ⁻¹(Nₙ)`.
-/
def PullbackOurFiltration (F : OurFiltration H) : OurFiltration G where
  N := fun n ↦ (F.N n).comap φ
  mono := fun n ↦ AddSubgroup.comap_mono (F.mono n)

/--
  Given two `A`-modules `M` and `N` and a map `φ : M →ₗ[A] N`, one can pushforward a filtration `F`
  on `M` to a filtration on `N` given by `Nₙ = φ(Mₙ)`.
-/
def PushforwardOurFiltration (F : OurFiltration G) : OurFiltration H where
  N := fun n ↦ (F.N n).map φ
  mono := fun n ↦ AddSubgroup.map_mono (F.mono n)

end
