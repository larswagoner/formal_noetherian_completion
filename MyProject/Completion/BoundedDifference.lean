import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

/-
  In this file we prove:
  · For any filtration `F` on a group `G`, we have an ismorphism
      `OurFiltrationCompletion F ≃+ OurFiltrationCompletion (OffsetPosOurFiltration F n)`.
  · For any two filtrations `F, F'` on a group `G` with a bounded difference, i.e. there are integers
      `m, n` such that `F.N (i + m) ⊆ F'.N i` and `F'.N (i + n) ⊆ F.N i`, there is an isomorphism
      `OurFiltrationCompletion F ≃+ OurFiltrationCompletion F'`..
-/

variable {G : Type*} [AddCommGroup G] (F : OurFiltration G)

def OffsetPosCompletionMap₁ (n : ℕ) :
    OurFiltrationCompletion F →+ OurFiltrationCompletion (OffsetPosOurFiltration F n) where
  toFun := by
    intro x
    use (fun i ↦ x.1 (i+n))
    intro i j h
    exact x.2 (show i + n ≤ j + n by linarith)
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

def OffsetPosCompletionMap₂ (n : ℕ) :
    OurFiltrationCompletion (OffsetPosOurFiltration F n) →+ OurFiltrationCompletion F :=
  OurFiltrationCompletionHom.of_comap_le (OffsetPosOurFiltration F n) F (AddMonoidHom.id G) (by
    intro m
    show F.N (m + n) ≤ F.N m
    apply OurFiltration_antitone
    exact Nat.le_add_right m n
  )

def OffsetPosCompletionIso (n : ℕ) :
    OurFiltrationCompletion F ≃+ OurFiltrationCompletion (OffsetPosOurFiltration F n) where
  __ := OffsetPosCompletionMap₁ F n
  invFun := OffsetPosCompletionMap₂ F n
  left_inv := by
    intro x
    ext i
    unfold OffsetPosCompletionMap₁
    unfold OffsetPosCompletionMap₂
    simp
    have : i ≤ i + n := by linarith
    rw [←x.2 this]
    rcases (x.1 (i + n)) with ⟨y⟩
    rfl
  right_inv := by
    intro x
    ext i
    unfold OffsetPosCompletionMap₁
    unfold OffsetPosCompletionMap₂
    simp
    have : i ≤ i + n := by linarith
    rw [←x.2 this]
    rcases (x.1 (i + n)) with ⟨y⟩
    rfl

variable {F} {F' : OurFiltration G} (n m : ℕ)
variable (h₁ : ∀ i, F.N (i + n) ≤ F'.N i ) (h₂ : ∀ i, F'.N (i + m) ≤ F.N i)

def OurFiltrationCompletion_bounded_offset_map :
    OurFiltrationCompletion (OffsetPosOurFiltration F n) →+ OurFiltrationCompletion F' :=
  OurFiltrationCompletionHom.of_comap_le (OffsetPosOurFiltration F n) F' (AddMonoidHom.id G) h₁

def OurFiltrationCompletionIso_of_bounded_difference :
      OurFiltrationCompletion F ≃+ OurFiltrationCompletion F' where
    __ := (OurFiltrationCompletion_bounded_offset_map n h₁).comp (OffsetPosCompletionMap₁ F n)
    invFun := (OurFiltrationCompletion_bounded_offset_map m h₂).comp (OffsetPosCompletionMap₁ F' m)
    left_inv := by
      intro x
      ext i
      unfold OffsetPosCompletionMap₁ OurFiltrationCompletion_bounded_offset_map
      simp
      have : i ≤ i + m + n := by linarith
      rw [←x.2 this]
      rcases (x.1 (i + m + n)) with ⟨y⟩
      rfl
    right_inv := by
      intro x
      ext i
      unfold OffsetPosCompletionMap₁ OurFiltrationCompletion_bounded_offset_map
      simp
      have : i ≤ i + n + m := by linarith
      rw [←x.2 this]
      rcases (x.1 (i + n + m)) with ⟨y⟩
      rfl
