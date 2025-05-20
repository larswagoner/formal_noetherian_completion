import MyProject.am10_2
import MyProject.AssociatedGradedRing.Map
import MyProject.Completion.FiltrationCompletion
import Mathlib.Algebra.Module.NatInt

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
variable {M : Type u} [AddCommGroup M] [Module A M]
variable (F : I.Filtration M)

def submoduleOfSubSet {N₁ N₂ : Submodule A M} (_ : N₁ ≤ N₂) : Submodule A N₂ where
  carrier := {x | x.1 ∈ N₁}
  add_mem' := by
    intro a b ha hb
    simp
    apply N₁.add_mem' ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp
    apply N₁.smul_mem'
    exact hx

def SES_n (n : ℕ) : AddCommGroupSES where
  X₁ := AddCommGrp.of <| F.N n ⧸ (submoduleOfSubSet (F.mono n)).toAddSubgroup
  X₂ := AddCommGrp.of <| M ⧸ (F.N (n+1)).toAddSubgroup
  X₃ := AddCommGrp.of <| M ⧸ (F.N n).toAddSubgroup
  f := by
    let f₁ : F.N n →+ M := (F.N n).subtype.toAddMonoidHom
    have : (submoduleOfSubSet (F.mono n)).toAddSubgroup ≤ AddSubgroup.comap f₁ (F.N (n+1)).toAddSubgroup := by
      intro x hx
      simp [f₁]
      apply hx

    apply groupHomToGrpHom <| QuotientAddGroup.map _ _ f₁ this
  g := by
    let g₁ : M →+ M := AddMonoidHom.id M
    have : (F.N (n+1)).toAddSubgroup ≤ AddSubgroup.comap g₁ (F.N n).toAddSubgroup := by
      intro x hx
      simp [g₁]
      apply F.mono
      apply hx

    apply groupHomToGrpHom <| QuotientAddGroup.map _ _ g₁ this
  zero := by
    let f₁ : F.N n →+ M := (F.N n).subtype.toAddMonoidHom
    have : (submoduleOfSubSet (F.mono n)).toAddSubgroup ≤ AddSubgroup.comap f₁ (F.N (n+1)).toAddSubgroup := by
      intro x hx
      simp [f₁]
      apply hx
    let f : F.N n ⧸ (submoduleOfSubSet (F.mono n)).toAddSubgroup →+ M ⧸ (F.N (n+1)).toAddSubgroup := QuotientAddGroup.map _ _ f₁ this

    let g₁ : M →+ M := AddMonoidHom.id M
    have : (F.N (n+1)).toAddSubgroup ≤ AddSubgroup.comap g₁ (F.N n).toAddSubgroup := by
      intro x hx
      simp [g₁]
      apply F.mono
      apply hx

    let g : M ⧸ (F.N (n+1)).toAddSubgroup →+ M ⧸ (F.N n).toAddSubgroup := QuotientAddGroup.map _ _ g₁ this
    --

    ext x
    have this : g (f x) = x.1 := rfl
    simp
    show g (f x) = 0
    rw [this]
    simp
  injective := by
    /- This has to be the ugliest proof I have ever written -/
    let f₁ : F.N n →+ M := (F.N n).subtype.toAddMonoidHom
    have : (submoduleOfSubSet (F.mono n)).toAddSubgroup ≤ AddSubgroup.comap f₁ (F.N (n+1)).toAddSubgroup := by
      intro x hx
      simp [f₁]
      apply hx
    let f : F.N n ⧸ (submoduleOfSubSet (F.mono n)).toAddSubgroup →+ M ⧸ (F.N (n+1)).toAddSubgroup := QuotientAddGroup.map _ _ f₁ this
    --

    intro x y
    show f x = f y → x = y
    intro hxy
    rcases (QuotientAddGroup.mk'_surjective (submoduleOfSubSet (F.mono n)).toAddSubgroup x) with ⟨a,ha⟩
    rcases (QuotientAddGroup.mk'_surjective (submoduleOfSubSet (F.mono n)).toAddSubgroup y) with ⟨b,hb⟩
    have afx : (F.N n).subtype a = f x := by unfold f; rw [<- ha]; rfl
    have bfy : (F.N n).subtype b = f y := by unfold f; rw [<- hb]; rfl

    rw [<- afx, <- bfy] at hxy
    apply (QuotientAddGroup.mk'_eq_mk' _).mp at hxy
    rcases hxy with ⟨z, hz₁, hz₂⟩

    have : z ∈ F.N n := by apply Set.mem_of_subset_of_mem (F.mono n) hz₁

    have : QuotientAddGroup.mk' (submoduleOfSubSet (F.mono n)).toAddSubgroup a = QuotientAddGroup.mk' (submoduleOfSubSet (F.mono n)).toAddSubgroup b := by
      apply (QuotientAddGroup.mk'_eq_mk' _).mpr
      use ⟨z, this⟩
      use hz₁
      apply Submodule.subtype_injective
      simp
      exact hz₂

    rw [<- ha, this, hb]
  middle := by
    let f₁ : F.N n →+ M := (F.N n).subtype.toAddMonoidHom
    have : (submoduleOfSubSet (F.mono n)).toAddSubgroup ≤ AddSubgroup.comap f₁ (F.N (n+1)).toAddSubgroup := by
      intro x hx
      simp [f₁]
      apply hx
    let f : F.N n ⧸ (submoduleOfSubSet (F.mono n)).toAddSubgroup →+ M ⧸ (F.N (n+1)).toAddSubgroup := QuotientAddGroup.map _ _ f₁ this

    let g₁ : M →+ M := AddMonoidHom.id M
    have : (F.N (n+1)).toAddSubgroup ≤ AddSubgroup.comap g₁ (F.N n).toAddSubgroup := by
      intro x hx
      simp [g₁]
      apply F.mono
      apply hx

    let g : M ⧸ (F.N (n+1)).toAddSubgroup →+ M ⧸ (F.N n).toAddSubgroup := QuotientAddGroup.map _ _ g₁ this
    --

    intro x hx
    simp at hx
    simp
    rcases QuotientAddGroup.mk'_surjective (F.N (n+1)).toAddSubgroup x with ⟨w,hw⟩
    have : w ∈ F.N n := by
      simp at hw
      rw [<- hw] at hx
      simp at hx
      exact hx
    use QuotientAddGroup.mk' _ ⟨w, this⟩
    simp
    exact hw
  surjective := by
    intro y
    rcases QuotientAddGroup.mk'_surjective (F.N n).toAddSubgroup y with ⟨x,hx⟩
    use QuotientAddGroup.mk' _ x
    simp
    exact hx


variable {M' : Type u} [AddCommGroup M'] [Module A M']
variable (F' : I.Filtration M')

def CommDiagramOfSES_n (n : ℕ) : CommDiagramOfSES where
  s₁ := SES_n F n
  s₂ := SES_n F' n
  v₁ := sorry
  v₂ := sorry
  v₃ := sorry
  commleft := sorry
  commright := sorry

lemma am10_23_i (hφ : ∀ n, F.N n ≤ (F'.N n).comap φ) :
  Function.Injective (GradedModuleHom hφ) → Function.Injective (FiltrationCompletionHom.of_comap_le hφ) := sorry

lemma am10_23_ii (hφ : ∀ n, F.N n ≤ (F'.N n).comap φ) :
  Function.Surjective (GradedModuleHom hφ) → Function.Surjective (FiltrationCompletionHom.of_comap_le hφ) := sorry
