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


section nthExactSequence

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
  X₁ := AddCommGrp.of <| GradedPiece F n
  X₂ := AddCommGrp.of <| FiltrationIS F (n+1)
  X₃ := AddCommGrp.of <| FiltrationIS F n
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
    rcases (QuotientAddGroup.mk'_surjective (submoduleOfSubSet (F.mono n)).toAddSubgroup x) with ⟨w,hw⟩
    have this : g (f x) = Submodule.subtype _ w := by rw [<- hw]; rfl
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
      exact (Submodule.Quotient.mk_eq_zero (F.N n)).mp hx
    use QuotientAddGroup.mk' _ ⟨w, this⟩
    simp
    exact hw
  surjective := by
    intro y
    rcases QuotientAddGroup.mk'_surjective (F.N n).toAddSubgroup y with ⟨x,hx⟩
    use QuotientAddGroup.mk' _ x
    simp
    exact hx

end nthExactSequence


variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {F : I.Filtration M}
variable {M' : Type u} [AddCommGroup M'] [Module A M']
variable {F' : I.Filtration M'}
variable {φ : M →ₗ[A] M'} (hφ : ∀ n, F.N n ≤ (F'.N n).comap φ)

def CommDiagramOfSES_n (n : ℕ) : CommDiagramOfSES where
  s₁ := SES_n F n
  s₂ := SES_n F' n
  v₁ := groupHomToGrpHom <| GradedPieceHom_additive hφ n
  v₂ := groupHomToGrpHom <| (FISystemHom.of_comap_le hφ).maps (n+1)
  v₃ := groupHomToGrpHom <| (FISystemHom.of_comap_le hφ).maps n
  commleft := by
    ext x
    rcases QuotientAddGroup.mk'_surjective _ x with ⟨w,hw⟩
    rw [<- hw]
    rfl
  commright := by
    ext x
    rcases QuotientAddGroup.mk'_surjective _ x with ⟨w,hw⟩
    rw [<- hw]
    rfl

lemma cokerφnzero (GradedSurjective : Function.Surjective (GradedModuleHom hφ)) (n : ℕ) : ∀ x : (cokernel (CommDiagramOfSES_n hφ n).v₁.hom'), x = 0 := by
  intro y
  rcases QuotientAddGroup.mk'_surjective _ y with ⟨w,hw⟩
  rw [<- hw]
  simp
  exact (DirectSum.lmap_surjective (GradedPieceHom hφ)).mp GradedSurjective _ _


lemma cokerv₃zero (F'top : F'.N 0 = ⊤) (GradedSurjective : Function.Surjective (GradedModuleHom hφ)) (n : ℕ) : ∀ x : (cokernel (CommDiagramOfSES_n hφ n).v₃.hom'), x = 0 := by
  intro y
  induction' n with n hn
  · rcases QuotientAddGroup.mk'_surjective _ y with ⟨w,hw⟩
    rcases QuotientAddGroup.mk'_surjective _ w with ⟨a,ha⟩
    have : QuotientAddGroup.mk' _ a = (0 : (CommDiagramOfSES_n hφ 0).s₂.X₃) := by
      show a ∈ (QuotientAddGroup.mk' _).ker
      rw [QuotientAddGroup.ker_mk', F'top]
      simp
    rw [<- hw, <- ha, this, map_zero]
  · exact zeroOfZeroExactZero (cokerφnzero hφ GradedSurjective n) hn (inducedMap₄inducedMap₅Exact (CommDiagramOfSES_n hφ n)) y


lemma inducedMap₂Surjective (GradedSurjective : Function.Surjective (GradedModuleHom hφ)) (n : ℕ) : Function.Surjective <| inducedMap₂ (CommDiagramOfSES_n hφ n) :=
  surjectiveOfExactZero (cokerφnzero hφ GradedSurjective n) (DeltaExact (CommDiagramOfSES_n hφ n))

lemma kerEqKer (n : ℕ) : (CommDiagramOfSES_n hφ n).v₂.hom'.ker = (CommDiagramOfSES_n hφ (n+1)).v₃.hom'.ker := rfl

def kernelMorphism (n : ℕ) : (CommDiagramOfSES_n hφ (n+1)).v₃.hom'.ker →+ (CommDiagramOfSES_n hφ n).v₃.hom'.ker := by
  rw [<- kerEqKer hφ n]
  exact inducedMap₂ (CommDiagramOfSES_n hφ n)

open CategoryTheory

def kernelMorphismnm : ∀ ⦃n m⦄ (_ : n ≤ m), (CommDiagramOfSES_n hφ m).v₃.hom'.ker →+ (CommDiagramOfSES_n hφ n).v₃.hom'.ker := by
  intro n m h
  let diam := (CommDiagramOfSES_n hφ m)
  let dian := (CommDiagramOfSES_n hφ n)
  let g₁ : diam.s₁.X₃ ⟶ dian.s₁.X₃ := by
    have : (F.N m).toAddSubgroup ≤ AddSubgroup.comap (AddMonoidHom.id M) (F.N n).toAddSubgroup := by
      simp
      apply F.antitone h
    apply groupHomToGrpHom <| QuotientAddGroup.map _ _ (AddMonoidHom.id M) this
  let g₂ : diam.s₂.X₃ ⟶ dian.s₂.X₃ := by
    have : (F'.N m).toAddSubgroup ≤ AddSubgroup.comap (AddMonoidHom.id M') (F'.N n).toAddSubgroup := by
      simp
      apply F'.antitone h
    apply groupHomToGrpHom <| QuotientAddGroup.map _ _ (AddMonoidHom.id M') this
  let f₁ := diam.v₃
  let f₂ := dian.v₃
  have : f₁ ≫ g₂ = g₁ ≫ f₂ := by
    simp
    congr 1
    ext x
    simp [f₁, f₂, g₁, g₂]
    rcases QuotientAddGroup.mk'_surjective _ x with ⟨w,hw⟩
    rw [<- hw]
    rfl
  apply inducedMapKer this.symm

def map_nm : ∀ ⦃n m⦄ (_ : n ≤ m), (CommDiagramOfSES_n hφ m).s₁.X₃ ⟶ (CommDiagramOfSES_n hφ n).s₁.X₃ := by
  intro n m h
  have : (F.N m).toAddSubgroup ≤ AddSubgroup.comap (AddMonoidHom.id M) (F.N n).toAddSubgroup := by
    simp
    apply F.antitone h
  apply groupHomToGrpHom <| QuotientAddGroup.map _ _ (AddMonoidHom.id M) this

instance firstAddInvSystem : AddInverseSystem (kernelMorphismnm hφ) where
  map_self := by
    intro n x
    let g₁ : (CommDiagramOfSES_n hφ n).s₁.X₃ ⟶ (CommDiagramOfSES_n hφ n).s₁.X₃ := by
      have : (F.N n).toAddSubgroup ≤ AddSubgroup.comap (AddMonoidHom.id M) (F.N n).toAddSubgroup := by
        simp
      apply groupHomToGrpHom <| QuotientAddGroup.map _ _ (AddMonoidHom.id M) this
    rcases QuotientAddGroup.mk'_surjective _ x.1 with ⟨w,hw⟩
    have : kernelMorphismnm hφ n.le_refl x = g₁.hom' x.1 := rfl
    rw [Subtype.mk.injEq, this, <- hw]
    rfl
  map_map := by
    intro k j i hkj hji x
    let g₁ := map_nm hφ hkj
    let g₂ := map_nm hφ hji
    let g₃ := map_nm hφ (le_trans hkj hji)
    have : ∀ ⦃n m⦄ (h : n ≤ m), ∀ x, kernelMorphismnm hφ h x = (map_nm hφ h).hom' x.1 := by
      intro n m h x
      rcases QuotientAddGroup.mk'_surjective _ x.1 with ⟨w,hw⟩
      rfl
    rw [Subtype.mk.injEq, this (le_trans hkj hji) x, this hkj _, this hji _]
    have : g₁.hom'.comp g₂.hom' = g₃.hom' := by
      ext a
      rcases QuotientAddGroup.mk'_surjective _ a with ⟨w,hw⟩
      rw [<- hw]
      rfl
    apply congrHom this x.1

lemma firstSystemSurjBase (GradedSurjective : Function.Surjective (GradedModuleHom hφ)) : ∀ n : ℕ, Function.Surjective (kernelMorphismnm hφ n.le_succ) := by
  intro n
  apply surjectiveOfExactZero (cokerφnzero hφ GradedSurjective n) (DeltaExact (CommDiagramOfSES_n hφ n))

lemma firstSystemSurj (GradedSurjective : Function.Surjective (GradedModuleHom hφ)) : ∀ ⦃n m⦄ (h : n ≤ m), Function.Surjective (kernelMorphismnm hφ h) := by
  intro n m h
  induction h using Nat.leRec with
  | refl => intro x; use x; exact (firstAddInvSystem hφ).map_self x
  | le_succ_of_le h ih =>
    expose_names
    have : (kernelMorphismnm hφ (Nat.le_succ_of_le h)) = (kernelMorphismnm hφ h).comp (kernelMorphismnm hφ k.le_succ) := by ext x; simp
    rw [this]
    apply Function.Surjective.comp ih (firstSystemSurjBase hφ GradedSurjective k)

def inducedSESofInverseSystems (F'top : F'.N 0 = ⊤) (GradedSurjective : Function.Surjective (GradedModuleHom hφ)) : AddInverseSystemSES (kernelMorphismnm hφ) (FISTransitionMap F) (FISTransitionMap F') where
  ψ := {
    maps := fun n ↦ (CommDiagramOfSES_n hφ n).v₃.hom'.ker.subtype
    compatible := fun _ _ _ _ ↦ by rfl
  }
  ϕ := FISystemHom.of_comap_le hφ
  inj := fun n ↦ AddSubgroup.subtype_injective _
  mid := fun n ↦ by simp; rfl
  surj := by
    intro n
    have h₁ := (cokerv₃zero hφ F'top GradedSurjective n)
    let mapsn := (FISystemHom.of_comap_le hφ).maps n
    have h₂ := cokernelExact (@groupHomToGrpHom (AddCommGrp.of (FiltrationIS F n)) (AddCommGrp.of (FiltrationIS F' n)) mapsn)
    exact surjectiveOfExactZero h₁ h₂


lemma am10_23_i (hφ : ∀ n, F.N n ≤ (F'.N n).comap φ) :
  Function.Injective (GradedModuleHom hφ) → Function.Injective (FiltrationCompletionHom.of_comap_le hφ) := sorry

lemma am10_23_ii (F'top : F'.N 0 = ⊤) :
  Function.Surjective (GradedModuleHom hφ) → Function.Surjective (FiltrationCompletionHom.of_comap_le hφ) := by
  intro GradedSurjective
  apply am10_2_ii (inducedSESofInverseSystems hφ F'top GradedSurjective) (firstSystemSurj hφ GradedSurjective)
