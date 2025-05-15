import MyProject.Filtration.OurFiltration
import Mathlib.LinearAlgebra.SModEq

section

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H)
variable {σ : Type*}

/--
  Given two `A`-modules `M` and `N` and a map `φ : M →ₗ[A] N`, one can pullback a filtration `F` on `N`
  to a filtration on `M` given by `Mₙ = φ⁻¹(Nₙ)`.
-/
def PullbackOurFiltration [SetLike σ H] [AddSubgroupClass σ H] (F : OurFiltration H σ) : OurFiltration G (AddSubgroup G) where
  N := fun n ↦ ((AddSubgroup.ofClass (F.N n)).comap φ)
  mono := fun n ↦ AddSubgroup.comap_mono (F.mono n)

/--
  Given two `A`-modules `M` and `N` and a map `φ : M →ₗ[A] N`, one can pushforward a filtration `F`
  on `M` to a filtration on `N` given by `Nₙ = φ(Mₙ)`.
-/
def PushforwardOurFiltration [SetLike σ G] [AddSubgroupClass σ G] (F : OurFiltration G σ) : OurFiltration H (AddSubgroup H) where
  N := fun n ↦ ((AddSubgroup.ofClass (F.N n)).map φ)
  mono := fun n ↦ AddSubgroup.map_mono (F.mono n)

end
