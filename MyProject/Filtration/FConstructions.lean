import MyProject.Filtration.OurFiltration
import Mathlib.LinearAlgebra.SModEq

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
