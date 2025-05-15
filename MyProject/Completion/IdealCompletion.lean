import Mathlib.RingTheory.AdicCompletion.Algebra

variable {A : Type*} [CommRing A] (I : Ideal A)

/--
  I adic completion of J = I.adicCompletion J.  Extension of J into I-adic completion via induced map.
-/
def Ideal.adicCompletion (J : Ideal A): Ideal (AdicCompletion I A) :=
  Ideal.map (AdicCompletion.of I A) J
