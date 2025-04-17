import Mathlib.RingTheory.AdicCompletion.Algebra

variable {A : Type*} [CommRing A] (I : Ideal A)

/--
  I adic completion of J = I.adicCompletion J.  Extension of J into I-adic completion via induced algebra map.
-/
def Ideal.adicCompletion (J : Ideal A): Ideal (AdicCompletion I A) := Ideal.map (algebraMap A (AdicCompletion I A)) J

#check (AdicCompletion ((2):Ideal ℤ) ((2):Ideal ℤ))

/-
  Adic Complete
-/

class IsReallyAdicComplete  {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] where
  map_iso : Function.Bijective (AdicCompletion.of I M)


instance {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] [IsAdicComplete I M] : IsReallyAdicComplete I M := sorry

instance {A : Type u} [CommRing A] {I : Ideal A}: IsAdicComplete (I.adicCompletion I) (AdicCompletion I A) := sorry

instance {A : Type u} [CommRing A] {I : Ideal A}: IsReallyAdicComplete (I.adicCompletion I) (AdicCompletion I A) := sorry


-- IsReallyAdicComplete (AdicCompletion I A)
