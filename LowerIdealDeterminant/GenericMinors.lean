import LowerIdealDeterminant.RingMinors
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Generic matrices and polynomial specialization

The matrix with distinct indeterminates in each position is the intended
bridge between the nonzero-leading-minor locus and *all* matrices. The
results here establish that its leading minors are nonzero and that **if**
the ring-valued identity holds generically, then it holds after evaluation
in any commutative ring. The generic identity itself is not asserted here.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {n d : ℕ}

/-- Every leading principal minor of the generic integer matrix is nonzero:
evaluate all entries at the identity matrix. -/
theorem ringLeadingPrincipalMinor_generic_ne_zero (r : Fin n) :
    ringLeadingPrincipalMinor (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ) r ≠ 0 := by
  classical
  let ev : MvPolynomial (Fin n × Fin n) ℤ →+* ℤ :=
    MvPolynomial.eval fun p => (1 : Matrix (Fin n) (Fin n) ℤ) p.1 p.2
  have heval : (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map ev = 1 := by
    simpa only [ev] using
      (Matrix.mvPolynomialX_mapMatrix_eval (1 : Matrix (Fin n) (Fin n) ℤ))
  intro hz
  have h : ringLeadingPrincipalMinor (1 : Matrix (Fin n) (Fin n) ℤ) r = 0 := by
    calc
      ringLeadingPrincipalMinor (1 : Matrix (Fin n) (Fin n) ℤ) r =
          ringLeadingPrincipalMinor ((Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map ev) r := by
            rw [heval]
      _ = ev (ringLeadingPrincipalMinor (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ) r) :=
        ringLeadingPrincipalMinor_map ev _ r
      _ = 0 := by rw [hz, map_zero]
  have hone : ringLeadingPrincipalMinor (1 : Matrix (Fin n) (Fin n) ℤ) r = 1 := by
    unfold ringLeadingPrincipalMinor
    rw [Matrix.submatrix_one _ (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt)).injective,
      Matrix.det_one]
  exact one_ne_zero (hone.symm.trans h)

/-- A **conditional** specialization theorem. Its hypothesis is the as-yet
unproved identity for the generic matrix, not an axiom or a hidden proof of it. -/
theorem ringDesiredIdentity_of_generic {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d))
    (hgeneric : RingDesiredIdentity F (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ))
    (A : Matrix (Fin n) (Fin n) R) : RingDesiredIdentity F A := by
  let ev : MvPolynomial (Fin n × Fin n) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) fun p => A p.1 p.2
  have heval : (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map ev = A := by
    simpa only [ev] using
      (Matrix.mvPolynomialX_map_eval₂ (Int.castRingHom R) A)
  rw [← heval]
  exact ringDesiredIdentity_map ev F _ hgeneric

/-- The generic matrix retains nonzero leading minors in its fraction field. -/
theorem leadingPrincipalMinor_generic_fraction_ne_zero (r : Fin n) :
    leadingPrincipalMinor
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map
        (algebraMap (MvPolynomial (Fin n × Fin n) ℤ)
          (FractionRing (MvPolynomial (Fin n × Fin n) ℤ)))) r ≠ 0 := by
  let P := MvPolynomial (Fin n × Fin n) ℤ
  let f : P →+* FractionRing P := algebraMap P (FractionRing P)
  change ringLeadingPrincipalMinor
    ((Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map f) r ≠ 0
  rw [ringLeadingPrincipalMinor_map]
  intro hz
  have hf : Function.Injective f := IsFractionRing.injective P (FractionRing P)
  have heq : f (ringLeadingPrincipalMinor (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ) r) =
      f 0 := by simpa only [map_zero] using hz
  exact ringLeadingPrincipalMinor_generic_ne_zero r (hf heq)

/-- This conditional theorem assumes a unit-LDU factorization of the generic
matrix over its fraction field. `LDUExistence.lean` supplies that factorization,
and `Theorem.lean` proves the unrestricted identity. -/
theorem ringDesiredIdentity_of_generic_hasUnitLDU
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (hLDU : HasUnitLDU
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map
        (algebraMap (MvPolynomial (Fin n × Fin n) ℤ)
          (FractionRing (MvPolynomial (Fin n × Fin n) ℤ))))) :
    RingDesiredIdentity F (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ) := by
  let P := MvPolynomial (Fin n × Fin n) ℤ
  let f : P →+* FractionRing P := algebraMap P (FractionRing P)
  apply ringDesiredIdentity_of_map_injective f (IsFractionRing.injective P (FractionRing P))
  exact (ringDesiredIdentity_iff_desiredIdentity F _).2
    (desiredIdentity_of_hasUnitLDU F hF _ hLDU)

/-- Conditional all-rings result: once generic no-pivot LDU is constructed,
we can descend and specialize the identity to every commutative ring. -/
theorem ringDesiredIdentity_of_generic_hasUnitLDU_all
    {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (hLDU : HasUnitLDU
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).map
        (algebraMap (MvPolynomial (Fin n × Fin n) ℤ)
          (FractionRing (MvPolynomial (Fin n × Fin n) ℤ)))))
    (A : Matrix (Fin n) (Fin n) R) : RingDesiredIdentity F A :=
  ringDesiredIdentity_of_generic F
    (ringDesiredIdentity_of_generic_hasUnitLDU F hF hLDU) A

end LowerIdealDeterminant
