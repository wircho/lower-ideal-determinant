import LowerIdealDeterminant.LDUExistence

/-!
# Lower-ideal determinant identity

No-pivot LDU existence applies to the generic matrix over the fraction field
of the integer polynomial ring. The checked determinant identity for unit LDU,
followed by descent and polynomial evaluation, therefore proves the identity
for every matrix over an arbitrary commutative ring and every `IsLowerIdeal`
family. `ShiftBridge.lean` proves that the thesis's elementary-lowering
assumption is equivalent to `IsLowerIdeal`.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {n d : ℕ}

/-- The theorem on the nonzero-leading-minor locus, directly from no-pivot
unit LDU and the already checked conditional determinant calculation. -/
theorem desiredIdentity_of_leadingPrincipalMinors_ne_zero
    {K : Type*} [Field K]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r : Fin n, leadingPrincipalMinor A r ≠ 0) :
    DesiredIdentity F A :=
  desiredIdentity_of_hasUnitLDU F hF A
    (hasUnitLDU_of_leadingPrincipalMinors_ne_zero A hA)

/-- The lower-ideal determinant identity for **every** matrix over **every
commutative ring**, including matrices with zero leading minors. -/
theorem ringDesiredIdentity_all
    {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (A : Matrix (Fin n) (Fin n) R) : RingDesiredIdentity F A := by
  apply ringDesiredIdentity_of_generic_hasUnitLDU_all F hF _ A
  apply hasUnitLDU_of_leadingPrincipalMinors_ne_zero
  exact leadingPrincipalMinor_generic_fraction_ne_zero

/-- The field-valued formulation in terms of the exterior-power compound
matrix; this is the unrestricted `DesiredIdentity` for lower ideals. -/
theorem desiredIdentity_all
    {K : Type*} [Field K]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (A : Matrix (Fin n) (Fin n) K) : DesiredIdentity F A :=
  (ringDesiredIdentity_iff_desiredIdentity F A).1 (ringDesiredIdentity_all F hF A)

end LowerIdealDeterminant
