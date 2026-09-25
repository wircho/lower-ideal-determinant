import LowerIdealDeterminant.LeadingMinors

/-!
# The determinant identity as a commutative-ring polynomial expression

The exterior-power implementation of `restrictedCompound` is field-valued.
For specialization, we also need a matrix of minors over an arbitrary
commutative ring. Its entries are the same minors, but this definition does
not use exterior powers or impose a field assumption.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {n d : ℕ}

/-- A chosen matrix of minors over an arbitrary commutative ring. -/
noncomputable def selectedMinors {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d)) (A : Matrix (Fin n) (Fin n) R) :
    Matrix {s : powersetCard (Fin n) d // s ∈ F}
      {s : powersetCard (Fin n) d // s ∈ F} R :=
  fun s t => (A.submatrix (ofFinEmbEquiv.symm s.val) (ofFinEmbEquiv.symm t.val)).det

@[simp] theorem selectedMinors_apply {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d)) (A : Matrix (Fin n) (Fin n) R)
    (s t : {s : powersetCard (Fin n) d // s ∈ F}) :
    selectedMinors F A s t =
      (A.submatrix (ofFinEmbEquiv.symm s.val) (ofFinEmbEquiv.symm t.val)).det :=
  rfl

/-- Taking selected minors commutes with any map of commutative rings. -/
theorem selectedMinors_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : Finset (powersetCard (Fin n) d))
    (A : Matrix (Fin n) (Fin n) R) :
    selectedMinors F (A.map f) = (selectedMinors F A).map f := by
  ext s t
  simp [selectedMinors, Matrix.submatrix_map, f.map_det]

/-- Over fields, the ring-valued definition agrees with the checked
exterior-power compound construction. -/
theorem selectedMinors_eq_restrictedCompound {K : Type*} [Field K]
    (F : Finset (powersetCard (Fin n) d)) (A : Matrix (Fin n) (Fin n) K) :
    selectedMinors F A = restrictedCompound F A := by
  ext s t
  simp

/-- A leading principal minor, defined without a field hypothesis. -/
noncomputable def ringLeadingPrincipalMinor {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (r : Fin n) : R :=
  (A.submatrix (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))
    (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))).det

@[simp] theorem ringLeadingPrincipalMinor_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin n) (Fin n) R) (r : Fin n) :
    ringLeadingPrincipalMinor (A.map f) r = f (ringLeadingPrincipalMinor A r) := by
  simp [ringLeadingPrincipalMinor, Matrix.submatrix_map, f.map_det]

/-- Ring-valued version of the target proposition, suitable for generic
polynomials, descent, and specialization. This is a definition, not a proof. -/
def RingDesiredIdentity {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d)) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (selectedMinors F A).det =
    ∏ r : Fin n, ringLeadingPrincipalMinor A r ^
      (incidenceCount F r - nextIncidenceCount F r)

/-- The ring-valued statement and the original field-valued statement are
literally the same formula after unfolding the two presentations. -/
theorem ringDesiredIdentity_iff_desiredIdentity {K : Type*} [Field K]
    (F : Finset (powersetCard (Fin n) d)) (A : Matrix (Fin n) (Fin n) K) :
    RingDesiredIdentity F A ↔ DesiredIdentity F A := by
  simp only [RingDesiredIdentity, DesiredIdentity, selectedMinors_eq_restrictedCompound]
  rfl

/-- An injective ring map reflects the determinant identity. In particular,
this will allow descent from a fraction field to an integral polynomial ring. -/
theorem ringDesiredIdentity_of_map_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (F : Finset (powersetCard (Fin n) d)) (A : Matrix (Fin n) (Fin n) R)
    (h : RingDesiredIdentity F (A.map f)) : RingDesiredIdentity F A := by
  apply hf
  simpa only [RingDesiredIdentity, selectedMinors_map, f.map_det,
    ringLeadingPrincipalMinor_map, map_prod, map_pow] using h

/-- Once an integral polynomial identity has been proved, it specializes to
any commutative coefficient ring. -/
theorem ringDesiredIdentity_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : Finset (powersetCard (Fin n) d))
    (A : Matrix (Fin n) (Fin n) R) (h : RingDesiredIdentity F A) :
    RingDesiredIdentity F (A.map f) := by
  unfold RingDesiredIdentity at h ⊢
  calc
    (selectedMinors F (A.map f)).det = f ((selectedMinors F A).det) := by
      rw [selectedMinors_map]
      exact (f.map_det _).symm
    _ = f (∏ r : Fin n, ringLeadingPrincipalMinor A r ^
        (incidenceCount F r - nextIncidenceCount F r)) := congrArg f h
    _ = ∏ r : Fin n, ringLeadingPrincipalMinor (A.map f) r ^
        (incidenceCount F r - nextIncidenceCount F r) := by
      simp only [map_prod, map_pow, ringLeadingPrincipalMinor_map]

end LowerIdealDeterminant
