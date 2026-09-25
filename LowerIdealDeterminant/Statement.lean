import LowerIdealDeterminant.Product

/-!
# Field-valued determinant identity

`DesiredIdentity` names the formula as a proposition; its proof for all matrices
is in `Theorem.lean` and its elementary-lowering form is in `ShiftBridge.lean`.
We use zero-based `Fin n` indices: the factor at `r` is the leading principal
minor of size `r.val + 1`.
-/

namespace LowerIdealDeterminant

open Matrix
open Set
open Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

/-- The leading principal minor of size `r.val + 1`. -/
def leadingPrincipalMinor (A : Matrix (Fin n) (Fin n) K) (r : Fin n) : K :=
  (A.submatrix (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))
    (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))).det

/-- The occurrence count at the next coordinate, or zero past the last one. -/
noncomputable def nextIncidenceCount (F : Finset (powersetCard (Fin n) d))
    (r : Fin n) : ℕ :=
  if h : r.val + 1 < n then incidenceCount F ⟨r.val + 1, h⟩ else 0

/-- The exact target equality for a family and a matrix. A proof is expected
only when `IsLowerIdeal F` holds. This is a *definition of a proposition*,
not a proof or an axiom. -/
def DesiredIdentity (F : Finset (powersetCard (Fin n) d))
    (A : Matrix (Fin n) (Fin n) K) : Prop :=
  (restrictedCompound F A).det =
    ∏ r : Fin n, (leadingPrincipalMinor A r) ^
      (incidenceCount F r - nextIncidenceCount F r)

end LowerIdealDeterminant
