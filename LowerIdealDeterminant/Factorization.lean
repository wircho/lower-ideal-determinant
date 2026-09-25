import LowerIdealDeterminant.DiagonalCounts

/-!
# Restricted determinant of a factored matrix

This is the algebraic portion of the proposed LDU proof that needs only a
lower-triangular left factor. It makes no assertion that an arbitrary matrix
admits such a factorization.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

/-- For an explicitly given `L * D * U`, restricted multiplicativity and the
incidence-count formula reduce the determinant to the two outer factors. -/
theorem det_restrictedCompound_lower_diagonal_upper
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hL : L.BlockTriangular OrderDual.toDual) :
    (restrictedCompound F (L * Matrix.diagonal a * U)).det =
      (restrictedCompound F L).det *
        (∏ i : Fin n, a i ^ incidenceCount F i) *
        (restrictedCompound F U).det := by
  rw [mul_assoc,
    det_restrictedCompound_mul_lowerTriangular F hF L (Matrix.diagonal a * U) hL,
    det_restrictedCompound_mul_lowerTriangular F hF (Matrix.diagonal a) U
      (Matrix.blockTriangular_diagonal a),
    det_restrictedCompound_diagonal_incidence, mul_assoc]

end LowerIdealDeterminant
