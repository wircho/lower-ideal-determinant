import LowerIdealDeterminant.IncidenceShift

/-!
# Leading principal minors of an explicitly factored matrix

For a lower-triangular left factor, initial rows of a matrix product only see
initial columns. Restricting the product to a leading principal block therefore
commutes with multiplication. This is not true for an arbitrary left factor.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {K : Type*} [Field K] {n : ℕ}

private theorem prefix_index_image (r : Fin n) :
    (Finset.univ : Finset (Fin n)).filter (fun k => k.val < r.val + 1) =
      (Finset.univ : Finset (Fin (r.val + 1))).map
        (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro hk
    exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
  · rintro ⟨i, rfl⟩
    exact i.isLt

/-- Leading-block restriction commutes with left multiplication by a lower
triangular matrix. -/
theorem prefix_submatrix_mul_lower
    (L B : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual) (r : Fin n) :
    (L * B).submatrix (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))
        (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt)) =
      (L.submatrix (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))
        (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))) *
      (B.submatrix (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))
        (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))) := by
  classical
  let f := Fin.castLEEmb (Nat.succ_le_of_lt r.isLt)
  ext i j
  change (∑ k : Fin n, L (f i) k * B k (f j)) =
    ∑ k : Fin (r.val + 1), L (f i) (f k) * B (f k) (f j)
  calc
    (∑ k : Fin n, L (f i) k * B k (f j)) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k => k.val < r.val + 1), L (f i) k * B k (f j) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k _
          split_ifs with hk
          · rfl
          · have hzero : L (f i) k = 0 := hL (by
              change (f i).val < k.val
              have hi : (f i).val < r.val + 1 := i.isLt
              omega)
            simp [hzero]
    _ = ∑ k : Fin (r.val + 1), L (f i) (f k) * B (f k) (f j) := by
          rw [prefix_index_image r, Finset.sum_map]

/-- A leading principal minor is multiplicative when the left factor is
lower triangular. -/
theorem leadingPrincipalMinor_mul_lower
    (L B : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual) (r : Fin n) :
    leadingPrincipalMinor (L * B) r =
      leadingPrincipalMinor L r * leadingPrincipalMinor B r := by
  unfold leadingPrincipalMinor
  rw [prefix_submatrix_mul_lower L B hL r, Matrix.det_mul]

/-- Leading principal minors of a unit lower-triangular matrix are one. -/
theorem leadingPrincipalMinor_unit_lower
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i : Fin n, L i i = 1) (r : Fin n) :
    leadingPrincipalMinor L r = 1 := by
  classical
  unfold leadingPrincipalMinor
  rw [Matrix.det_of_lowerTriangular _ (by
    intro i j hij
    exact hL ((Fin.castLEOrderEmb (Nat.succ_le_of_lt r.isLt)).strictMono hij))]
  simp [hdiag]

/-- Leading principal minors of a unit upper-triangular matrix are one. -/
theorem leadingPrincipalMinor_unit_upper
    (U : Matrix (Fin n) (Fin n) K)
    (hU : U.BlockTriangular id)
    (hdiag : ∀ i : Fin n, U i i = 1) (r : Fin n) :
    leadingPrincipalMinor U r = 1 := by
  classical
  unfold leadingPrincipalMinor
  rw [Matrix.det_of_upperTriangular (by
    intro i j hij
    exact hU ((Fin.castLEOrderEmb (Nat.succ_le_of_lt r.isLt)).strictMono hij))]
  simp [hdiag]

/-- For an explicitly given unit LDU, every leading principal minor is the
corresponding prefix product of its diagonal entries. -/
theorem leadingPrincipalMinor_unit_LDU
    (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hL : L.BlockTriangular OrderDual.toDual)
    (hU : U.BlockTriangular id)
    (hLdiag : ∀ i : Fin n, L i i = 1)
    (hUdiag : ∀ i : Fin n, U i i = 1) (r : Fin n) :
    leadingPrincipalMinor (L * Matrix.diagonal a * U) r =
      ∏ i : Fin (r.val + 1), a (Fin.castLE (Nat.succ_le_of_lt r.isLt) i) := by
  rw [mul_assoc, leadingPrincipalMinor_mul_lower L (Matrix.diagonal a * U) hL r,
    leadingPrincipalMinor_mul_lower (Matrix.diagonal a) U
      (Matrix.blockTriangular_diagonal a) r,
    leadingPrincipalMinor_unit_lower L hL hLdiag r,
    leadingPrincipalMinor_unit_upper U hU hUdiag r,
    leadingPrincipalMinor_diagonal, one_mul, mul_one]

/-- The target determinant identity for **any explicitly given** unit LDU
factorization. No nonzero-pivot hypothesis is needed for this conditional
statement, but existence of such a factorization is not proved here. -/
theorem desiredIdentity_unit_LDU {d : ℕ}
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hL : L.BlockTriangular OrderDual.toDual)
    (hU : U.BlockTriangular id)
    (hLdiag : ∀ i : Fin n, L i i = 1)
    (hUdiag : ∀ i : Fin n, U i i = 1) :
    DesiredIdentity F (L * Matrix.diagonal a * U) := by
  unfold DesiredIdentity
  rw [det_restrictedCompound_unit_LDU F hF L U a hL hU hLdiag hUdiag]
  rw [← prod_fin_prefix_pow_sub a (incidenceCount F) (nextIncidenceCount_le F hF)]
  apply Finset.prod_congr rfl
  intro r _
  rw [leadingPrincipalMinor_unit_LDU L U a hL hU hLdiag hUdiag r,
    nextIncidenceCount]

/-- Having a unit lower-diagonal-upper factorization. Existence for every
matrix with nonzero leading principal minors is a separate, open task. -/
def HasUnitLDU (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K),
    L.BlockTriangular OrderDual.toDual ∧ U.BlockTriangular id ∧
      (∀ i : Fin n, L i i = 1) ∧ (∀ i : Fin n, U i i = 1) ∧
        A = L * Matrix.diagonal a * U

/-- The full target identity holds for matrices equipped with a unit-LDU
factorization. It remains to prove factorization existence and then remove
pivot-nonvanishing assumptions for arbitrary matrices. -/
theorem desiredIdentity_of_hasUnitLDU {d : ℕ}
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (A : Matrix (Fin n) (Fin n) K) (hA : HasUnitLDU A) :
    DesiredIdentity F A := by
  rcases hA with ⟨L, U, a, hL, hU, hLdiag, hUdiag, rfl⟩
  exact desiredIdentity_unit_LDU F hF L U a hL hU hLdiag hUdiag

end LowerIdealDeterminant
