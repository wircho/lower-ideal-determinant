import LowerIdealDeterminant.GenericMinors
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Block assembly for a no-pivot LDU factorization

The inductive LDU construction will split off the last row and column. If the
leading block `B` is invertible and has a unit-LDU decomposition, the Schur
complement is a single pivot; its factorization can be assembled with the
previous factors. The algebraic identity below isolates this assembly before
reindexing `Fin n ⊕ Fin 1` back to `Fin (n+1)` and checking triangularity.
-/

namespace LowerIdealDeterminant

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The leading `n × n` block of a matrix of size `n+1`. -/
def leadingBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin n) K :=
  A.submatrix Fin.castSucc Fin.castSucc

/-- All nonempty prefixes of the leading block are also prefixes of the
original matrix. -/
theorem leadingPrincipalMinor_leadingBlock
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (r : Fin n) :
    leadingPrincipalMinor (leadingBlock A) r =
      leadingPrincipalMinor A r.castSucc := by
  unfold leadingPrincipalMinor leadingBlock
  rw [Matrix.submatrix_submatrix]
  rfl

omit [Field K] in
/-- Under the standard block reindexing, the top-left block is exactly the
leading block, rather than merely an isomorphic matrix. -/
theorem toBlocks₁₁_finSumFinEquiv
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (A.submatrix (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
      finSumFinEquiv).toBlocks₁₁ = leadingBlock A := by
  ext i j
  rfl

/-- The last leading principal minor of a nonempty square matrix is its
determinant. -/
theorem leadingPrincipalMinor_last
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    leadingPrincipalMinor A (Fin.last n) = A.det := by
  unfold leadingPrincipalMinor
  congr 1

/-- The leading block is invertible if the original matrix has nonzero
leading minors. We state the nonempty-block case; the empty block is
invertible without hypotheses. -/
theorem leadingBlock_det_ne_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (h : ∀ r : Fin (n + 2), leadingPrincipalMinor A r ≠ 0) :
    (leadingBlock A).det ≠ 0 := by
  rw [← leadingPrincipalMinor_last (leadingBlock A)]
  rw [leadingPrincipalMinor_leadingBlock]
  exact h (Fin.last n).castSucc

/-- The leading block is invertible at every step of no-pivot elimination,
including the empty-block base case. -/
theorem leadingBlock_det_ne_zero_of_prefix
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : ∀ r : Fin (n + 1), leadingPrincipalMinor A r ≠ 0) :
    (leadingBlock A).det ≠ 0 := by
  cases n with
  | zero => simp [leadingBlock]
  | succ m => exact leadingBlock_det_ne_zero A h

/-- A lower triangular block with a final singleton block remains lower
triangular under the standard `Fin n ⊕ Fin 1 ≃ Fin (n+1)` reindexing. -/
theorem blockLower_reindex_lower
    (L : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin 1) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual) :
    ((Matrix.fromBlocks L 0 C 1).submatrix
      (finSumFinEquiv.symm : Fin (n + 1) ≃ Fin n ⊕ Fin 1)
      finSumFinEquiv.symm).BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  cases hi : finSumFinEquiv.symm i with
  | inl p =>
    cases hj : finSumFinEquiv.symm j with
    | inl q =>
      have hpq : p < q := by
        have hi' : i = finSumFinEquiv (Sum.inl p) := by
          have := congrArg finSumFinEquiv hi
          simpa using this
        have hj' : j = finSumFinEquiv (Sum.inl q) := by
          have := congrArg finSumFinEquiv hj
          simpa using this
        simpa [hi', hj', finSumFinEquiv_apply_left] using hij
      simpa [Matrix.submatrix_apply, hi, hj] using hL hpq
    | inr q =>
      simp [Matrix.submatrix_apply, hi, hj]
  | inr p =>
    cases hj : finSumFinEquiv.symm j with
    | inl q =>
      have hi' : i = finSumFinEquiv (Sum.inr p) := by
        have := congrArg finSumFinEquiv hi
        simpa using this
      have hj' : j = finSumFinEquiv (Sum.inl q) := by
        have := congrArg finSumFinEquiv hj
        simpa using this
      have : False := by
        have hbad : (n + (p : ℕ)) < (q : ℕ) := by
          simpa only [hi', hj', finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] using hij
        have hq := q.isLt
        omega
      exact this.elim
    | inr q =>
      have hpq : p < q := by
        have hi' : i = finSumFinEquiv (Sum.inr p) := by
          have := congrArg finSumFinEquiv hi
          simpa using this
        have hj' : j = finSumFinEquiv (Sum.inr q) := by
          have := congrArg finSumFinEquiv hj
          simpa using this
        simpa [hi', hj', finSumFinEquiv_apply_right] using hij
      have hpq' : p = q := Subsingleton.elim _ _
      exact (lt_irrefl q (hpq' ▸ hpq)).elim

/-- The upper-block analogue, by transposing the lower-block lemma. -/
theorem blockUpper_reindex_upper
    (U : Matrix (Fin n) (Fin n) K) (V : Matrix (Fin n) (Fin 1) K)
    (hU : U.BlockTriangular id) :
    ((Matrix.fromBlocks U V 0 1).submatrix
      (finSumFinEquiv.symm : Fin (n + 1) ≃ Fin n ⊕ Fin 1)
      finSumFinEquiv.symm).BlockTriangular id := by
  have hT : Uᵀ.BlockTriangular OrderDual.toDual := by
    simpa using hU.transpose
  have h := (blockLower_reindex_lower Uᵀ Vᵀ hT).transpose
  simpa [Matrix.transpose_submatrix, Matrix.fromBlocks_transpose] using h

/-- Unit diagonal of the reindexed lower block. -/
theorem blockLower_reindex_unit
    (L : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin 1) (Fin n) K)
    (hdiag : ∀ i : Fin n, L i i = 1) (i : Fin (n + 1)) :
    (Matrix.fromBlocks L 0 C 1).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm i i = 1 := by
  cases hi : finSumFinEquiv.symm i with
  | inl p => simpa [Matrix.submatrix_apply, hi] using hdiag p
  | inr p => simp [Matrix.submatrix_apply, hi]

/-- Unit diagonal of the reindexed upper block. -/
theorem blockUpper_reindex_unit
    (U : Matrix (Fin n) (Fin n) K) (V : Matrix (Fin n) (Fin 1) K)
    (hdiag : ∀ i : Fin n, U i i = 1) (i : Fin (n + 1)) :
    (Matrix.fromBlocks U V 0 1).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm i i = 1 := by
  cases hi : finSumFinEquiv.symm i with
  | inl p => simpa [Matrix.submatrix_apply, hi] using hdiag p
  | inr p => simp [Matrix.submatrix_apply, hi]

/-- Assemble a block LDU from a factorization of the invertible leading block.
The bottom-right Schur complement is a `1 × 1` matrix; the displayed middle
factor is block diagonal but has not yet been identified with a diagonal
matrix on `Fin (n+1)`. -/
theorem fromBlocks_eq_LDU_of_invertible_leading
    (B : Matrix (Fin n) (Fin n) K)
    (b : Matrix (Fin n) (Fin 1) K) (c : Matrix (Fin 1) (Fin n) K)
    (d : Matrix (Fin 1) (Fin 1) K) [Invertible B]
    (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hB : B = L * Matrix.diagonal a * U) :
    Matrix.fromBlocks B b c d =
      Matrix.fromBlocks L 0 (c * ⅟B * L) 1 *
      Matrix.fromBlocks (Matrix.diagonal a) 0 0 (d - c * ⅟B * b) *
      Matrix.fromBlocks U (U * (⅟B * b)) 0 1 := by
  let X := c * ⅟B
  let Y := ⅟B * b
  let S := d - c * ⅟B * b
  have hX : X * B = c := by
    dsimp [X]
    rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  have hY : B * Y = b := by
    dsimp [Y]
    rw [Matrix.mul_invOf_cancel_left]
  have hS : X * B * Y + S = d := by
    dsimp [S]
    rw [hX, Matrix.mul_assoc]
    abel
  change Matrix.fromBlocks B b c d =
    Matrix.fromBlocks L 0 (X * L) 1 *
      Matrix.fromBlocks (Matrix.diagonal a) 0 0 S *
      Matrix.fromBlocks U (U * Y) 0 1
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · calc
      B = L * Matrix.diagonal a * U := hB
      _ = (L * Matrix.diagonal a) * U := by rw [Matrix.mul_assoc]
  constructor
  · calc
      b = B * Y := hY.symm
      _ = (L * Matrix.diagonal a) * (U * Y) := by rw [hB, Matrix.mul_assoc]
  constructor
  · calc
      c = X * B := hX.symm
      _ = X * (L * Matrix.diagonal a * U) := congrArg (X * ·) hB
      _ = (X * L * Matrix.diagonal a) * U := by simp only [Matrix.mul_assoc]
  · calc
      d = X * B * Y + S := hS.symm
      _ = X * (L * Matrix.diagonal a * U) * Y + S := by
        exact congrArg (fun T => X * T * Y + S) hB
      _ = (X * L * Matrix.diagonal a) * (U * Y) + S := by
        simp only [Matrix.mul_assoc]

/-- A `1 × 1` Schur complement is itself a diagonal matrix. -/
private theorem finOne_matrix_diagonal (S : Matrix (Fin 1) (Fin 1) K) :
    S = Matrix.diagonal (fun _ => S 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- The block assembly above has an honest diagonal middle factor; only
reindexing and verification of unit triangularity remain for the induction. -/
theorem fromBlocks_eq_unit_diagonal_unit_of_invertible_leading
    (B : Matrix (Fin n) (Fin n) K)
    (b : Matrix (Fin n) (Fin 1) K) (c : Matrix (Fin 1) (Fin n) K)
    (d : Matrix (Fin 1) (Fin 1) K) [Invertible B]
    (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hB : B = L * Matrix.diagonal a * U) :
    Matrix.fromBlocks B b c d =
      Matrix.fromBlocks L 0 (c * ⅟B * L) 1 *
      Matrix.diagonal (Sum.elim a (fun _ => (d - c * ⅟B * b) 0 0)) *
      Matrix.fromBlocks U (U * (⅟B * b)) 0 1 := by
  rw [← Matrix.fromBlocks_diagonal a (fun _ => (d - c * ⅟B * b) 0 0),
    ← finOne_matrix_diagonal (d - c * ⅟B * b)]
  exact fromBlocks_eq_LDU_of_invertible_leading B b c d L U a hB

end LowerIdealDeterminant
