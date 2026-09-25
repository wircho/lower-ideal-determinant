import LowerIdealDeterminant.LDUBlocks

/-!
# No-pivot LDU existence from leading principal minors

The inductive step separates the final row and column. The leading block
inherits the prefix hypotheses, hence factors by induction and is invertible.
The block assembly lemma then constructs the larger factors. No row or column
permutation is used.
-/

namespace LowerIdealDeterminant

open Matrix

variable {K : Type*} [Field K]

private theorem hasUnitLDU_succ {n : ℕ}
    (ih : ∀ (B : Matrix (Fin n) (Fin n) K),
      (∀ r : Fin n, leadingPrincipalMinor B r ≠ 0) → HasUnitLDU B)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA : ∀ r : Fin (n + 1), leadingPrincipalMinor A r ≠ 0) :
    HasUnitLDU A := by
  classical
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  let M := A.submatrix e e
  let B := leadingBlock A
  let b := M.toBlocks₁₂
  let c := M.toBlocks₂₁
  let d := M.toBlocks₂₂
  have hM : M = Matrix.fromBlocks B b c d := by
    rw [← Matrix.fromBlocks_toBlocks M]
    congr 1
  have hB : ∀ r : Fin n, leadingPrincipalMinor B r ≠ 0 := by
    intro r
    rw [leadingPrincipalMinor_leadingBlock]
    exact hA r.castSucc
  obtain ⟨L, U, a, hL, hU, hLdiag, hUdiag, hfact⟩ := ih B hB
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B
    (isUnit_iff_ne_zero.mpr (leadingBlock_det_ne_zero_of_prefix A hA))
  let X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) K :=
    Matrix.fromBlocks L 0 (c * ⅟B * L) 1
  let Y : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) K :=
    Matrix.fromBlocks U (U * (⅟B * b)) 0 1
  let piv : Fin n ⊕ Fin 1 → K :=
    Sum.elim a (fun _ => (d - c * ⅟B * b) 0 0)
  let L' := X.submatrix e.symm e.symm
  let U' := Y.submatrix e.symm e.symm
  let a' : Fin (n + 1) → K := piv ∘ e.symm
  have hAeq : A = (Matrix.fromBlocks B b c d).submatrix e.symm e.symm := by
    rw [← hM]
    simp [M, Matrix.submatrix_submatrix]
  refine ⟨L', U', a', ?_, ?_, ?_, ?_, ?_⟩
  · exact blockLower_reindex_lower L (c * ⅟B * L) hL
  · exact blockUpper_reindex_upper U (U * (⅟B * b)) hU
  · intro i
    exact blockLower_reindex_unit L (c * ⅟B * L) hLdiag i
  · intro i
    exact blockUpper_reindex_unit U (U * (⅟B * b)) hUdiag i
  · calc
      A = (Matrix.fromBlocks B b c d).submatrix e.symm e.symm := hAeq
      _ = (X * Matrix.diagonal piv * Y).submatrix e.symm e.symm := by
        rw [fromBlocks_eq_unit_diagonal_unit_of_invertible_leading B b c d L U a hfact]
      _ = L' * Matrix.diagonal a' * U' := by
        change (X * Matrix.diagonal piv * Y).submatrix e.symm e.symm =
          (X.submatrix e.symm e.symm * Matrix.diagonal (piv ∘ e.symm)) *
            Y.submatrix e.symm e.symm
        rw [← Matrix.submatrix_diagonal_equiv piv e.symm,
          Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- Every matrix over a field whose leading principal minors are nonzero
admits a no-pivot factorization into a unit lower-triangular matrix, a
diagonal matrix, and a unit upper-triangular matrix. -/
theorem hasUnitLDU_of_leadingPrincipalMinors_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r : Fin n, leadingPrincipalMinor A r ≠ 0) : HasUnitLDU A := by
  induction n with
  | zero =>
      refine ⟨1, 1, fun _ => 1, Matrix.blockTriangular_one,
        Matrix.blockTriangular_one, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · subsingleton
  | succ n ih =>
      exact hasUnitLDU_succ ih A hA

end LowerIdealDeterminant
