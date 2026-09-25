import LowerIdealDeterminant.Factorization

/-!
# Unit-triangular factors

The sum of the indices in a subset strictly increases along proper
componentwise comparisons. We use that weight to split the restricted compound
into triangular blocks; equal-weight blocks are diagonal.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

/-- A rank function for the componentwise order on `d`-subsets. -/
def subsetWeight (s : powersetCard (Fin n) d) : ℕ :=
  ∑ i : Fin d, ((ofFinEmbEquiv.symm s) i).val

theorem subsetWeight_mono {s t : powersetCard (Fin n) d}
    (hst : ComponentwiseLE s t) : subsetWeight s ≤ subsetWeight t := by
  unfold subsetWeight
  exact Finset.sum_le_sum (fun i _ => hst i)

theorem subsetWeight_strict {s t : powersetCard (Fin n) d}
    (hst : ComponentwiseLE s t) (hne : s ≠ t) : subsetWeight s < subsetWeight t := by
  have hi : ∃ i : Fin d,
      (ofFinEmbEquiv.symm s) i ≠ (ofFinEmbEquiv.symm t) i := by
    by_contra h
    push Not at h
    exact hne (ofFinEmbEquiv.symm.injective (by ext i; exact congrArg Fin.val (h i)))
  obtain ⟨i, hi⟩ := hi
  unfold subsetWeight
  apply Finset.sum_lt_sum
  · intro j _
    exact hst j
  · have hval : ((ofFinEmbEquiv.symm s) i).val ≠
        ((ofFinEmbEquiv.symm t) i).val := fun he => hi (Fin.ext he)
    exact ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hst i) hval⟩

/-- Every principal minor of a unit lower-triangular matrix is one. -/
theorem compound_self_eq_one_of_unit_lowerTriangular
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i : Fin n, L i i = 1)
    (s : powersetCard (Fin n) d) :
    CompoundDeterminant.compound d L s s = 1 := by
  classical
  rw [CompoundDeterminant.compound_apply,
    Matrix.det_of_lowerTriangular _ (by
      intro i j hij
      exact hL ((ofFinEmbEquiv.symm s).strictMono hij))]
  simp [hdiag]

/-- Selecting any family of minors of a unit lower-triangular matrix yields
a matrix of determinant one. The family need not be a lower ideal here. -/
theorem det_restrictedCompound_unit_lowerTriangular
    (F : Finset (powersetCard (Fin n) d))
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i : Fin n, L i i = 1) :
    (restrictedCompound F L).det = 1 := by
  classical
  let M := restrictedCompound F L
  let b : {s : powersetCard (Fin n) d // s ∈ F} → ℕᵒᵈ :=
    fun s => OrderDual.toDual (subsetWeight s.val)
  have hb : M.BlockTriangular b := by
    intro s t h
    have hw : subsetWeight s.val < subsetWeight t.val := h
    change CompoundDeterminant.compound d L s.val t.val = 0
    apply compound_eq_zero_of_lowerTriangular L (fun i j hij => hL hij)
    intro hts
    exact (not_lt_of_ge (subsetWeight_mono hts)) hw
  have hblock (k : ℕᵒᵈ) : M.toSquareBlock b k = 1 := by
    ext s t
    change M s.val t.val = (1 : Matrix _ _ K) s t
    by_cases he : s = t
    · subst t
      change CompoundDeterminant.compound d L s.val.val s.val.val =
        (1 : Matrix _ _ K) s s
      rw [compound_self_eq_one_of_unit_lowerTriangular L hL hdiag]
      simp
    · have hw : subsetWeight s.val.val = subsetWeight t.val.val :=
        congrArg OrderDual.ofDual (s.property.trans t.property.symm)
      have hne : s.val.val ≠ t.val.val := by
        intro h
        exact he (Subtype.ext (Subtype.ext h))
      have hnot : ¬ ComponentwiseLE t.val.val s.val.val := by
        intro hts
        exact (ne_of_lt (subsetWeight_strict hts hne.symm)) hw.symm
      change CompoundDeterminant.compound d L s.val.val t.val.val =
        (1 : Matrix _ _ K) s t
      rw [compound_eq_zero_of_lowerTriangular L (fun i j hij => hL hij)
        s.val.val t.val.val hnot, Matrix.one_apply_ne he]
  rw [hb.det]
  simp [hblock]

/-- Restriction of the compound commutes with transposition. -/
theorem restrictedCompound_transpose (F : Finset (powersetCard (Fin n) d))
    (A : Matrix (Fin n) (Fin n) K) :
    restrictedCompound F Aᵀ = (restrictedCompound F A)ᵀ := by
  classical
  ext s t
  rw [restrictedCompound_apply, Matrix.transpose_apply, restrictedCompound_apply]
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]

/-- The upper-triangular case follows from the lower-triangular one. -/
theorem det_restrictedCompound_unit_upperTriangular
    (F : Finset (powersetCard (Fin n) d))
    (U : Matrix (Fin n) (Fin n) K)
    (hU : U.BlockTriangular id)
    (hdiag : ∀ i : Fin n, U i i = 1) :
    (restrictedCompound F U).det = 1 := by
  rw [← Matrix.det_transpose, ← restrictedCompound_transpose F U]
  exact det_restrictedCompound_unit_lowerTriangular F Uᵀ hU.transpose
    (fun i => hdiag i)

/-- The complete restricted determinant calculation for an explicitly given
unit-LDU factorization. This does not establish that every matrix has such a
factorization. -/
theorem det_restrictedCompound_unit_LDU
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (L U : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hL : L.BlockTriangular OrderDual.toDual)
    (hU : U.BlockTriangular id)
    (hLdiag : ∀ i : Fin n, L i i = 1)
    (hUdiag : ∀ i : Fin n, U i i = 1) :
    (restrictedCompound F (L * Matrix.diagonal a * U)).det =
      ∏ i : Fin n, a i ^ incidenceCount F i := by
  rw [det_restrictedCompound_lower_diagonal_upper F hF L U a hL,
    det_restrictedCompound_unit_lowerTriangular F L hL hLdiag,
    det_restrictedCompound_unit_upperTriangular F U hU hUdiag,
    one_mul, mul_one]

end LowerIdealDeterminant
