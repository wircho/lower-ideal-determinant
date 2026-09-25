import CompoundDeterminant.Entries

open Matrix
open exteriorPower
open scoped Matrix
open Set
open Set.powersetCard

namespace CompoundDeterminant

section

variable {K : Type*} [Field K]
variable {n k : ℕ}

@[simp]
theorem compound_diagonal (d : Fin n → K) :
    compound k (Matrix.diagonal d) =
      Matrix.diagonal fun s : powersetCard (Fin n) k => ∏ i : Fin k, d ((ofFinEmbEquiv.symm s) i) := by
  classical
  ext s t
  by_cases hst : s = t
  · subst hst
    rw [compound_apply, Matrix.diagonal_apply_eq]
    rw [show (Matrix.diagonal d).submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm s) =
        Matrix.diagonal (d ∘ ofFinEmbEquiv.symm s) by
          simpa using Matrix.submatrix_diagonal_embedding d ((ofFinEmbEquiv.symm s).toEmbedding)]
    rw [Matrix.det_diagonal]
    simp [Function.comp_apply]
  · rw [compound_apply, Matrix.diagonal_apply_ne _ hst]
    obtain ⟨x, hxt, hxs⟩ :=
      (exists_mem_notMem_iff_ne t s).mp (by simpa [eq_comm] using hst)
    obtain ⟨j, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t x).mpr hxt
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    rw [Matrix.submatrix_apply, Matrix.diagonal_apply]
    split_ifs with h
    · exact (hxs ((mem_range_ofFinEmbEquiv_symm_iff_mem s ((ofFinEmbEquiv.symm t) j)).mp ⟨i, h⟩)).elim
    · rfl

end

end CompoundDeterminant
