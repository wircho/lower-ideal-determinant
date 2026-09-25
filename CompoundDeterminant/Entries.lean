import CompoundDeterminant.Compound

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
theorem compound_apply (A : Matrix (Fin n) (Fin n) K)
    (s t : powersetCard (Fin n) k) :
    compound k A s t =
      (A.submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)).det := by
  classical
  let B := (Pi.basisFun K (Fin n)).exteriorPower k
  rw [compound, LinearMap.toMatrix_apply]
  change B.repr (exteriorPower.map k (Matrix.toLin' A) (B t)) s =
    (A.submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)).det
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.toLin'_apply]

end

end CompoundDeterminant
