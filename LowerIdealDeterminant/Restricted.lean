import LowerIdealDeterminant.Family
import CompoundDeterminant.Diagonal
import CompoundDeterminant.Identity

/-!
# A selected principal submatrix of the compound matrix

Unlike the full compound matrix, this restricted matrix need not be multiplicative
for arbitrary pairs of matrices. Multiplicativity will be recovered under a
triangular-support hypothesis in the next stage of the project.
-/

namespace LowerIdealDeterminant

open Matrix
open Set
open Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

/-- The matrix whose `(s,t)`-entry is the minor of `A` with row set `s` and
column set `t`, for `s,t` in the chosen family. -/
noncomputable def restrictedCompound (F : Finset (powersetCard (Fin n) d))
    (A : Matrix (Fin n) (Fin n) K) :
    Matrix {s : powersetCard (Fin n) d // s ∈ F}
      {s : powersetCard (Fin n) d // s ∈ F} K :=
  (CompoundDeterminant.compound d A).submatrix Subtype.val Subtype.val

@[simp]
theorem restrictedCompound_apply (F : Finset (powersetCard (Fin n) d))
    (A : Matrix (Fin n) (Fin n) K)
    (s t : {s : powersetCard (Fin n) d // s ∈ F}) :
    restrictedCompound F A s t =
      (A.submatrix (ofFinEmbEquiv.symm s.val) (ofFinEmbEquiv.symm t.val)).det := by
  exact CompoundDeterminant.compound_apply A s.val t.val

@[simp]
theorem restrictedCompound_one (F : Finset (powersetCard (Fin n) d)) :
    restrictedCompound F (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  classical
  rw [restrictedCompound, CompoundDeterminant.compound_one]
  exact Matrix.submatrix_one Subtype.val Subtype.val_injective

/-- For a diagonal matrix, the restricted compound is diagonal too. -/
theorem restrictedCompound_diagonal (F : Finset (powersetCard (Fin n) d))
    (a : Fin n → K) :
    restrictedCompound F (Matrix.diagonal a) =
      Matrix.diagonal (fun s : {s : powersetCard (Fin n) d // s ∈ F} ↦
        ∏ i : Fin d, a ((ofFinEmbEquiv.symm s.val) i)) := by
  classical
  rw [restrictedCompound, CompoundDeterminant.compound_diagonal]
  exact Matrix.submatrix_diagonal
    (fun s : powersetCard (Fin n) d ↦ ∏ i : Fin d, a ((ofFinEmbEquiv.symm s) i)) (Subtype.val :
    {s : powersetCard (Fin n) d // s ∈ F} → powersetCard (Fin n) d) Subtype.val_injective

/-- First checked special case of the eventual determinant identity. -/
theorem det_restrictedCompound_diagonal (F : Finset (powersetCard (Fin n) d))
    (a : Fin n → K) :
    (restrictedCompound F (Matrix.diagonal a)).det =
      ∏ s : {s : powersetCard (Fin n) d // s ∈ F},
        ∏ i : Fin d, a ((ofFinEmbEquiv.symm s.val) i) := by
  classical
  rw [restrictedCompound_diagonal, Matrix.det_diagonal]

end LowerIdealDeterminant
