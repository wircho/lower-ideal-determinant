import Mathlib

open Matrix
open exteriorPower
open scoped Matrix
open Set
open Set.powersetCard

namespace CompoundDeterminant

section

variable {K : Type*} [Field K]
variable {n : ℕ}

noncomputable def compound (k : ℕ) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) K :=
  let B := (Pi.basisFun K (Fin n)).exteriorPower k
  LinearMap.toMatrix B B (exteriorPower.map k (Matrix.toLin' A))

@[simp]
theorem compound_mul (k : ℕ) (A B : Matrix (Fin n) (Fin n) K) :
    compound k (A * B) = compound k A * compound k B := by
  classical
  let Bk := (Pi.basisFun K (Fin n)).exteriorPower k
  simp only [compound, Matrix.toLin'_mul, exteriorPower.map_comp]
  simpa [Bk] using
    (LinearMap.toMatrix_comp (v₁ := Bk) (v₂ := Bk) (v₃ := Bk)
      (f := exteriorPower.map k (Matrix.toLin' A))
      (g := exteriorPower.map k (Matrix.toLin' B)))

@[simp]
theorem det_compound_mul (k : ℕ) (A B : Matrix (Fin n) (Fin n) K) :
    (compound k (A * B)).det = (compound k A).det * (compound k B).det := by
  rw [compound_mul, Matrix.det_mul]

end

end CompoundDeterminant
