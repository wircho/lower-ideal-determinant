import CompoundDeterminant.Diagonal

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
theorem compound_one :
    compound k (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simpa using (compound_diagonal (K := K) (n := n) (k := k) (fun _ => (1 : K)))

@[simp]
theorem det_compound_one :
    (compound k (1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
  rw [compound_one, Matrix.det_one]

end

end CompoundDeterminant
