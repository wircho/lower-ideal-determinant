import LowerIdealDeterminant.Restricted

/-!
# Restriction and matrix products

Selecting a principal submatrix does not generally preserve multiplication. The
statement below isolates the support condition that makes it work. In the final
proof, lower triangular matrices will satisfy this condition for lower ideals.
-/

namespace LowerIdealDeterminant

open Matrix
open Set
open Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

/-- Restricting a compound product to a family is multiplicative if the
compound of the left factor has no entries leading out of the family. -/
theorem restrictedCompound_mul_of_support
    (F : Finset (powersetCard (Fin n) d))
    (A B : Matrix (Fin n) (Fin n) K)
    (h : ∀ (s : {s : powersetCard (Fin n) d // s ∈ F})
      (u : powersetCard (Fin n) d), u ∉ F →
        CompoundDeterminant.compound d A s.val u = 0) :
    restrictedCompound F (A * B) = restrictedCompound F A * restrictedCompound F B := by
  classical
  ext s t
  simp only [restrictedCompound, Matrix.submatrix_apply, CompoundDeterminant.compound_mul,
    Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun u : powersetCard (Fin n) d => u ∈ F)
    (fun u => CompoundDeterminant.compound d A s.val u *
      CompoundDeterminant.compound d B u t.val)]
  have hz : (∑ u : {u : powersetCard (Fin n) d // u ∉ F},
      CompoundDeterminant.compound d A s.val u.val *
        CompoundDeterminant.compound d B u.val t.val) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    rw [h s u.val u.property, zero_mul]
  rw [hz, add_zero]
  apply Finset.sum_congr
  · ext u
    simp
  · intro u _
    rfl

/-- Under the same support hypothesis, determinants multiply. -/
theorem det_restrictedCompound_mul_of_support
    (F : Finset (powersetCard (Fin n) d))
    (A B : Matrix (Fin n) (Fin n) K)
    (h : ∀ (s : {s : powersetCard (Fin n) d // s ∈ F})
      (u : powersetCard (Fin n) d), u ∉ F →
        CompoundDeterminant.compound d A s.val u = 0) :
    (restrictedCompound F (A * B)).det =
      (restrictedCompound F A).det * (restrictedCompound F B).det := by
  rw [restrictedCompound_mul_of_support F A B h, Matrix.det_mul]

end LowerIdealDeterminant
