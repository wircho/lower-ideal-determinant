import LowerIdealDeterminant.Product
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Vanishing of minors of lower triangular matrices

The lower-triangular support of compounds will let us restrict their products to
lower ideals without losing any intermediate summands.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

/-- A permutation cannot send all `k+1` elements of the initial segment
`{0,...,k}` into the strictly smaller segment `{0,...,k-1}`. -/
private theorem exists_le_perm_ge (σ : Equiv.Perm (Fin d)) (k : Fin d) :
    ∃ i : Fin d, i ≤ k ∧ k ≤ σ i := by
  classical
  by_contra h
  have hsub : (Finset.Iic k).image σ ⊆ Finset.Iio k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hnot : ¬ k ≤ σ i := by
      intro hki
      exact h ⟨i, Finset.mem_Iic.mp hi, hki⟩
    exact Finset.mem_Iio.mpr (lt_of_not_ge hnot)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ σ.injective,
    Fin.card_Iic, Fin.card_Iio] at hcard
  omega

/-- For a lower triangular matrix, its minor with row set `I` and column set
`J` vanishes if `J` is not componentwise at most `I`. -/
theorem compound_eq_zero_of_lowerTriangular
    (L : Matrix (Fin n) (Fin n) K)
    (hL : ∀ i j : Fin n, i < j → L i j = 0)
    (I J : powersetCard (Fin n) d) (hJI : ¬ ComponentwiseLE J I) :
    CompoundDeterminant.compound d L I J = 0 := by
  classical
  let f := ofFinEmbEquiv.symm I
  let g := ofFinEmbEquiv.symm J
  obtain ⟨k, hk⟩ : ∃ k : Fin d, ¬g k ≤ f k := by
    simpa [ComponentwiseLE, f, g] using hJI
  have hfg : f k < g k := lt_of_not_ge hk
  rw [CompoundDeterminant.compound_apply, ← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_eq_zero
  intro σ _
  obtain ⟨i, hik, hksi⟩ := exists_le_perm_ge σ k
  have hzero : L (f i) (g (σ i)) = 0 :=
    hL _ _ (lt_of_le_of_lt (f.monotone hik)
      (lt_of_lt_of_le hfg (g.monotone hksi)))
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero]

/-- The support condition needed in `Product.lean` follows from lower-ideal
closure when the left factor is lower triangular. -/
theorem lowerTriangular_support_of_isLowerIdeal
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual) :
    ∀ (s : {s : powersetCard (Fin n) d // s ∈ F})
      (u : powersetCard (Fin n) d), u ∉ F →
        CompoundDeterminant.compound d L s.val u = 0 := by
  intro s u hu
  apply compound_eq_zero_of_lowerTriangular L (fun i j hij => hL hij) s.val u
  intro hus
  exact hu (hF hus s.property)

/-- Restricted compounds multiply when their left factor is lower triangular
and the indexing family is a lower ideal. -/
theorem restrictedCompound_mul_lowerTriangular
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (L B : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual) :
    restrictedCompound F (L * B) =
      restrictedCompound F L * restrictedCompound F B := by
  exact restrictedCompound_mul_of_support F L B
    (lowerTriangular_support_of_isLowerIdeal F hF L hL)

/-- Determinant version of restricted multiplicativity for lower ideals. -/
theorem det_restrictedCompound_mul_lowerTriangular
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (L B : Matrix (Fin n) (Fin n) K)
    (hL : L.BlockTriangular OrderDual.toDual) :
    (restrictedCompound F (L * B)).det =
      (restrictedCompound F L).det * (restrictedCompound F B).det := by
  rw [restrictedCompound_mul_lowerTriangular F hF L B hL, Matrix.det_mul]

end LowerIdealDeterminant
