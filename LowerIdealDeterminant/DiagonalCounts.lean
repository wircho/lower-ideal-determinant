import LowerIdealDeterminant.Statement
import LowerIdealDeterminant.Triangular

/-!
# The diagonal determinant, counted by coordinates

Rearrange the product of diagonal entries over selected subsets into a product
indexed by coordinates, each raised to its incidence count.
-/

namespace LowerIdealDeterminant

open Matrix Set Set.powersetCard

variable {K : Type*} [Field K] {n d : ℕ}

private theorem prod_sorted_subset (s : powersetCard (Fin n) d) (a : Fin n → K) :
    (∏ i : Fin d, a ((ofFinEmbEquiv.symm s) i)) =
      ∏ i ∈ (s : Finset (Fin n)), a i := by
  classical
  let e := s.val.orderEmbOfFin s.prop
  have h := Finset.prod_image (f := a) (s := (Finset.univ : Finset (Fin d)))
    (g := e) (fun _ _ _ _ hij => e.injective hij)
  simpa [e, ofFinEmbEquiv_symm_apply, Finset.image_orderEmbOfFin_univ] using h.symm

/-- The diagonal determinant in the form `∏ a_i ^ e_i`. This works for
*any* family of equal-sized subsets, with no lower-ideal hypothesis. -/
theorem det_restrictedCompound_diagonal_incidence
    (F : Finset (powersetCard (Fin n) d)) (a : Fin n → K) :
    (restrictedCompound F (Matrix.diagonal a)).det =
      ∏ i : Fin n, a i ^ incidenceCount F i := by
  classical
  rw [det_restrictedCompound_diagonal]
  calc
    (∏ s : {s : powersetCard (Fin n) d // s ∈ F},
        ∏ i : Fin d, a ((ofFinEmbEquiv.symm s.val) i)) =
        ∏ s ∈ F, ∏ i ∈ (s : Finset (Fin n)), a i := by
          calc
            (∏ s : {s : powersetCard (Fin n) d // s ∈ F},
              ∏ i : Fin d, a ((ofFinEmbEquiv.symm s.val) i)) =
              ∏ s : {s : powersetCard (Fin n) d // s ∈ F},
                ∏ i ∈ (s.val : Finset (Fin n)), a i := by
                  apply Finset.prod_congr rfl
                  intro s _
                  exact prod_sorted_subset s.val a
            _ = ∏ s ∈ F, ∏ i ∈ (s : Finset (Fin n)), a i := by
              simpa using (Finset.prod_coe_sort F
                (fun s : powersetCard (Fin n) d => ∏ i ∈ (s : Finset (Fin n)), a i))
    _ = ∏ s ∈ F, ∏ i : Fin n,
        if i ∈ (s : Finset (Fin n)) then a i else 1 := by
          apply Finset.prod_congr rfl
          intro s _
          exact (Finset.prod_ite_mem_eq (s : Finset (Fin n)) a).symm
    _ = ∏ i : Fin n, ∏ s ∈ F,
        if i ∈ (s : Finset (Fin n)) then a i else 1 := by
          exact Finset.prod_comm
    _ = ∏ i : Fin n, a i ^ incidenceCount F i := by
          apply Finset.prod_congr rfl
          intro i _
          rw [← Finset.prod_filter, Finset.prod_const]
          simp only [incidenceCount]

end LowerIdealDeterminant
