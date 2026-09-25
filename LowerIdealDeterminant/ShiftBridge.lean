import LowerIdealDeterminant.Theorem

/-!
# From elementary lowering moves to componentwise lower ideals

The thesis assumes closure under shifting an occupied coordinate down by one
into a vacant position. We prove this generates the componentwise order on
increasing enumerations of equal-sized subsets.
-/

namespace LowerIdealDeterminant

open Set Set.powersetCard

variable {n d : ℕ}

/-- An adjacent shift changes exactly the entry of the increasing enumeration
at the shifted coordinate. -/
theorem swapSubset_embedding_apply_of_adjacent
    (p q : Fin n) (hpq : q.val = p.val + 1)
    (s : powersetCard (Fin n) d)
    (hp : p ∉ (s : Finset (Fin n)))
    (k : Fin d) (hk : (ofFinEmbEquiv.symm s) k = q) (i : Fin d) :
    (ofFinEmbEquiv.symm (swapSubset p q s)) i =
      Function.update (ofFinEmbEquiv.symm s) k p i := by
  classical
  let f := ofFinEmbEquiv.symm s
  change f k = q at hk
  have hf_not_p (j : Fin d) : f j ≠ p := by
    intro hj
    exact hp ((mem_range_ofFinEmbEquiv_symm_iff_mem s p).1 ⟨j, hj⟩)
  let g0 : Fin d → Fin n := Function.update f k p
  have hg0 : StrictMono g0 := by
    intro j l hjl
    by_cases hj : j = k
    · subst j
      have hl : l ≠ k := ne_of_gt hjl
      have hfq : q < f l := by rw [← hk]; exact f.strictMono hjl
      change (Function.update f k p) k < (Function.update f k p) l
      simpa [Function.update_self, Function.update_of_ne hl] using
        (lt_trans (by omega : p < q) hfq)
    · by_cases hl : l = k
      · subst l
        have hfjq : f j < q := by rw [← hk]; exact f.strictMono hjl
        have hfjp : f j < p := by
          have hne := hf_not_p j
          omega
        change (Function.update f k p) j < (Function.update f k p) k
        simpa [Function.update_self, Function.update_of_ne hj] using hfjp
      · change (Function.update f k p) j < (Function.update f k p) l
        simpa [Function.update_of_ne hj, Function.update_of_ne hl] using f.strictMono hjl
  let g := OrderEmbedding.ofStrictMono g0 hg0
  have hgf (j : Fin d) : g j = Equiv.swap p q (f j) := by
    by_cases hj : j = k
    · subst j
      simp [g, g0, hk, Equiv.swap_apply_right]
    · have hfjq : f j ≠ q := by
        intro he
        exact hj (f.injective (he.trans hk.symm))
      simp [g, g0, Function.update_of_ne hj,
        Equiv.swap_apply_of_ne_of_ne (hf_not_p j) hfjq]
  have heq : swapSubset p q s = ofFinEmbEquiv g := by
    apply SetLike.ext
    intro x
    change (x ∈ (swapSubset p q s : Finset (Fin n))) ↔
      x ∈ (ofFinEmbEquiv g : Finset (Fin n))
    rw [mem_swapSubset_iff]
    rw [show x ∈ (ofFinEmbEquiv g : Finset (Fin n)) ↔ x ∈ Set.range g by
      exact mem_ofFinEmbEquiv_iff_mem_range g x]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s
        (Equiv.swap p q x)).2 hx
      refine ⟨j, ?_⟩
      rw [hgf j, hj, Equiv.swap_apply_self]
    · rintro ⟨j, rfl⟩
      rw [hgf j, Equiv.swap_apply_self]
      exact (mem_range_ofFinEmbEquiv_symm_iff_mem s (f j)).1 ⟨j, rfl⟩
  rw [heq]
  simp only [Equiv.symm_apply_apply]
  change g i = g0 i
  rfl

/-- If two sorted subsets are componentwise comparable but unequal, there
is a first coordinate where the smaller one is strictly smaller. -/
private theorem exists_first_gap {s t : powersetCard (Fin n) d}
    (hst : ComponentwiseLE s t) (hne : s ≠ t) :
    ∃ k : Fin d, (ofFinEmbEquiv.symm s) k < (ofFinEmbEquiv.symm t) k ∧
      ∀ j : Fin d, j < k → (ofFinEmbEquiv.symm s) j = (ofFinEmbEquiv.symm t) j := by
  classical
  let f := ofFinEmbEquiv.symm s
  let g := ofFinEmbEquiv.symm t
  let bad : Finset (Fin d) := Finset.univ.filter (fun i => f i < g i)
  have hbad : bad.Nonempty := by
    by_contra hempty
    have hgf : ComponentwiseLE t s := by
      intro i
      exact le_of_not_gt (by
        intro hi
        exact hempty ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
    exact hne (componentwiseLE_antisymm hst hgf)
  let k := bad.min' hbad
  refine ⟨k, (Finset.mem_filter.mp (Finset.min'_mem bad hbad)).2, ?_⟩
  intro j hj
  have hn : ¬ f j < g j := by
    intro hf
    exact (not_le_of_gt hj) (Finset.min'_le bad j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩))
  exact le_antisymm (hst j) (le_of_not_gt hn)

/-- Unless `s = t`, lower `t` at one vacant adjacent coordinate while
keeping `s` below it. The gap is chosen at the first differing position. -/
private theorem exists_adjacent_shift_toward {s t : powersetCard (Fin n) d}
    (hst : ComponentwiseLE s t) (hne : s ≠ t) :
    ∃ (p q : Fin n), q.val = p.val + 1 ∧
      q ∈ (t : Finset (Fin n)) ∧ p ∉ (t : Finset (Fin n)) ∧
        ComponentwiseLE s (swapSubset p q t) := by
  classical
  obtain ⟨k, hk, hfirst⟩ := exists_first_gap hst hne
  let f := ofFinEmbEquiv.symm s
  let g := ofFinEmbEquiv.symm t
  let q : Fin n := g k
  let p : Fin n := ⟨q.val - 1, by have := q.isLt; omega⟩
  have hpq : q.val = p.val + 1 := by
    have hfk : (f k).val < q.val := hk
    dsimp [p]
    omega
  have hp_le : f k ≤ p := by
    change (f k).val ≤ p.val
    have hfk : (f k).val < q.val := hk
    dsimp [p]
    omega
  have hq : q ∈ (t : Finset (Fin n)) :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem t q).1 ⟨k, rfl⟩
  have hp : p ∉ (t : Finset (Fin n)) := by
    intro hpt
    obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t p).2 hpt
    have hjk : j < k := (g.lt_iff_lt).mp (by
      rw [hj]
      change p.val < q.val
      omega)
    have hfj : f j = p := (hfirst j hjk).trans hj
    have hmono : f j < f k := f.strictMono hjk
    have hfk : (f k).val ≤ p.val := hp_le
    have hjval : (f j).val = p.val := congrArg Fin.val hfj
    have hmval : (f j).val < (f k).val := hmono
    omega
  refine ⟨p, q, hpq, hq, hp, ?_⟩
  intro i
  rw [swapSubset_embedding_apply_of_adjacent p q hpq t hp k rfl i]
  by_cases hi : i = k
  · subst i
    simpa only [Function.update_self] using hp_le
  · simpa only [Function.update_of_ne hi] using hst i

/-- The already established strict weight order turns an adjacent shift
into a well-founded induction step. -/
theorem subsetWeight_swapSubset_lt
    (p q : Fin n) (hpq : q.val = p.val + 1)
    (s : powersetCard (Fin n) d)
    (hq : q ∈ (s : Finset (Fin n)))
    (hp : p ∉ (s : Finset (Fin n))) :
    subsetWeight (swapSubset p q s) < subsetWeight s := by
  have hne : swapSubset p q s ≠ s := by
    intro heq
    have hnot : q ∉ (swapSubset p q s : Finset (Fin n)) := by
      rw [mem_swapSubset_iff, Equiv.swap_apply_right]
      exact hp
    rw [heq] at hnot
    exact hnot hq
  exact subsetWeight_strict (componentwiseLE_swapSubset_of_adjacent p q hpq s hq hp) hne

/-- The thesis's elementary adjacent lowering condition is equivalent to
being a componentwise lower ideal. -/
theorem isLowerIdeal_of_adjacentShifts
    (F : Finset (powersetCard (Fin n) d))
    (hF : ∀ (p q : Fin n), q.val = p.val + 1 → IsShiftClosed F p q) :
    IsLowerIdeal F := by
  have aux : ∀ t : powersetCard (Fin n) d,
      ∀ s : powersetCard (Fin n) d,
        ComponentwiseLE s t → t ∈ F → s ∈ F := by
    intro t
    induction t using (measure subsetWeight).wf.induction with
    | h t ih =>
      intro s hst ht
      by_cases heq : s = t
      · simpa [heq] using ht
      · obtain ⟨p, q, hpq, hq, hp, hs⟩ := exists_adjacent_shift_toward hst heq
        exact ih (swapSubset p q t) (subsetWeight_swapSubset_lt p q hpq t hq hp)
          s hs (hF p q hpq t ht hq hp)
  intro s t hst ht
  exact aux t s hst ht

/-- Equivalence between the thesis's adjacent-lowering formulation and the
componentwise-lower-ideal formulation used in the determinant proof. -/
theorem isLowerIdeal_iff_adjacentShifts
    (F : Finset (powersetCard (Fin n) d)) :
    IsLowerIdeal F ↔
      ∀ (p q : Fin n), q.val = p.val + 1 → IsShiftClosed F p q := by
  constructor
  · exact fun h p q hpq => isShiftClosed_of_isLowerIdeal F h p q hpq
  · exact isLowerIdeal_of_adjacentShifts F

/-- The previous coordinate `q - 1`, viewed in `Fin n`. This is defined
also at zero (where it remains zero); the lowering condition explicitly
requires `0 < q.val`. -/
def adjacentPredecessor (q : Fin n) : Fin n :=
  ⟨q.val - 1, by have := q.isLt; omega⟩

/-- With an occupied `q` and an unoccupied `p`, the permutation-based
`swapSubset` is literally the thesis's erase-and-insert operation. -/
theorem swapSubset_eq_erase_insert
    (p q : Fin n) (s : powersetCard (Fin n) d)
    (hq : q ∈ (s : Finset (Fin n)))
    (hp : p ∉ (s : Finset (Fin n))) :
    (swapSubset p q s : Finset (Fin n)) =
      insert p ((s : Finset (Fin n)).erase q) := by
  ext x
  by_cases hxp : x = p
  · subst x
    simp [mem_swapSubset_iff, hq]
  · by_cases hxq : x = q
    · subst x
      simp [mem_swapSubset_iff, hp, hxp]
    · simp [mem_swapSubset_iff, hxp, hxq,
        Equiv.swap_apply_of_ne_of_ne hxp hxq]

/-- The thesis's lowering condition: replace an occupied `q > 0` by its
unoccupied predecessor `q - 1` and remain in the family. -/
def IsElementaryLoweringClosed (F : Finset (powersetCard (Fin n) d)) : Prop :=
  ∀ s ∈ F, ∀ q : Fin n, q ∈ (s : Finset (Fin n)) → 0 < q.val →
    adjacentPredecessor q ∉ (s : Finset (Fin n)) →
      swapSubset (adjacentPredecessor q) q s ∈ F

/-- The predecessor formulation and adjacent-swap closure are equivalent. -/
theorem isElementaryLoweringClosed_iff_adjacentShifts
    (F : Finset (powersetCard (Fin n) d)) :
    IsElementaryLoweringClosed F ↔
      ∀ (p q : Fin n), q.val = p.val + 1 → IsShiftClosed F p q := by
  constructor
  · intro hF p q hpq s hs hq hp
    have hpos : 0 < q.val := by omega
    have heq : adjacentPredecessor q = p := Fin.ext (by
      dsimp [adjacentPredecessor]
      omega)
    simpa only [heq] using hF s hs q hq hpos (by simpa only [heq] using hp)
  · intro hF s hs q hq hpos hp
    exact hF (adjacentPredecessor q) q (by
      dsimp [adjacentPredecessor]
      omega) s hs hq hp

/-- The exact thesis lowering condition coincides with the lower-ideal
condition, in both directions. -/
theorem isElementaryLoweringClosed_iff_isLowerIdeal
    (F : Finset (powersetCard (Fin n) d)) :
    IsElementaryLoweringClosed F ↔ IsLowerIdeal F :=
  (isElementaryLoweringClosed_iff_adjacentShifts F).trans
    (isLowerIdeal_iff_adjacentShifts F).symm

/-- Thesis Theorem 3, in its elementary-lowering formulation, for arbitrary
matrices over arbitrary commutative rings. -/
theorem ringDesiredIdentity_of_elementaryLowering
    {R : Type*} [CommRing R]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsElementaryLoweringClosed F)
    (A : Matrix (Fin n) (Fin n) R) : RingDesiredIdentity F A :=
  ringDesiredIdentity_all F ((isElementaryLoweringClosed_iff_isLowerIdeal F).mp hF) A

/-- The same unrestricted theorem for the field-valued compound matrix. -/
theorem desiredIdentity_of_elementaryLowering
    {K : Type*} [Field K]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsElementaryLoweringClosed F)
    (A : Matrix (Fin n) (Fin n) K) : DesiredIdentity F A :=
  desiredIdentity_all F ((isElementaryLoweringClosed_iff_isLowerIdeal F).mp hF) A

end LowerIdealDeterminant
