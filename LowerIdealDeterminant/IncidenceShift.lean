import LowerIdealDeterminant.Telescoping

/-!
# Incidence counts and adjacent shifts

We isolate the finite-injection argument for incidence-count monotonicity.
The adjacent-swap closure for lower ideals is proved below; its converse is
proved in `ShiftBridge.lean`.
-/

namespace LowerIdealDeterminant

open Set Set.powersetCard

variable {n d : ℕ}

/-- Act on a `d`-subset by swapping two coordinates. -/
def swapSubset (p q : Fin n) (s : powersetCard (Fin n) d) :
    powersetCard (Fin n) d :=
  Set.powersetCard.map d (Equiv.swap p q).toEmbedding s

@[simp] theorem mem_swapSubset_iff (p q x : Fin n) (s : powersetCard (Fin n) d) :
    x ∈ (swapSubset p q s : Finset (Fin n)) ↔
      Equiv.swap p q x ∈ (s : Finset (Fin n)) := by
  simp [swapSubset]

theorem swapSubset_swapSubset (p q : Fin n) (s : powersetCard (Fin n) d) :
    swapSubset p q (swapSubset p q s) = s := by
  apply Subtype.ext
  ext x
  simp [mem_swapSubset_iff]

/-- An adjacent swap that moves an occupied coordinate down into an empty
position moves the sorted subset down componentwise. -/
theorem componentwiseLE_swapSubset_of_adjacent
    (p q : Fin n) (hpq : q.val = p.val + 1)
    (s : powersetCard (Fin n) d)
    (hq : q ∈ (s : Finset (Fin n)))
    (hp : p ∉ (s : Finset (Fin n))) :
    ComponentwiseLE (swapSubset p q s) s := by
  classical
  let f := ofFinEmbEquiv.symm s
  obtain ⟨k, hk⟩ : ∃ k : Fin d, f k = q :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem s q).2 hq
  have hf_not_p (i : Fin d) : f i ≠ p := by
    intro hi
    exact hp ((mem_range_ofFinEmbEquiv_symm_iff_mem s p).1 ⟨i, hi⟩)
  let g0 : Fin d → Fin n := Function.update f k p
  have hg0 : StrictMono g0 := by
    intro i j hij
    by_cases hi : i = k
    · subst i
      have hj : j ≠ k := ne_of_gt hij
      have hfq : q < f j := by rw [← hk]; exact f.strictMono hij
      change (Function.update f k p) k < (Function.update f k p) j
      simpa [Function.update_self, Function.update_of_ne hj] using
        (lt_trans (by omega : p < q) hfq)
    · by_cases hj : j = k
      · subst j
        have hfiq : f i < q := by rw [← hk]; exact f.strictMono hij
        have hfip : f i < p := by
          have hne := hf_not_p i
          omega
        change (Function.update f k p) i < (Function.update f k p) k
        simpa [Function.update_self, Function.update_of_ne hi] using hfip
      · change (Function.update f k p) i < (Function.update f k p) j
        simpa [Function.update_of_ne hi, Function.update_of_ne hj] using f.strictMono hij
  let g := OrderEmbedding.ofStrictMono g0 hg0
  have hgf (i : Fin d) : g i = Equiv.swap p q (f i) := by
    by_cases hi : i = k
    · subst i
      simp [g, g0, hk, Equiv.swap_apply_right]
    · have hfiq : f i ≠ q := by
        intro he
        exact hi (f.injective (he.trans hk.symm))
      simp [g, g0, Function.update_of_ne hi,
        Equiv.swap_apply_of_ne_of_ne (hf_not_p i) hfiq]
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
      obtain ⟨i, hi⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s
        (Equiv.swap p q x)).2 hx
      refine ⟨i, ?_⟩
      rw [hgf i, hi, Equiv.swap_apply_self]
    · rintro ⟨i, rfl⟩
      rw [hgf i, Equiv.swap_apply_self]
      exact (mem_range_ofFinEmbEquiv_symm_iff_mem s (f i)).1 ⟨i, rfl⟩
  rw [heq]
  intro i
  simp only [Equiv.symm_apply_apply]
  change g i ≤ f i
  by_cases hi : i = k
  · subst i
    simp [g, g0, hk]
    omega
  · simp [g, g0, Function.update_of_ne hi]

/-- Membership closure under shifting `q` to `p`, provided `p` is absent.
We will deduce this from `IsLowerIdeal` for adjacent `p,q`. -/
def IsShiftClosed (F : Finset (powersetCard (Fin n) d)) (p q : Fin n) : Prop :=
  ∀ s ∈ F, q ∈ (s : Finset (Fin n)) → p ∉ (s : Finset (Fin n)) →
    swapSubset p q s ∈ F

/-- Count monotonicity follows from adjacent shift closure, without any
assumption about matrices or coefficients. -/
theorem incidenceCount_le_of_isShiftClosed
    (F : Finset (powersetCard (Fin n) d)) (p q : Fin n)
    (hF : IsShiftClosed F p q) :
    incidenceCount F q ≤ incidenceCount F p := by
  classical
  let shift : powersetCard (Fin n) d → powersetCard (Fin n) d :=
    fun s => if p ∈ (s : Finset (Fin n)) then s else swapSubset p q s
  have hmem (s : powersetCard (Fin n) d) (hs : s ∈ F)
      (hq : q ∈ (s : Finset (Fin n))) :
      shift s ∈ F ∧ p ∈ (shift s : Finset (Fin n)) := by
    by_cases hps : p ∈ (s : Finset (Fin n))
    · simp [shift, hps, hs]
    · have hm := hF s hs hq hps
      have hp : p ∈ (swapSubset p q s : Finset (Fin n)) := by
        rw [mem_swapSubset_iff, Equiv.swap_apply_left]
        exact hq
      simp [shift, hps, hm, hp]
  have hinj : (↑(F.filter (fun s : powersetCard (Fin n) d =>
      q ∈ (s : Finset (Fin n)))) : Set (powersetCard (Fin n) d)).InjOn shift := by
    intro s hs t ht he
    have hqs : q ∈ (s : Finset (Fin n)) := (Finset.mem_filter.mp hs).2
    have hqt : q ∈ (t : Finset (Fin n)) := (Finset.mem_filter.mp ht).2
    by_cases hps : p ∈ (s : Finset (Fin n))
    · by_cases hpt : p ∈ (t : Finset (Fin n))
      · simpa [shift, hps, hpt] using he
      · have hnoq : q ∉ (swapSubset p q t : Finset (Fin n)) := by
          rw [mem_swapSubset_iff, Equiv.swap_apply_right]
          exact hpt
        have hst : s = swapSubset p q t := by simpa [shift, hps, hpt] using he
        exact (hnoq (hst ▸ hqs)).elim
    · by_cases hpt : p ∈ (t : Finset (Fin n))
      · have hnoq : q ∉ (swapSubset p q s : Finset (Fin n)) := by
          rw [mem_swapSubset_iff, Equiv.swap_apply_right]
          exact hps
        have hst : swapSubset p q s = t := by simpa [shift, hps, hpt] using he
        exact (hnoq (hst.symm ▸ hqt)).elim
      · have he' : swapSubset p q s = swapSubset p q t := by
          simpa [shift, hps, hpt] using he
        have := congrArg (swapSubset p q) he'
        simpa [swapSubset_swapSubset] using this
  have hmaps : Set.MapsTo shift
      (↑(F.filter (fun s : powersetCard (Fin n) d =>
        q ∈ (s : Finset (Fin n)))) : Set (powersetCard (Fin n) d))
      (↑(F.filter (fun s : powersetCard (Fin n) d =>
        p ∈ (s : Finset (Fin n)))) : Set (powersetCard (Fin n) d)) := by
    intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hsF, hsq⟩
    exact Finset.mem_filter.mpr (hmem s hsF hsq)
  exact Finset.card_le_card_of_injOn shift hmaps hinj

/-- Componentwise lower ideals are closed under elementary adjacent lowering. -/
theorem isShiftClosed_of_isLowerIdeal
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (p q : Fin n) (hpq : q.val = p.val + 1) : IsShiftClosed F p q := by
  intro s hs hq hp
  exact hF (componentwiseLE_swapSubset_of_adjacent p q hpq s hq hp) hs

/-- Incidence counts of a lower ideal are nonincreasing. -/
theorem nextIncidenceCount_le
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F) (r : Fin n) :
    nextIncidenceCount F r ≤ incidenceCount F r := by
  unfold nextIncidenceCount
  split_ifs with h
  · exact incidenceCount_le_of_isShiftClosed F r ⟨r.val + 1, h⟩
      (isShiftClosed_of_isLowerIdeal F hF r ⟨r.val + 1, h⟩ rfl)
  · exact Nat.zero_le _

/-- The exact target identity for diagonal matrices and any lower ideal,
without any hypothesis that the diagonal entries are nonzero. -/
theorem desiredIdentity_diagonal {K : Type*} [Field K]
    (F : Finset (powersetCard (Fin n) d)) (hF : IsLowerIdeal F)
    (a : Fin n → K) : DesiredIdentity F (Matrix.diagonal a) := by
  exact desiredIdentity_diagonal_of_count_mono F a (nextIncidenceCount_le F hF)

end LowerIdealDeterminant
