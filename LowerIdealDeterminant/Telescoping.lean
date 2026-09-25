import LowerIdealDeterminant.UnitTriangular

/-!
# Telescoping prefix products

An algebraic lemma valid without assuming that any pivot or prefix product is
nonzero. This will convert the diagonal contribution of an LDU factorization
to a product of leading principal minors once incidence-count monotonicity and
the leading-minor formula have been established.
-/

namespace LowerIdealDeterminant

variable {K : Type*} [Field K]

/-- The prefix product of a sequence. -/
def prefixProduct (a : ℕ → K) (m : ℕ) : K :=
  ∏ i ∈ Finset.range m, a i

@[simp] theorem prefixProduct_zero (a : ℕ → K) : prefixProduct a 0 = 1 := by
  simp [prefixProduct]

@[simp] theorem prefixProduct_succ (a : ℕ → K) (m : ℕ) :
    prefixProduct a (m + 1) = prefixProduct a m * a m := by
  simp [prefixProduct, Finset.prod_range_succ]

/-- Telescoping with an extra final factor. This form avoids dividing by a
prefix product, so it remains valid if some entries are zero. -/
theorem prod_prefix_pow_sub_mul_tail
    (a : ℕ → K) (e : ℕ → ℕ)
    (hmono : ∀ m, e (m + 1) ≤ e m) (m : ℕ) :
    (∏ r ∈ Finset.range m,
      (prefixProduct a (r + 1)) ^ (e r - e (r + 1))) *
      (prefixProduct a m) ^ (e m) =
        ∏ i ∈ Finset.range m, a i ^ e i := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        (∏ r ∈ Finset.range (m + 1),
            (prefixProduct a (r + 1)) ^ (e r - e (r + 1))) *
            (prefixProduct a (m + 1)) ^ (e (m + 1)) =
          ((∏ r ∈ Finset.range m,
              (prefixProduct a (r + 1)) ^ (e r - e (r + 1))) *
              (prefixProduct a (m + 1)) ^ (e m - e (m + 1))) *
              (prefixProduct a (m + 1)) ^ (e (m + 1)) := by
                rw [Finset.prod_range_succ]
        _ = (∏ r ∈ Finset.range m,
              (prefixProduct a (r + 1)) ^ (e r - e (r + 1))) *
              (prefixProduct a (m + 1)) ^ e m := by
                rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (hmono m)]
        _ = ((∏ r ∈ Finset.range m,
              (prefixProduct a (r + 1)) ^ (e r - e (r + 1))) *
              (prefixProduct a m) ^ e m) * a m ^ e m := by
                rw [prefixProduct_succ, mul_pow]
                ring
        _ = ∏ i ∈ Finset.range (m + 1), a i ^ e i := by
                rw [ih, Finset.prod_range_succ]

/-- If the occurrence count vanishes at the endpoint, no tail factor remains. -/
theorem prod_prefix_pow_sub (a : ℕ → K) (e : ℕ → ℕ)
    (hmono : ∀ m, e (m + 1) ≤ e m) (m : ℕ) (hend : e m = 0) :
    ∏ r ∈ Finset.range m,
        (prefixProduct a (r + 1)) ^ (e r - e (r + 1)) =
      ∏ i ∈ Finset.range m, a i ^ e i := by
  have h := prod_prefix_pow_sub_mul_tail a e hmono m
  simpa [hend] using h

/-- The prefix minor of a diagonal matrix is its product of diagonal entries. -/
theorem leadingPrincipalMinor_diagonal {n : ℕ} (a : Fin n → K) (r : Fin n) :
    leadingPrincipalMinor (Matrix.diagonal a) r =
      ∏ i : Fin (r.val + 1), a (Fin.castLE (Nat.succ_le_of_lt r.isLt) i) := by
  classical
  unfold leadingPrincipalMinor
  rw [Matrix.submatrix_diagonal a (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt))
    (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt)).injective, Matrix.det_diagonal]
  rfl

/-- Telescoping indexed by `Fin n`, with zero as the occurrence count just
past the final coordinate. No nonzero assumptions on the entries. -/
theorem prod_fin_prefix_pow_sub {n : ℕ} (a : Fin n → K) (e : Fin n → ℕ)
    (hstep : ∀ r : Fin n,
      (if h : r.val + 1 < n then e ⟨r.val + 1, h⟩ else 0) ≤ e r) :
    (∏ r : Fin n,
        (∏ i : Fin (r.val + 1),
          a (Fin.castLE (Nat.succ_le_of_lt r.isLt) i)) ^
          (e r - (if h : r.val + 1 < n then e ⟨r.val + 1, h⟩ else 0))) =
      ∏ i : Fin n, a i ^ e i := by
  classical
  let aNat : ℕ → K := fun i => if h : i < n then a ⟨i, h⟩ else 1
  let eNat : ℕ → ℕ := fun i => if h : i < n then e ⟨i, h⟩ else 0
  have hm : ∀ m, eNat (m + 1) ≤ eNat m := by
    intro m
    by_cases h : m < n
    · by_cases hs : m + 1 < n
      · simpa [eNat, h, hs] using hstep ⟨m, h⟩
      · simp [eNat, h, hs]
    · have hs : ¬ m + 1 < n := by omega
      simp [eNat, h, hs]
  have hp (r : Fin n) : prefixProduct aNat (r.val + 1) =
      ∏ i : Fin (r.val + 1), a (Fin.castLE (Nat.succ_le_of_lt r.isLt) i) := by
    unfold prefixProduct
    rw [← Fin.prod_univ_eq_prod_range (fun i => aNat i) (r.val + 1)]
    apply Finset.prod_congr rfl
    intro i _
    have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt r.isLt)
    simp [aNat, hi, Fin.castLE]
  have hn := prod_prefix_pow_sub aNat eNat hm n (by simp [eNat])
  calc
    (∏ r : Fin n,
        (∏ i : Fin (r.val + 1),
          a (Fin.castLE (Nat.succ_le_of_lt r.isLt) i)) ^
          (e r - (if h : r.val + 1 < n then e ⟨r.val + 1, h⟩ else 0))) =
        ∏ r : Fin n, (prefixProduct aNat (r.val + 1)) ^
          (eNat r.val - eNat (r.val + 1)) := by
            apply Finset.prod_congr rfl
            intro r _
            rw [hp]
            simp [eNat, r.isLt]
    _ = ∏ i : Fin n, a i ^ e i := by
          rw [Fin.prod_univ_eq_prod_range
            (fun i => prefixProduct aNat (i + 1) ^ (eNat i - eNat (i + 1))) n]
          rw [hn, ← Fin.prod_univ_eq_prod_range (fun i => aNat i ^ eNat i) n]
          apply Finset.prod_congr rfl
          intro i _
          simp [aNat, eNat, i.isLt]

/-- The full target formula for diagonal matrices, conditional only on the
incidence-count inequalities. These inequalities are proved for lower ideals
in `IncidenceShift.lean`. -/
theorem desiredIdentity_diagonal_of_count_mono {n d : ℕ}
    (F : Finset (Set.powersetCard (Fin n) d)) (a : Fin n → K)
    (hmono : ∀ r : Fin n, nextIncidenceCount F r ≤ incidenceCount F r) :
    DesiredIdentity F (Matrix.diagonal a) := by
  unfold DesiredIdentity
  rw [det_restrictedCompound_diagonal_incidence]
  rw [← prod_fin_prefix_pow_sub a (incidenceCount F) hmono]
  apply Finset.prod_congr rfl
  intro r _
  rw [leadingPrincipalMinor_diagonal, nextIncidenceCount]

end LowerIdealDeterminant
