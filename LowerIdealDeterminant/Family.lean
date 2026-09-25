import CompoundDeterminant.Entries

/-!
# Families of equal-cardinality subsets

We keep the order on subsets separate from the usual `≤` on `Set.powersetCard`:
the latter is *inclusion*, whereas the theorem needs componentwise comparison of
increasing enumerations.
-/

namespace LowerIdealDeterminant

open Set
open Set.powersetCard

variable {n d : ℕ}

/-- Componentwise order on `d`-subsets of `Fin n`, comparing their increasing
enumerations. In a later file we will relate this to the thesis's elementary
lowering-move condition. -/
def ComponentwiseLE (s t : powersetCard (Fin n) d) : Prop :=
  ∀ i : Fin d, (ofFinEmbEquiv.symm s) i ≤ (ofFinEmbEquiv.symm t) i

theorem componentwiseLE_refl (s : powersetCard (Fin n) d) : ComponentwiseLE s s :=
  fun _ ↦ le_refl _

theorem componentwiseLE_trans {s t u : powersetCard (Fin n) d}
    (hst : ComponentwiseLE s t) (htu : ComponentwiseLE t u) : ComponentwiseLE s u :=
  fun i ↦ (hst i).trans (htu i)

theorem componentwiseLE_antisymm {s t : powersetCard (Fin n) d}
    (hst : ComponentwiseLE s t) (hts : ComponentwiseLE t s) : s = t := by
  apply (ofFinEmbEquiv.symm).injective
  ext i
  exact le_antisymm (hst i) (hts i)

/-- A finite order ideal in the componentwise order on `d`-subsets. -/
def IsLowerIdeal (F : Finset (powersetCard (Fin n) d)) : Prop :=
  ∀ ⦃s t⦄, ComponentwiseLE s t → t ∈ F → s ∈ F

/-- Number of members of the family containing a fixed coordinate. -/
noncomputable def incidenceCount (F : Finset (powersetCard (Fin n) d)) (i : Fin n) : ℕ := by
  classical
  exact (F.filter fun (s : powersetCard (Fin n) d) ↦ i ∈ (s : Finset (Fin n))).card

end LowerIdealDeterminant
