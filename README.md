# Lower-ideal determinant identity

This repository contains a Lean 4 / Mathlib proof of the following result:

> Let $F$ be a finite family of $d$-element subsets of $\lbrace 1,\ldots,n\rbrace$, closed under replacing $q>1$ by $q-1$ whenever $q$ belongs to a subset and $q-1$ does not. Let $e_r$ count the members of $F$ containing $r$, with $e_{n+1}=0$, and let $\Delta_r$ be the leading principal minor of order $r$ of an $n\times n$ matrix $A$ over a commutative ring. Then
>
> $$
> \det\bigl[\det A_{I,J}\bigr]_{I,J\in F}
> = \prod_{r=1}^{n}\Delta_r^{e_r-e_{r+1}}.
> $$

This result first appeared in my PhD thesis, [*SLk-tilings and Laurent polynomials*](https://archipel.uqam.ca/6123/), where I gave a combinatorial proof based on nonintersecting lattice paths. The Lean proof takes a different route: it uses a unit-LDU factorization of the generic matrix, analyzes the selected minors of triangular matrices, and then specializes the resulting polynomial identity to any commutative ring.

### Statement and proof

The main theorem is [`ringDesiredIdentity_of_elementaryLowering`](LowerIdealDeterminant/ShiftBridge.lean). Its hypothesis, [`IsElementaryLoweringClosed`](LowerIdealDeterminant/ShiftBridge.lean), encodes the lowering move. Its conclusion, [`RingDesiredIdentity`](LowerIdealDeterminant/RingMinors.lean), uses the matrix of minors [`selectedMinors`](LowerIdealDeterminant/RingMinors.lean). The supporting proofs are in [`LowerIdealDeterminant/`](LowerIdealDeterminant/) and the minimal compound-matrix files in [`CompoundDeterminant/`](CompoundDeterminant/).

### Check

Install [elan](https://github.com/leanprover/elan), then run in this directory:

```bash
lake exe cache get  # optional: download Mathlib build artifacts
lake build
```

The Lean and Mathlib versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
