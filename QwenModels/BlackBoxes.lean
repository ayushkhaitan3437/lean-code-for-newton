import QwenModels.Pure
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace QwenModels

open Polynomial

/-!
Black box for the single result quoted from outside the paper.

This file is the only Lean file in `QwenModels/` allowed to contain an axiom
for this formalization.

The factorization theorem below is stated for `ℚ_[p]` with its standard
additive valuation `Padic.addValuation`.  Two hypotheses are essential for the
statement to be true, not merely convenient:

* Completeness of the base field cannot be dropped.  Over `ℚ` with the
  `2`-adic valuation, `X ^ 2 + X + 2` has the two-segment Newton polygon
  `[(1, -1), (1, 0)]` but is irreducible over `ℚ`, so it admits no
  factorization into two linear pure factors.  A version of this axiom over an
  arbitrary valued field (or, worse, an arbitrary function
  `ord : K → WithTop ℤ`) is therefore false and would make the environment
  inconsistent.
* `data ≠ []` cannot be dropped.  A nonzero constant polynomial `C c` has
  `HasNewtonPolygonData` with the empty segment list, and `List.Forall₂`
  against `[]` would force `factors = []`, whose product is `1 ≠ C c`.
-/

/-- Neukirch's Newton polygon factorization theorem (Algebraic Number Theory,
Proposition II.6.3) over `ℚ_[p]`, in the segment-data form used by the paper:
a polynomial factors according to the maximal segments of its Newton polygon,
with one pure factor of matching degree and slope per segment. -/
axiom blackbox_np_factor_by_segments {p : ℕ} [Fact p.Prime]
    {f : ℚ_[p][X]} {data : NewtonPolygonData} :
    data ≠ [] →
    HasNewtonPolygonData
      ((Padic.addValuation : AddValuation ℚ_[p] (WithTop ℤ)) : ℚ_[p] → WithTop ℤ)
      f data →
    ∃ factors : List ℚ_[p][X], factors.prod = f ∧
      List.Forall₂
        (fun factor seg => factor.natDegree = seg.length ∧
          PureAt
            ((Padic.addValuation : AddValuation ℚ_[p] (WithTop ℤ)) : ℚ_[p] → WithTop ℤ)
            factor seg.slope)
        factors data

end QwenModels
