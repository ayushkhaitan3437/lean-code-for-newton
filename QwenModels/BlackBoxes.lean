import QwenModels.Pure

namespace QwenModels

open Polynomial

/-!
Black boxes for results quoted from outside the paper.

This file is the only Lean file in `QwenModels/` allowed to contain axioms for
this formalization.  The axioms below should be read with `ord` instantiated as
the intended p-adic additive valuation; that ambient condition is not yet bundled
into the lightweight Newton-polygon API.
-/

/-- Neukirch's Newton polygon factorization theorem, in the segment-data form
used by the paper. -/
axiom blackbox_np_factor_by_segments {K : Type*} [Field K]
    {ord : K → WithTop ℤ} {f : K[X]} {data : NewtonPolygonData} :
    HasNewtonPolygonData ord f data →
      ∃ factors : List K[X], factors.prod = f ∧
        List.Forall₂
          (fun factor seg => factor.natDegree = seg.length ∧ PureAt ord factor seg.slope)
          factors data

end QwenModels
