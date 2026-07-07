import Mathlib.RingTheory.Valuation.Basic

open BigOperators

namespace QwenModels

/-!
Bundled valuation facts from mathlib.

This file is intentionally not imported by `QwenModels/test1.lean`: it pulls in
the full bundled valuation API, which is useful but heavier than the current
unbundled Newton-polygon development.
-/

theorem addValuation_map_sum_eq_of_lt {R Γ₀ ι : Type*}
    [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] [DecidableEq ι]
    (v : AddValuation R Γ₀) {s : Finset ι} {f : ι → R} {j : ι}
    (hj : j ∈ s)
    (hf : ∀ i ∈ s \ {j}, v (f j) < v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  have h := Valuation.map_sum_eq_of_lt (AddValuation.toValuation v) hj (by
    intro i hi
    simpa [AddValuation.toValuation_apply] using hf i hi)
  simpa [AddValuation.toValuation_apply] using h

end QwenModels
