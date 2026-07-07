import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic

namespace QwenModels

/-!
Valuation-style lemmas used by the Newton polygon proof.

This file stays abstract: instead of importing a concrete p-adic valuation, it
uses only the strict two-term rule `v a < v b -> v (a + b) = v a`.
-/

theorem strictMin_list_sum {K Γ : Type*} [AddCommMonoid K] [Preorder Γ]
    {v : K → Γ} (hstrict : ∀ a b : K, v a < v b → v (a + b) = v a)
    {t0 : K} {ts : List K} {m : Γ}
    (h0 : v t0 = m) (hts : ∀ t ∈ ts, m < v t) :
    v ((t0 :: ts).sum) = m := by
  induction ts generalizing t0 with
  | nil =>
      simpa [List.sum_cons] using h0
  | cons a rest ih =>
      have ha : v t0 < v a := by
        rw [h0]
        exact hts a (by simp)
      have hta : v (t0 + a) = m := by
        simpa [h0] using hstrict t0 a ha
      have hrest : ∀ t ∈ rest, m < v t := by
        intro t ht
        exact hts t (by simp [ht])
      have ih' := ih (t0 := t0 + a) hta hrest
      simpa [List.sum_cons, add_assoc] using ih'

theorem strictMin_add_list_sum {K Γ : Type*} [AddCommMonoid K] [Preorder Γ]
    {v : K → Γ} (hstrict : ∀ a b : K, v a < v b → v (a + b) = v a)
    {t0 : K} {ts : List K} {m : Γ}
    (h0 : v t0 = m) (hts : ∀ t ∈ ts, m < v t) :
    v (t0 + ts.sum) = m := by
  simpa [List.sum_cons] using
    strictMin_list_sum (v := v) hstrict (t0 := t0) (ts := ts) (m := m) h0 hts

end QwenModels
