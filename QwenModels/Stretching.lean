import QwenModels.BlackBoxes
import QwenModels.Pure
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Valuation.Basic

namespace QwenModels

open Polynomial
open scoped Convex

/-!
Current frontier module.

Quoted external theorems live in `QwenModels.BlackBoxes`.  This file is reserved
for actual paper-result theorems; supporting facts should stay local inside those
proofs rather than becoming new helper API.
-/

/- The anonymous examples below are proof checks only; they intentionally export
no named API. -/

example {X Y Z : Set (ℝ × ℝ)} (hZ : Z ⊆ X ∪ Y) :
    lowerConvexEpigraph Z ⊆ lowerConvexEpigraph (X ∪ Y) := by
  exact lowerConvexEpigraph_mono hZ

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {r : ℕ} {f : K[X]}
    (h : PrPure ord r f) :
    HasNewtonPolygonData ord f
      [{ length := f.natDegree, length_pos := PrPure.natDegree_pos h,
         slope := prPureSlope r f.natDegree }] := by
  exact PureAt.hasNewtonPolygonData h.2.choose_spec.2.2

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    (h : PrPure (v : K → WithTop ℤ) r f) : f.coeff 0 ≠ 0 := by
  rw [← AddValuation.ne_top_iff v]
  rw [PrPure.coeff_zero_valuation h]
  simp

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    (h : PrPure (v : K → WithTop ℤ) r f) : f.leadingCoeff ≠ 0 := by
  rw [← AddValuation.ne_top_iff v]
  rw [PrPure.leadingCoeff_valuation h]
  simp

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    (h : PrPure (v : K → WithTop ℤ) r f) :
    ((0 : ℝ), (r : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
  apply coefficientSupport_subset_newtonPolygon
  refine ⟨0, (r : ℤ), Nat.zero_le _, ?_, ?_, ?_⟩
  · rw [← AddValuation.ne_top_iff v]
    rw [PrPure.coeff_zero_valuation h]
    simp
  · exact PrPure.coeff_zero_valuation h
  · simp

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    (h : PrPure (v : K → WithTop ℤ) r f) :
    ((f.natDegree : ℝ), (0 : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
  apply coefficientSupport_subset_newtonPolygon
  refine ⟨f.natDegree, (0 : ℤ), le_rfl, ?_, ?_, ?_⟩
  · rw [← AddValuation.ne_top_iff v]
    rw [Polynomial.coeff_natDegree]
    rw [PrPure.leadingCoeff_valuation h]
    simp
  · rw [Polynomial.coeff_natDegree]
    exact PrPure.leadingCoeff_valuation h
  · simp

example {K : Type*} [Semiring K] {factors : List K[X]} {data : NewtonPolygonData}
    (hforall : List.Forall₂
      (fun factor seg =>
        factor.natDegree = seg.length ∧
          PureAt (fun _ : K => (⊤ : WithTop ℤ)) factor seg.slope)
      factors data) :
    factors.map (fun factor : K[X] => factor.natDegree) =
      data.map (fun seg : SegmentData => seg.length) := by
  induction hforall with
  | nil => rfl
  | cons h hd ih =>
      simp [h.1, ih]

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {factors : List K[X]} {data : NewtonPolygonData}
    (hforall : List.Forall₂
      (fun factor seg => factor.natDegree = seg.length ∧ PureAt ord factor seg.slope)
      factors data) :
    factors.map (fun factor : K[X] => factor.natDegree) =
      data.map (fun seg : SegmentData => seg.length) := by
  induction hforall with
  | nil => rfl
  | cons h hd ih => simp [h.1, ih]

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {factors : List K[X]} {data : NewtonPolygonData}
    (hforall : List.Forall₂
      (fun factor seg => factor.natDegree = seg.length ∧ PureAt ord factor seg.slope)
      factors data) :
    factors.length = data.length := by
  exact List.Forall₂.length_eq hforall

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {f : K[X]}
    {data : NewtonPolygonData} (h : HasNewtonPolygonData ord f data)
    (hpos : 0 < f.natDegree) : data ≠ [] := by
  intro hnil
  have hdeg := HasNewtonPolygonData.natDegree_eq_totalLength h
  rw [hnil, totalLength_nil] at hdeg
  exact Nat.ne_of_gt hpos hdeg

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {f : K[X]}
    {data : NewtonPolygonData} (h : HasNewtonPolygonData ord f data) :
    f.natDegree = (data.map fun seg => seg.length).sum := by
  have htotal : ∀ data : NewtonPolygonData,
      totalLength data = (data.map fun seg => seg.length).sum := by
    intro data
    induction data with
    | nil => simp [totalLength]
    | cons seg rest ih => simp [totalLength, ih]
  rw [HasNewtonPolygonData.natDegree_eq_totalLength h, htotal data]

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {f : K[X]}
    {data : NewtonPolygonData} (h : HasNewtonPolygonData ord f data) :
    ∃ startHeight : ℚ, newtonPolygon ord f = polygonEpigraph startHeight data := by
  exact HasNewtonPolygonData.exists_startHeight h

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {f : K[X]} {i : ℕ} {z : ℤ}
    (hi : i ≤ f.natDegree) (hcoeff : f.coeff i ≠ 0)
    (hz : ord (f.coeff i) = ((z : ℤ) : WithTop ℤ)) :
    ((i : ℝ), (z : ℝ)) ∈ newtonPolygon ord f := by
  exact coefficientSupport_subset_newtonPolygon ord f ⟨i, z, hi, hcoeff, hz, rfl⟩

example (r : ℝ) :
    Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ (p.1 = 0 → r ≤ p.2)} := by
  intro x hx y hy a b ha hb hab
  constructor
  · change 0 ≤ a * x.1 + b * y.1
    exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · intro hzero
    have hsumx : a * x.1 + b * y.1 = 0 := by simpa using hzero
    have hax : a * x.1 = 0 := by
      have hnonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
      have hby_nonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
      nlinarith
    have hby : b * y.1 = 0 := by
      have hnonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
      have hax_nonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
      nlinarith
    have hxlower : a * r ≤ a * x.2 := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have hx0 : x.1 = 0 := by
          rcases mul_eq_zero.mp hax with ha_zero | hx_zero
          · exact (ha0 ha_zero).elim
          · exact hx_zero
        exact mul_le_mul_of_nonneg_left (hx.2 hx0) ha
    have hylower : b * r ≤ b * y.2 := by
      by_cases hb0 : b = 0
      · simp [hb0]
      · have hy0 : y.1 = 0 := by
          rcases mul_eq_zero.mp hby with hb_zero | hy_zero
          · exact (hb0 hb_zero).elim
          · exact hy_zero
        exact mul_le_mul_of_nonneg_left (hy.2 hy0) hb
    have hsumlower : a * r + b * r ≤ a * x.2 + b * y.2 := add_le_add hxlower hylower
    change r ≤ a * x.2 + b * y.2
    calc
      r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x.2 + b * y.2 := hsumlower

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) :
    coefficientSupportPoints (v : K → WithTop ℤ) f ⊆
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ (p.1 = 0 → (r : ℝ) ≤ p.2)} := by
  intro p hp
  rcases hp with ⟨i, z, hi, hcoeff, hz, rfl⟩
  constructor
  · change (0 : ℝ) ≤ (i : ℝ)
    exact_mod_cast Nat.zero_le i
  · intro hx0
    have hx0' : (i : ℝ) = 0 := by simpa using hx0
    have hi0 : i = 0 := by exact_mod_cast hx0'
    subst i
    have hzeq : ((z : ℤ) : WithTop ℤ) = (((r : ℤ) : WithTop ℤ)) := by
      rw [← hz, PrPure.coeff_zero_valuation hf]
    have hzint : z = (r : ℤ) := WithTop.coe_eq_coe.mp hzeq
    rw [hzint]
    exact_mod_cast le_rfl

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    {p : ℝ × ℝ}
    (hf : PrPure (v : K → WithTop ℤ) r f)
    (hp : p ∈ convexHull ℝ (coefficientSupportPoints (v : K → WithTop ℤ) f))
    (hpx : p.1 = 0) :
    (r : ℝ) ≤ p.2 := by
  let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ (q.1 = 0 → (r : ℝ) ≤ q.2)}
  have hWconv : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    constructor
    · change 0 ≤ a * x.1 + b * y.1
      exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    · intro hzero
      have hsumx : a * x.1 + b * y.1 = 0 := by simpa using hzero
      have hax : a * x.1 = 0 := by
        have hnonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
        have hby_nonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
        nlinarith
      have hby : b * y.1 = 0 := by
        have hnonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
        have hax_nonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
        nlinarith
      have hxlower : a * (r : ℝ) ≤ a * x.2 := by
        by_cases ha0 : a = 0
        · simp [ha0]
        · have hx0 : x.1 = 0 := by
            rcases mul_eq_zero.mp hax with ha_zero | hx_zero
            · exact (ha0 ha_zero).elim
            · exact hx_zero
          exact mul_le_mul_of_nonneg_left (hx.2 hx0) ha
      have hylower : b * (r : ℝ) ≤ b * y.2 := by
        by_cases hb0 : b = 0
        · simp [hb0]
        · have hy0 : y.1 = 0 := by
            rcases mul_eq_zero.mp hby with hb_zero | hy_zero
            · exact (hb0 hb_zero).elim
            · exact hy_zero
          exact mul_le_mul_of_nonneg_left (hy.2 hy0) hb
      have hsumlower :
          a * (r : ℝ) + b * (r : ℝ) ≤ a * x.2 + b * y.2 := add_le_add hxlower hylower
      change (r : ℝ) ≤ a * x.2 + b * y.2
      calc
        (r : ℝ) = a * (r : ℝ) + b * (r : ℝ) := by rw [← add_mul, hab, one_mul]
        _ ≤ a * x.2 + b * y.2 := hsumlower
  have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
    intro q hq
    rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
    constructor
    · change (0 : ℝ) ≤ (i : ℝ)
      exact_mod_cast Nat.zero_le i
    · intro hx0
      have hx0' : (i : ℝ) = 0 := by simpa using hx0
      have hi0 : i = 0 := by exact_mod_cast hx0'
      subst i
      have hzeq : ((z : ℤ) : WithTop ℤ) = (((r : ℤ) : WithTop ℤ)) := by
        rw [← hz, PrPure.coeff_zero_valuation hf]
      have hzint : z = (r : ℤ) := WithTop.coe_eq_coe.mp hzeq
      rw [hzint]
      exact_mod_cast le_rfl
  have hpW : p ∈ W := convexHull_min hsub hWconv hp
  exact hpW.2 hpx

example {r n : ℕ} (hn : 0 < n) :
    SegmentData.nextVertex
      { length := n, length_pos := hn, slope := prPureSlope r n }
      ((0 : ℝ), (r : ℝ)) = ((n : ℝ), (0 : ℝ)) := by
  ext <;> simp [SegmentData.nextVertex, prPureSlope]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnr]
  ring

example {r n : ℕ} (hn : 0 < n) :
    verticesFrom ((0 : ℝ), (r : ℝ))
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
    [((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))] := by
  simp [verticesFrom, SegmentData.nextVertex, prPureSlope]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnr]
  ring

example {r n : ℕ} (hn : 0 < n) :
    verticesSet (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
    {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
  ext p
  constructor
  · intro hp
    simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hp ⊢
    rcases hp with hp | hp
    · left
      exact hp
    · right
      rw [hp]
      ext <;> simp
      have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      field_simp [hnr]
      ring
  · intro hp
    simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hp ⊢
    rcases hp with hp | hp
    · left
      exact hp
    · right
      rw [hp]
      ext <;> simp
      have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      field_simp [hnr]
      ring

example {r n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : p ∈ convexHull ℝ ({((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))) :
    p.2 = (r : ℝ) - ((r : ℝ) / (n : ℝ)) * p.1 := by
  rw [convexHull_pair] at hp
  rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
  have hx : p.1 = b * (n : ℝ) := by
    rw [← hpab]
    simp
  have hy : p.2 = a * (r : ℝ) := by
    rw [← hpab]
    simp
  rw [hy, hx]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hn0]
  nlinarith [hab]

example {r n : ℕ} (hn : 0 < n) {q : ℝ × ℝ}
    (hq : q ∈ polygonEpigraph (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }]) :
    (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2 := by
  rcases hq with ⟨p, hp, hpx, hpy⟩
  have hverts : verticesSet (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
      {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
    ext x
    constructor
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
        ext <;> simp
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        ring
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
        ext <;> simp
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        ring
  rw [hverts] at hp
  have hline : p.2 = (r : ℝ) - ((r : ℝ) / (n : ℝ)) * p.1 := by
    rw [convexHull_pair] at hp
    rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
    have hx : p.1 = b * (n : ℝ) := by
      rw [← hpab]
      simp
    have hy : p.2 = a * (r : ℝ) := by
      rw [← hpab]
      simp
    rw [hy, hx]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hn0]
    nlinarith [hab]
  rw [← hpx]
  rw [← hline]
  exact hpy

example {r n : ℕ} (hn : 0 < n) :
    polygonEpigraph (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
      (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2} := by
  ext q
  constructor
  · intro hq
    rcases hq with ⟨p, hp, hpx, hpy⟩
    have hverts : verticesSet (r : ℚ)
        [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
        {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
      ext x
      constructor
      · intro hx
        simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
        rcases hx with hx | hx
        · left
          exact hx
        · right
          rw [hx]
          ext <;> simp
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          field_simp [hn0]
          ring
      · intro hx
        simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
        rcases hx with hx | hx
        · left
          exact hx
        · right
          rw [hx]
          ext <;> simp
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          field_simp [hn0]
          ring
    rw [hverts] at hp
    rw [convexHull_pair] at hp
    rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
    have hx : p.1 = b * (n : ℝ) := by
      rw [← hpab]
      simp
    have hy : p.2 = a * (r : ℝ) := by
      rw [← hpab]
      simp
    constructor
    · rw [← hpx, hx]
      exact mul_nonneg hb (by exact_mod_cast hn.le)
    constructor
    · rw [← hpx, hx]
      nlinarith [hab, ha, hb, show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn.le]
    · have hline : p.2 = (r : ℝ) - ((r : ℝ) / (n : ℝ)) * p.1 := by
        rw [hy, hx]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        nlinarith [hab]
      rw [← hpx]
      rw [← hline]
      exact hpy
  · intro hq
    rcases hq with ⟨hqx0, hqxn, hqline⟩
    let p : ℝ × ℝ := (q.1, (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1)
    refine ⟨p, ?_, ?_, ?_⟩
    · have hverts : verticesSet (r : ℚ)
          [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
          {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
        ext x
        constructor
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
            ext <;> simp
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
            field_simp [hn0]
            ring
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
            ext <;> simp
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
            field_simp [hn0]
            ring
      rw [hverts]
      rw [convexHull_pair]
      refine ⟨1 - q.1 / (n : ℝ), q.1 / (n : ℝ), ?_, ?_, ?_, ?_⟩
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        field_simp [ne_of_gt hnpos]
        nlinarith
      · exact div_nonneg hqx0 (by exact_mod_cast hn.le)
      · field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]
        ring
      · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        ext
        · simp [p]
          field_simp [hn0]
        · simp [p]
          field_simp [hn0]
    · rfl
    · exact hqline

example {r n : ℕ} :
    Convex ℝ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
      (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2} := by
  intro x hx y hy a b ha hb hab
  constructor
  · change 0 ≤ a * x.1 + b * y.1
    exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  constructor
  · change a * x.1 + b * y.1 ≤ (n : ℝ)
    calc
      a * x.1 + b * y.1 ≤ a * (n : ℝ) + b * (n : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
          (mul_le_mul_of_nonneg_left hy.2.1 hb)
      _ = (n : ℝ) := by rw [← add_mul, hab, one_mul]
  · change (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (a * x.1 + b * y.1) ≤
      a * x.2 + b * y.2
    have hxline :
        a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) ≤ a * x.2 :=
      mul_le_mul_of_nonneg_left hx.2.2 ha
    have hyline :
        b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) ≤ b * y.2 :=
      mul_le_mul_of_nonneg_left hy.2.2 hb
    have hsum :
        a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) +
            b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) ≤
          a * x.2 + b * y.2 :=
      add_le_add hxline hyline
    have haff :
        (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (a * x.1 + b * y.1) =
          a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) +
            b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) := by
      ring_nf
      nlinarith
    rw [haff]
    exact hsum

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {r n : ℕ} {f : K[X]}
    (hn : 0 < n)
    (hsub : coefficientSupportPoints ord f ⊆
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
        (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2}) :
    newtonPolygon ord f ⊆ polygonEpigraph (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] := by
  intro q hq
  rcases hq with ⟨p, hp, hpx, hpy⟩
  let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
    (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2}
  have hWconv : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    constructor
    · change 0 ≤ a * x.1 + b * y.1
      exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    constructor
    · change a * x.1 + b * y.1 ≤ (n : ℝ)
      calc
        a * x.1 + b * y.1 ≤ a * (n : ℝ) + b * (n : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
            (mul_le_mul_of_nonneg_left hy.2.1 hb)
        _ = (n : ℝ) := by rw [← add_mul, hab, one_mul]
    · change (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (a * x.1 + b * y.1) ≤
        a * x.2 + b * y.2
      have hxline :
          a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) ≤ a * x.2 :=
        mul_le_mul_of_nonneg_left hx.2.2 ha
      have hyline :
          b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) ≤ b * y.2 :=
        mul_le_mul_of_nonneg_left hy.2.2 hb
      have hsum :
          a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) +
              b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) ≤
            a * x.2 + b * y.2 :=
        add_le_add hxline hyline
      have haff :
          (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (a * x.1 + b * y.1) =
            a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) +
              b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) := by
        ring_nf
        nlinarith
      rw [haff]
      exact hsum
  have hpW : p ∈ W := convexHull_min hsub hWconv hp
  have hqW : q ∈ W := by
    constructor
    · rw [← hpx]
      exact hpW.1
    constructor
    · rw [← hpx]
      exact hpW.2.1
    · have hlinep :
          (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 =
            (r : ℝ) - ((r : ℝ) / (n : ℝ)) * p.1 := by
        rw [← hpx]
      rw [hlinep]
      exact le_trans hpW.2.2 hpy
  rcases hqW with ⟨hqx0, hqxn, hqline⟩
  let p0 : ℝ × ℝ := (q.1, (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1)
  refine ⟨p0, ?_, ?_, ?_⟩
  · have hverts : verticesSet (r : ℚ)
        [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
        {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
      ext x
      constructor
      · intro hx
        simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
        rcases hx with hx | hx
        · left
          exact hx
        · right
          rw [hx]
          ext <;> simp
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          field_simp [hn0]
          ring
      · intro hx
        simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
        rcases hx with hx | hx
        · left
          exact hx
        · right
          rw [hx]
          ext <;> simp
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          field_simp [hn0]
          ring
    rw [hverts]
    rw [convexHull_pair]
    refine ⟨1 - q.1 / (n : ℝ), q.1 / (n : ℝ), ?_, ?_, ?_, ?_⟩
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      field_simp [ne_of_gt hnpos]
      nlinarith
    · exact div_nonneg hqx0 (by exact_mod_cast hn.le)
    · field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]
      ring
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      ext
      · simp [p0]
        field_simp [hn0]
      · simp [p0]
        field_simp [hn0]
  · rfl
  · exact hqline

private theorem oneSegment_reverse_inclusion
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r n : ℕ} {f : K[X]}
    (hn : 0 < n) (hdeg : f.natDegree = n)
    (h0 : v (f.coeff 0) = (((r : ℤ) : WithTop ℤ)))
    (hlead : v f.leadingCoeff = (((0 : ℤ) : WithTop ℤ))) :
    polygonEpigraph (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] ⊆
    newtonPolygon (v : K → WithTop ℤ) f := by
  change lowerConvexEpigraph (verticesSet (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }]) ⊆
    lowerConvexEpigraph (coefficientSupportPoints (v : K → WithTop ℤ) f)
  apply lowerConvexEpigraph_mono
  intro p hp
  have hverts : verticesSet (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
      {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
    ext x
    constructor
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
        ext <;> simp
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        ring
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
        ext <;> simp
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        ring
  rw [hverts] at hp
  rcases hp with hp | hp
  · rw [hp]
    refine ⟨0, (r : ℤ), Nat.zero_le _, ?_, h0, ?_⟩
    · rw [← AddValuation.ne_top_iff v]
      rw [h0]
      simp
    · simp
  · rw [hp]
    refine ⟨n, (0 : ℤ), ?_, ?_, ?_, ?_⟩
    · rw [← hdeg]
    · rw [← AddValuation.ne_top_iff v]
      rw [← hdeg, Polynomial.coeff_natDegree]
      rw [hlead]
      simp
    · rw [← hdeg, Polynomial.coeff_natDegree]
      exact hlead
    · simp

private theorem oneSegment_support_subset_of_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r n : ℕ} {f : K[X]}
    (hdeg : f.natDegree = n)
    (hlower : ∀ i z, i ≤ n → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (i : ℝ) ≤ (z : ℝ)) :
    coefficientSupportPoints (v : K → WithTop ℤ) f ⊆
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
        (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2} := by
  intro q hq
  rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
  constructor
  · change (0 : ℝ) ≤ (i : ℝ)
    exact_mod_cast Nat.zero_le i
  constructor
  · change (i : ℝ) ≤ (n : ℝ)
    have hin : i ≤ n := by simpa [hdeg] using hi
    exact_mod_cast hin
  · exact hlower i z (by simpa [hdeg] using hi) hcoeff hz

private theorem oneSegment_of_endpoint_and_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r n : ℕ} {f : K[X]}
    (hn : 0 < n) (hdeg : f.natDegree = n)
    (h0 : v (f.coeff 0) = (((r : ℤ) : WithTop ℤ)))
    (hlead : v f.leadingCoeff = (((0 : ℤ) : WithTop ℤ)))
    (hlower : ∀ i z, i ≤ n → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (i : ℝ) ≤ (z : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) f
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] := by
  constructor
  · simp
  constructor
  · simpa [totalLength] using hdeg
  · refine ⟨(r : ℚ), ?_⟩
    apply Set.Subset.antisymm
    · intro q hq
      rcases hq with ⟨p, hp, hpx, hpy⟩
      let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
        (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 ≤ q.2}
      have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
        intro q hq
        rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
        constructor
        · change (0 : ℝ) ≤ (i : ℝ)
          exact_mod_cast Nat.zero_le i
        constructor
        · change (i : ℝ) ≤ (n : ℝ)
          have hin : i ≤ n := by simpa [hdeg] using hi
          exact_mod_cast hin
        · exact hlower i z (by simpa [hdeg] using hi) hcoeff hz
      have hWconv : Convex ℝ W := by
        intro x hx y hy a b ha hb hab
        constructor
        · change 0 ≤ a * x.1 + b * y.1
          exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
        constructor
        · change a * x.1 + b * y.1 ≤ (n : ℝ)
          calc
            a * x.1 + b * y.1 ≤ a * (n : ℝ) + b * (n : ℝ) :=
              add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
                (mul_le_mul_of_nonneg_left hy.2.1 hb)
            _ = (n : ℝ) := by rw [← add_mul, hab, one_mul]
        · change (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (a * x.1 + b * y.1) ≤
            a * x.2 + b * y.2
          have hxline :
              a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) ≤ a * x.2 :=
            mul_le_mul_of_nonneg_left hx.2.2 ha
          have hyline :
              b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) ≤ b * y.2 :=
            mul_le_mul_of_nonneg_left hy.2.2 hb
          have hsum :
              a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) +
                  b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) ≤
                a * x.2 + b * y.2 :=
            add_le_add hxline hyline
          have haff :
              (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (a * x.1 + b * y.1) =
                a * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * x.1) +
                  b * ((r : ℝ) - ((r : ℝ) / (n : ℝ)) * y.1) := by
            ring_nf
            nlinarith
          rw [haff]
          exact hsum
      have hpW : p ∈ W := convexHull_min hsub hWconv hp
      have hqW : q ∈ W := by
        constructor
        · rw [← hpx]
          exact hpW.1
        constructor
        · rw [← hpx]
          exact hpW.2.1
        · have hlinep :
              (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1 =
                (r : ℝ) - ((r : ℝ) / (n : ℝ)) * p.1 := by
            rw [← hpx]
          rw [hlinep]
          exact le_trans hpW.2.2 hpy
      rcases hqW with ⟨hqx0, hqxn, hqline⟩
      let p0 : ℝ × ℝ := (q.1, (r : ℝ) - ((r : ℝ) / (n : ℝ)) * q.1)
      refine ⟨p0, ?_, ?_, ?_⟩
      · have hverts : verticesSet (r : ℚ)
            [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
            {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
          ext x
          constructor
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
              field_simp [hn0]
              ring
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
              field_simp [hn0]
              ring
        rw [hverts]
        rw [convexHull_pair]
        refine ⟨1 - q.1 / (n : ℝ), q.1 / (n : ℝ), ?_, ?_, ?_, ?_⟩
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          field_simp [ne_of_gt hnpos]
          nlinarith
        · exact div_nonneg hqx0 (by exact_mod_cast hn.le)
        · field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]
          ring
        · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          ext
          · simp [p0]
            field_simp [hn0]
          · simp [p0]
            field_simp [hn0]
      · rfl
      · exact hqline
    · change lowerConvexEpigraph (verticesSet (r : ℚ)
          [{ length := n, length_pos := hn, slope := prPureSlope r n }]) ⊆
        lowerConvexEpigraph (coefficientSupportPoints (v : K → WithTop ℤ) f)
      apply lowerConvexEpigraph_mono
      intro p hp
      have hverts : verticesSet (r : ℚ)
          [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
          {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
        ext x
        constructor
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
            ext <;> simp
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
            field_simp [hn0]
            ring
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
            ext <;> simp
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
            field_simp [hn0]
            ring
      rw [hverts] at hp
      rcases hp with hp | hp
      · rw [hp]
        refine ⟨0, (r : ℤ), Nat.zero_le _, ?_, h0, ?_⟩
        · rw [← AddValuation.ne_top_iff v]
          rw [h0]
          simp
        · simp
      · rw [hp]
        refine ⟨n, (0 : ℤ), ?_, ?_, ?_, ?_⟩
        · rw [← hdeg]
        · rw [← AddValuation.ne_top_iff v]
          rw [← hdeg, Polynomial.coeff_natDegree]
          rw [hlead]
          simp
        · rw [← hdeg, Polynomial.coeff_natDegree]
          exact hlead
        · simp

private theorem oneSegment_line_lower_of_newtonPolygon_eq
    {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {r n i : ℕ} {z : ℤ} {f : K[X]}
    (hn : 0 < n)
    (hNP : newtonPolygon ord f = polygonEpigraph (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }])
    (hi : i ≤ f.natDegree) (hcoeff : f.coeff i ≠ 0)
    (hz : ord (f.coeff i) = ((z : ℤ) : WithTop ℤ)) :
    (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (i : ℝ) ≤ (z : ℝ) := by
  have hpt : ((i : ℝ), (z : ℝ)) ∈ newtonPolygon ord f := by
    exact coefficientSupport_subset_newtonPolygon ord f ⟨i, z, hi, hcoeff, hz, rfl⟩
  rw [hNP] at hpt
  rcases hpt with ⟨p, hp, hpx, hpy⟩
  have hverts : verticesSet (r : ℚ)
      [{ length := n, length_pos := hn, slope := prPureSlope r n }] =
      {((0 : ℝ), (r : ℝ)), ((n : ℝ), (0 : ℝ))} := by
    ext x
    constructor
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
        ext <;> simp
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        ring
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
        ext <;> simp
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        field_simp [hn0]
        ring
  rw [hverts] at hp
  have hline : p.2 = (r : ℝ) - ((r : ℝ) / (n : ℝ)) * p.1 := by
    rw [convexHull_pair] at hp
    rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
    have hx : p.1 = b * (n : ℝ) := by
      rw [← hpab]
      simp
    have hy : p.2 = a * (r : ℝ) := by
      rw [← hpab]
      simp
    rw [hy, hx]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hn0]
    nlinarith [hab]
  have hpxi : p.1 = (i : ℝ) := by simpa using hpx
  have hpyz : p.2 ≤ (z : ℝ) := by simpa using hpy
  rw [← hpxi]
  rw [← hline]
  exact hpyz

private theorem oneSegment_affine_lower_of_newtonPolygon_eq
    {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {start slope : ℚ}
    {n i : ℕ} {z : ℤ} {f : K[X]}
    (hn : 0 < n)
    (hNP : newtonPolygon ord f = polygonEpigraph start
      [{ length := n, length_pos := hn, slope := slope }])
    (hi : i ≤ f.natDegree) (hcoeff : f.coeff i ≠ 0)
    (hz : ord (f.coeff i) = ((z : ℤ) : WithTop ℤ)) :
    (start : ℝ) + (slope : ℝ) * (i : ℝ) ≤ (z : ℝ) := by
  have hpt : ((i : ℝ), (z : ℝ)) ∈ newtonPolygon ord f := by
    exact coefficientSupport_subset_newtonPolygon ord f ⟨i, z, hi, hcoeff, hz, rfl⟩
  rw [hNP] at hpt
  rcases hpt with ⟨p, hp, hpx, hpy⟩
  have hverts : verticesSet start [{ length := n, length_pos := hn, slope := slope }] =
      {((0 : ℝ), (start : ℝ)), ((n : ℝ), (start : ℝ) + (n : ℝ) * (slope : ℝ))} := by
    ext x
    constructor
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
    · intro hx
      simp [verticesSet, verticesFrom, SegmentData.nextVertex] at hx ⊢
      rcases hx with hx | hx
      · left
        exact hx
      · right
        rw [hx]
  rw [hverts] at hp
  have hline : p.2 = (start : ℝ) + (slope : ℝ) * p.1 := by
    rw [convexHull_pair] at hp
    rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
    have hx : p.1 = b * (n : ℝ) := by
      rw [← hpab]
      simp
    have hy : p.2 =
        a * (start : ℝ) + b * ((start : ℝ) + (n : ℝ) * (slope : ℝ)) := by
      rw [← hpab]
      simp [mul_add, add_comm]
    rw [hy, hx]
    calc
      a * (start : ℝ) + b * ((start : ℝ) + (n : ℝ) * (slope : ℝ)) =
          (a + b) * (start : ℝ) + b * ((n : ℝ) * (slope : ℝ)) := by ring
      _ = (start : ℝ) + (slope : ℝ) * (b * (n : ℝ)) := by
          rw [hab]
          ring
  have hpxi : p.1 = (i : ℝ) := by simpa using hpx
  have hpyz : p.2 ≤ (z : ℝ) := by simpa using hpy
  rw [← hpxi]
  rw [← hline]
  exact hpyz

private theorem oneSegment_coeff_zero_ne
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {start slope : ℚ}
    {n : ℕ} {f : K[X]}
    (hn : 0 < n)
    (hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph start
      [{ length := n, length_pos := hn, slope := slope }]) :
    f.coeff 0 ≠ 0 := by
  intro hzero
  have hstartPoly : ((0 : ℝ), (start : ℝ)) ∈ polygonEpigraph start
      [{ length := n, length_pos := hn, slope := slope }] := by
    exact start_mem_polygonEpigraph start [{ length := n, length_pos := hn, slope := slope }]
  have hstartNP : ((0 : ℝ), (start : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
    rw [hNP]
    exact hstartPoly
  rcases hstartNP with ⟨p, hp, hpx, hpy⟩
  have hpx0 : p.1 = 0 := by simpa using hpx
  let W : Set (ℝ × ℝ) := {q | (1 : ℝ) ≤ q.1}
  have hWconv : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    change (1 : ℝ) ≤ a * x.1 + b * y.1
    calc
      (1 : ℝ) = a * (1 : ℝ) + b * (1 : ℝ) := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x.1 + b * y.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha)
          (mul_le_mul_of_nonneg_left hy hb)
  have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
    intro q hq
    rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
    change (1 : ℝ) ≤ (i : ℝ)
    have hi0 : i ≠ 0 := by
      intro hi0
      subst i
      exact hcoeff hzero
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
  have hpW : p ∈ W := convexHull_min hsub hWconv hp
  change (1 : ℝ) ≤ p.1 at hpW
  nlinarith

private theorem oneSegment_start_eq_coeff_zero_of_valuation
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {start slope : ℚ}
    {n : ℕ} {f : K[X]} {z0 : ℤ}
    (hn : 0 < n)
    (hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph start
      [{ length := n, length_pos := hn, slope := slope }])
    (h0 : v (f.coeff 0) = ((z0 : ℤ) : WithTop ℤ)) :
    start = (z0 : ℚ) := by
  have hcoeff0 : f.coeff 0 ≠ 0 := by
    rw [← AddValuation.ne_top_iff v]
    rw [h0]
    simp
  have hstart_le_z0 : (start : ℝ) ≤ (z0 : ℝ) := by
    simpa using oneSegment_affine_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (start := start) (slope := slope)
      (n := n) (i := 0) (z := z0) (f := f) hn hNP (Nat.zero_le _) hcoeff0 h0
  have hz0_le_start : (z0 : ℝ) ≤ (start : ℝ) := by
    have hstartPoly : ((0 : ℝ), (start : ℝ)) ∈ polygonEpigraph start
        [{ length := n, length_pos := hn, slope := slope }] := by
      exact start_mem_polygonEpigraph start [{ length := n, length_pos := hn, slope := slope }]
    have hstartNP : ((0 : ℝ), (start : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
      rw [hNP]
      exact hstartPoly
    rcases hstartNP with ⟨p, hp, hpx, hpy⟩
    have hpx0 : p.1 = 0 := by simpa using hpx
    let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ (q.1 = 0 → (z0 : ℝ) ≤ q.2)}
    have hWconv : Convex ℝ W := by
      intro x hx y hy a b ha hb hab
      constructor
      · change 0 ≤ a * x.1 + b * y.1
        exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      · intro hzero
        have hsumx : a * x.1 + b * y.1 = 0 := by simpa using hzero
        have hax : a * x.1 = 0 := by
          have hnonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
          have hby_nonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
          nlinarith
        have hby : b * y.1 = 0 := by
          have hnonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
          have hax_nonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
          nlinarith
        have hxlower : a * (z0 : ℝ) ≤ a * x.2 := by
          by_cases ha0 : a = 0
          · simp [ha0]
          · have hx0 : x.1 = 0 := by
              rcases mul_eq_zero.mp hax with ha_zero | hx_zero
              · exact (ha0 ha_zero).elim
              · exact hx_zero
            exact mul_le_mul_of_nonneg_left (hx.2 hx0) ha
        have hylower : b * (z0 : ℝ) ≤ b * y.2 := by
          by_cases hb0 : b = 0
          · simp [hb0]
          · have hy0 : y.1 = 0 := by
              rcases mul_eq_zero.mp hby with hb_zero | hy_zero
              · exact (hb0 hb_zero).elim
              · exact hy_zero
            exact mul_le_mul_of_nonneg_left (hy.2 hy0) hb
        have hsumlower : a * (z0 : ℝ) + b * (z0 : ℝ) ≤ a * x.2 + b * y.2 :=
          add_le_add hxlower hylower
        change (z0 : ℝ) ≤ a * x.2 + b * y.2
        calc
          (z0 : ℝ) = a * (z0 : ℝ) + b * (z0 : ℝ) := by
            rw [← add_mul, hab, one_mul]
          _ ≤ a * x.2 + b * y.2 := hsumlower
    have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
      intro q hq
      rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
      constructor
      · change (0 : ℝ) ≤ (i : ℝ)
        exact_mod_cast Nat.zero_le i
      · intro hx0
        have hx0' : (i : ℝ) = 0 := by simpa using hx0
        have hi0 : i = 0 := by exact_mod_cast hx0'
        subst i
        have hzeq : ((z : ℤ) : WithTop ℤ) = (((z0 : ℤ) : WithTop ℤ)) := by
          rw [← hz, h0]
        have hzint : z = z0 := WithTop.coe_eq_coe.mp hzeq
        rw [hzint]
    have hpW : p ∈ W := convexHull_min hsub hWconv hp
    exact le_trans (hpW.2 hpx0) hpy
  have hsR : (start : ℝ) = (z0 : ℝ) := le_antisymm hstart_le_z0 hz0_le_start
  exact_mod_cast hsR

private theorem oneSegment_end_eq_leadingCoeff_of_valuation
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {start slope : ℚ}
    {n : ℕ} {f : K[X]} {zN : ℤ}
    (hn : 0 < n) (hdeg : f.natDegree = n)
    (hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph start
      [{ length := n, length_pos := hn, slope := slope }])
    (hlead : v f.leadingCoeff = ((zN : ℤ) : WithTop ℤ)) :
    start + (n : ℚ) * slope = (zN : ℚ) := by
  have hcoeffN : f.coeff n ≠ 0 := by
    rw [← AddValuation.ne_top_iff v]
    rw [← hdeg, Polynomial.coeff_natDegree, hlead]
    simp
  have hcoeffN_val : v (f.coeff n) = ((zN : ℤ) : WithTop ℤ) := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact hlead
  have hline_le : (start : ℝ) + (slope : ℝ) * (n : ℝ) ≤ (zN : ℝ) := by
    have hi : n ≤ f.natDegree := by rw [hdeg]
    simpa [mul_comm] using oneSegment_affine_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (start := start) (slope := slope)
      (n := n) (i := n) (z := zN) (f := f) hn hNP hi hcoeffN
      hcoeffN_val
  have hzN_le_line : (zN : ℝ) ≤ (start : ℝ) + (n : ℝ) * (slope : ℝ) := by
    let endpoint : ℝ × ℝ := ((n : ℝ), (start : ℝ) + (n : ℝ) * (slope : ℝ))
    have hendVertex :
        endpoint ∈ verticesSet start [{ length := n, length_pos := hn, slope := slope }] := by
      simp [endpoint, verticesSet, verticesFrom, SegmentData.nextVertex]
    have hendPoly : endpoint ∈ polygonEpigraph start
        [{ length := n, length_pos := hn, slope := slope }] :=
      verticesSet_subset_polygonEpigraph start
        [{ length := n, length_pos := hn, slope := slope }] hendVertex
    have hendNP : endpoint ∈ newtonPolygon (v : K → WithTop ℤ) f := by
      rw [hNP]
      exact hendPoly
    rcases hendNP with ⟨p, hp, hpx, hpy⟩
    have hpxn : p.1 = (n : ℝ) := by simpa [endpoint] using hpx
    let W : Set (ℝ × ℝ) :=
      {q | q.1 ≤ (n : ℝ) ∧ (q.1 = (n : ℝ) → (zN : ℝ) ≤ q.2)}
    have hWconv : Convex ℝ W := by
      intro x hx y hy a b ha hb hab
      constructor
      · change a * x.1 + b * y.1 ≤ (n : ℝ)
        calc
          a * x.1 + b * y.1 ≤ a * (n : ℝ) + b * (n : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
              (mul_le_mul_of_nonneg_left hy.1 hb)
          _ = (n : ℝ) := by rw [← add_mul, hab, one_mul]
      · intro hEq
        have hEq' : a * x.1 + b * y.1 = (n : ℝ) := by
          simpa using hEq
        have hdx_nonneg : 0 ≤ (n : ℝ) - x.1 := sub_nonneg.mpr hx.1
        have hdy_nonneg : 0 ≤ (n : ℝ) - y.1 := sub_nonneg.mpr hy.1
        have hsumdiff :
            a * ((n : ℝ) - x.1) + b * ((n : ℝ) - y.1) = 0 := by
          calc
            a * ((n : ℝ) - x.1) + b * ((n : ℝ) - y.1) =
                (a + b) * (n : ℝ) - (a * x.1 + b * y.1) := by ring
            _ = 0 := by rw [hab, hEq']; ring
        have hax : a * ((n : ℝ) - x.1) = 0 := by
          have hnonneg : 0 ≤ a * ((n : ℝ) - x.1) := mul_nonneg ha hdx_nonneg
          have hby_nonneg : 0 ≤ b * ((n : ℝ) - y.1) := mul_nonneg hb hdy_nonneg
          nlinarith
        have hby : b * ((n : ℝ) - y.1) = 0 := by
          have hnonneg : 0 ≤ b * ((n : ℝ) - y.1) := mul_nonneg hb hdy_nonneg
          have hax_nonneg : 0 ≤ a * ((n : ℝ) - x.1) := mul_nonneg ha hdx_nonneg
          nlinarith
        have hxlower : a * (zN : ℝ) ≤ a * x.2 := by
          by_cases ha0 : a = 0
          · simp [ha0]
          · have hxN : x.1 = (n : ℝ) := by
              rcases mul_eq_zero.mp hax with ha_zero | hx_zero
              · exact (ha0 ha_zero).elim
              · nlinarith
            exact mul_le_mul_of_nonneg_left (hx.2 hxN) ha
        have hylower : b * (zN : ℝ) ≤ b * y.2 := by
          by_cases hb0 : b = 0
          · simp [hb0]
          · have hyN : y.1 = (n : ℝ) := by
              rcases mul_eq_zero.mp hby with hb_zero | hy_zero
              · exact (hb0 hb_zero).elim
              · nlinarith
            exact mul_le_mul_of_nonneg_left (hy.2 hyN) hb
        have hsumlower : a * (zN : ℝ) + b * (zN : ℝ) ≤ a * x.2 + b * y.2 :=
          add_le_add hxlower hylower
        change (zN : ℝ) ≤ a * x.2 + b * y.2
        calc
          (zN : ℝ) = a * (zN : ℝ) + b * (zN : ℝ) := by
            rw [← add_mul, hab, one_mul]
          _ ≤ a * x.2 + b * y.2 := hsumlower
    have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
      intro q hq
      rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
      constructor
      · change (i : ℝ) ≤ (n : ℝ)
        have hin : i ≤ n := by simpa [hdeg] using hi
        exact_mod_cast hin
      · intro hxn
        have hxn' : (i : ℝ) = (n : ℝ) := by simpa using hxn
        have hiN : i = n := by exact_mod_cast hxn'
        subst i
        have hzeq : ((z : ℤ) : WithTop ℤ) = (((zN : ℤ) : WithTop ℤ)) := by
          rw [← hz, ← hdeg, Polynomial.coeff_natDegree, hlead]
        have hzint : z = zN := WithTop.coe_eq_coe.mp hzeq
        rw [hzint]
    have hpW : p ∈ W := convexHull_min hsub hWconv hp
    exact le_trans (hpW.2 hpxn) hpy
  have hR : (start : ℝ) + (n : ℝ) * (slope : ℝ) = (zN : ℝ) := by
    exact le_antisymm (by simpa [mul_comm] using hline_le) hzN_le_line
  exact_mod_cast hR

private theorem oneSegment_of_endpoint_and_affine_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {start slope : ℚ} {n : ℕ} {f : K[X]} {z0 zN : ℤ}
    (hn : 0 < n) (hdeg : f.natDegree = n)
    (h0 : v (f.coeff 0) = ((z0 : ℤ) : WithTop ℤ))
    (hlead : v f.leadingCoeff = ((zN : ℤ) : WithTop ℤ))
    (hstart : start = (z0 : ℚ))
    (hend : start + (n : ℚ) * slope = (zN : ℚ))
    (hlower : ∀ i z, i ≤ n → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (start : ℝ) + (slope : ℝ) * (i : ℝ) ≤ (z : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) f
      [{ length := n, length_pos := hn, slope := slope }] := by
  have hstartR : (start : ℝ) = (z0 : ℝ) := by exact_mod_cast hstart
  have hendR : (start : ℝ) + (n : ℝ) * (slope : ℝ) = (zN : ℝ) := by
    have hendR' : ((start + (n : ℚ) * slope : ℚ) : ℝ) = (zN : ℝ) := by
      exact_mod_cast hend
    simpa using hendR'
  constructor
  · simp
  constructor
  · simpa [totalLength] using hdeg
  · refine ⟨start, ?_⟩
    apply Set.Subset.antisymm
    · intro q hq
      rcases hq with ⟨p, hp, hpx, hpy⟩
      let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ (n : ℝ) ∧
        (start : ℝ) + (slope : ℝ) * q.1 ≤ q.2}
      have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
        intro q hq
        rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
        constructor
        · change (0 : ℝ) ≤ (i : ℝ)
          exact_mod_cast Nat.zero_le i
        constructor
        · change (i : ℝ) ≤ (n : ℝ)
          have hin : i ≤ n := by simpa [hdeg] using hi
          exact_mod_cast hin
        · exact hlower i z (by simpa [hdeg] using hi) hcoeff hz
      have hWconv : Convex ℝ W := by
        intro x hx y hy a b ha hb hab
        constructor
        · change 0 ≤ a * x.1 + b * y.1
          exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
        constructor
        · change a * x.1 + b * y.1 ≤ (n : ℝ)
          calc
            a * x.1 + b * y.1 ≤ a * (n : ℝ) + b * (n : ℝ) :=
              add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
                (mul_le_mul_of_nonneg_left hy.2.1 hb)
            _ = (n : ℝ) := by rw [← add_mul, hab, one_mul]
        · change (start : ℝ) + (slope : ℝ) * (a * x.1 + b * y.1) ≤
            a * x.2 + b * y.2
          have hxline :
              a * ((start : ℝ) + (slope : ℝ) * x.1) ≤ a * x.2 :=
            mul_le_mul_of_nonneg_left hx.2.2 ha
          have hyline :
              b * ((start : ℝ) + (slope : ℝ) * y.1) ≤ b * y.2 :=
            mul_le_mul_of_nonneg_left hy.2.2 hb
          have hsum :
              a * ((start : ℝ) + (slope : ℝ) * x.1) +
                  b * ((start : ℝ) + (slope : ℝ) * y.1) ≤
                a * x.2 + b * y.2 :=
            add_le_add hxline hyline
          have haff :
              (start : ℝ) + (slope : ℝ) * (a * x.1 + b * y.1) =
                a * ((start : ℝ) + (slope : ℝ) * x.1) +
                  b * ((start : ℝ) + (slope : ℝ) * y.1) := by
            calc
              (start : ℝ) + (slope : ℝ) * (a * x.1 + b * y.1) =
                  (a + b) * (start : ℝ) + (slope : ℝ) * (a * x.1 + b * y.1) := by
                rw [hab]
                ring
              _ = a * ((start : ℝ) + (slope : ℝ) * x.1) +
                  b * ((start : ℝ) + (slope : ℝ) * y.1) := by
                ring
          rw [haff]
          exact hsum
      have hpW : p ∈ W := convexHull_min hsub hWconv hp
      have hqW : q ∈ W := by
        constructor
        · rw [← hpx]
          exact hpW.1
        constructor
        · rw [← hpx]
          exact hpW.2.1
        · have hlinep :
              (start : ℝ) + (slope : ℝ) * q.1 =
                (start : ℝ) + (slope : ℝ) * p.1 := by
            rw [← hpx]
          rw [hlinep]
          exact le_trans hpW.2.2 hpy
      rcases hqW with ⟨hqx0, hqxn, hqline⟩
      let p0 : ℝ × ℝ := (q.1, (start : ℝ) + (slope : ℝ) * q.1)
      refine ⟨p0, ?_, ?_, ?_⟩
      · have hverts : verticesSet start [{ length := n, length_pos := hn, slope := slope }] =
            {((0 : ℝ), (start : ℝ)),
             ((n : ℝ), (start : ℝ) + (n : ℝ) * (slope : ℝ))} := by
          ext x
          constructor
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
        rw [hverts]
        rw [convexHull_pair]
        refine ⟨1 - q.1 / (n : ℝ), q.1 / (n : ℝ), ?_, ?_, ?_, ?_⟩
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          field_simp [ne_of_gt hnpos]
          nlinarith
        · exact div_nonneg hqx0 (by exact_mod_cast hn.le)
        · field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]
          ring
        · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          ext
          · simp [p0]
            field_simp [hn0]
          · simp [p0]
            field_simp [hn0]
            ring
      · rfl
      · exact hqline
    · change lowerConvexEpigraph (verticesSet start
          [{ length := n, length_pos := hn, slope := slope }]) ⊆
        lowerConvexEpigraph (coefficientSupportPoints (v : K → WithTop ℤ) f)
      apply lowerConvexEpigraph_mono
      intro p hp
      have hverts : verticesSet start [{ length := n, length_pos := hn, slope := slope }] =
          {((0 : ℝ), (start : ℝ)),
           ((n : ℝ), (start : ℝ) + (n : ℝ) * (slope : ℝ))} := by
        ext x
        constructor
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
      rw [hverts] at hp
      rcases hp with hp | hp
      · rw [hp]
        refine ⟨0, z0, Nat.zero_le _, ?_, h0, ?_⟩
        · rw [← AddValuation.ne_top_iff v]
          rw [h0]
          simp
        · ext <;> simp [hstartR]
      · rw [hp]
        refine ⟨n, zN, ?_, ?_, ?_, ?_⟩
        · rw [← hdeg]
        · rw [← AddValuation.ne_top_iff v]
          rw [← hdeg, Polynomial.coeff_natDegree, hlead]
          simp
        · rw [← hdeg, Polynomial.coeff_natDegree]
          exact hlead
        · ext <;> simp [hendR]

private theorem prPure_startHeight_eq
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    {s : ℚ} (hf : PrPure (v : K → WithTop ℤ) r f)
    (hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph s
      [{ length := f.natDegree, length_pos := PrPure.natDegree_pos hf,
         slope := prPureSlope r f.natDegree }]) :
    s = (r : ℚ) := by
  let data : NewtonPolygonData :=
    [{ length := f.natDegree, length_pos := PrPure.natDegree_pos hf,
       slope := prPureSlope r f.natDegree }]
  have hn : 0 < f.natDegree := PrPure.natDegree_pos hf
  have hr_le_s : (r : ℝ) ≤ (s : ℝ) := by
    have hstartPoly : ((0 : ℝ), (s : ℝ)) ∈ polygonEpigraph s data := by
      exact start_mem_polygonEpigraph s data
    have hstartNP : ((0 : ℝ), (s : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
      dsimp [data] at hstartPoly ⊢
      rw [hNP]
      exact hstartPoly
    rcases hstartNP with ⟨p, hp, hpx, hpy⟩
    have hpx0 : p.1 = 0 := by simpa using hpx
    let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ (q.1 = 0 → (r : ℝ) ≤ q.2)}
    have hWconv : Convex ℝ W := by
      intro x hx y hy a b ha hb hab
      constructor
      · change 0 ≤ a * x.1 + b * y.1
        exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      · intro hzero
        have hsumx : a * x.1 + b * y.1 = 0 := by simpa using hzero
        have hax : a * x.1 = 0 := by
          have hnonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
          have hby_nonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
          nlinarith
        have hby : b * y.1 = 0 := by
          have hnonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
          have hax_nonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
          nlinarith
        have hxlower : a * (r : ℝ) ≤ a * x.2 := by
          by_cases ha0 : a = 0
          · simp [ha0]
          · have hx0 : x.1 = 0 := by
              rcases mul_eq_zero.mp hax with ha_zero | hx_zero
              · exact (ha0 ha_zero).elim
              · exact hx_zero
            exact mul_le_mul_of_nonneg_left (hx.2 hx0) ha
        have hylower : b * (r : ℝ) ≤ b * y.2 := by
          by_cases hb0 : b = 0
          · simp [hb0]
          · have hy0 : y.1 = 0 := by
              rcases mul_eq_zero.mp hby with hb_zero | hy_zero
              · exact (hb0 hb_zero).elim
              · exact hy_zero
            exact mul_le_mul_of_nonneg_left (hy.2 hy0) hb
        have hsumlower :
            a * (r : ℝ) + b * (r : ℝ) ≤ a * x.2 + b * y.2 :=
          add_le_add hxlower hylower
        change (r : ℝ) ≤ a * x.2 + b * y.2
        calc
          (r : ℝ) = a * (r : ℝ) + b * (r : ℝ) := by rw [← add_mul, hab, one_mul]
          _ ≤ a * x.2 + b * y.2 := hsumlower
    have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
      intro q hq
      rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
      constructor
      · change (0 : ℝ) ≤ (i : ℝ)
        exact_mod_cast Nat.zero_le i
      · intro hx0
        have hx0' : (i : ℝ) = 0 := by simpa using hx0
        have hi0 : i = 0 := by exact_mod_cast hx0'
        subst i
        have hzeq : ((z : ℤ) : WithTop ℤ) = (((r : ℤ) : WithTop ℤ)) := by
          rw [← hz, PrPure.coeff_zero_valuation hf]
        have hzint : z = (r : ℤ) := WithTop.coe_eq_coe.mp hzeq
        rw [hzint]
        exact_mod_cast le_rfl
    have hpW : p ∈ W := convexHull_min hsub hWconv hp
    exact le_trans (hpW.2 hpx0) hpy
  have hs_le_r : (s : ℝ) ≤ (r : ℝ) := by
    have hconstNP : ((0 : ℝ), (r : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
      apply coefficientSupport_subset_newtonPolygon
      refine ⟨0, (r : ℤ), Nat.zero_le _, ?_, ?_, ?_⟩
      · rw [← AddValuation.ne_top_iff v]
        rw [PrPure.coeff_zero_valuation hf]
        simp
      · exact PrPure.coeff_zero_valuation hf
      · simp
    have hconstPoly : ((0 : ℝ), (r : ℝ)) ∈ polygonEpigraph s data := by
      dsimp [data]
      rw [← hNP]
      exact hconstNP
    rcases hconstPoly with ⟨p, hp, hpx, hpy⟩
    have hverts : verticesSet s data =
        {((0 : ℝ), (s : ℝ)), ((f.natDegree : ℝ), (s : ℝ) - (r : ℝ))} := by
      dsimp [data]
      ext x
      constructor
      · intro hx
        simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
        rcases hx with hx | hx
        · left
          exact hx
        · right
          rw [hx]
          ext <;> simp
          have hn0 : (f.natDegree : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          field_simp [hn0]
          ring
      · intro hx
        simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
        rcases hx with hx | hx
        · left
          exact hx
        · right
          rw [hx]
          ext <;> simp
          have hn0 : (f.natDegree : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          field_simp [hn0]
          ring
    rw [hverts] at hp
    rw [convexHull_pair] at hp
    rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
    have hp0 : p.1 = 0 := by simpa using hpx
    have hx : p.1 = b * (f.natDegree : ℝ) := by
      rw [← hpab]
      simp
    have hb0 : b = 0 := by
      have hnpos : (0 : ℝ) < (f.natDegree : ℝ) := by exact_mod_cast hn
      nlinarith
    have ha1 : a = 1 := by nlinarith
    have hy : p.2 = (s : ℝ) := by
      rw [← hpab, hb0, ha1]
      simp
    rw [← hy]
    exact hpy
  have hsR : (s : ℝ) = (r : ℝ) := le_antisymm hs_le_r hr_le_s
  exact_mod_cast hsR

example {r n i : ℕ} {z : ℤ} (hr : 0 < r) (hn : 1 < n)
    (hi1 : 1 ≤ i)
    (hline : (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (i : ℝ) ≤ (z : ℝ)) :
    (((r : ℤ) : WithTop ℤ)) < ((z : ℤ) : WithTop ℤ) + i • (((r : ℤ) : WithTop ℤ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hfactor : (0 : ℝ) < 1 - (1 : ℝ) / (n : ℝ) := by
    field_simp [ne_of_gt hn0]
    nlinarith [show (1 : ℝ) < n by exact_mod_cast hn]
  have hstrict : (r : ℝ) <
      (r : ℝ) - ((r : ℝ) / (n : ℝ)) * (i : ℝ) + (i : ℝ) * (r : ℝ) := by
    have hpos : (0 : ℝ) <
        (i : ℝ) * (r : ℝ) * (1 - (1 : ℝ) / (n : ℝ)) := by
      positivity
    field_simp [ne_of_gt hn0] at hpos ⊢
    nlinarith
  have hzR : (r : ℝ) < (z : ℝ) + (i : ℝ) * (r : ℝ) := by
    nlinarith
  have hzInt : (r : ℤ) < z + (i : ℤ) * (r : ℤ) := by
    exact_mod_cast hzR
  have hzTop : (((r : ℤ) : WithTop ℤ)) <
      ((z + (i : ℤ) * (r : ℤ) : ℤ) : WithTop ℤ) := by
    exact_mod_cast hzInt
  convert hzTop using 1

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]}
    (hr : 0 < r) (hdeg : 1 < f.natDegree)
    (hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph (r : ℚ)
      [{ length := f.natDegree, length_pos := Nat.zero_lt_of_lt hdeg,
         slope := prPureSlope r f.natDegree }]) :
    ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i) + i • (((r : ℤ) : WithTop ℤ)) := by
  intro i hi
  by_cases hcoeff : f.coeff i = 0
  · simp [hcoeff, AddValuation.map_zero]
  · have hvne : v (f.coeff i) ≠ (⊤ : WithTop ℤ) := by
      rw [AddValuation.ne_top_iff v]
      exact hcoeff
    rcases WithTop.ne_top_iff_exists.mp hvne with ⟨z, hz⟩
    have hi_le : i ≤ f.natDegree := by exact (Finset.mem_Icc.mp hi).2
    have hline : (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) ≤ (z : ℝ) := by
      have hpt : ((i : ℝ), (z : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
        exact coefficientSupport_subset_newtonPolygon (v : K → WithTop ℤ) f
          ⟨i, z, hi_le, hcoeff, hz.symm, rfl⟩
      rw [hNP] at hpt
      rcases hpt with ⟨p, hp, hpx, hpy⟩
      have hverts : verticesSet (r : ℚ)
          [{ length := f.natDegree, length_pos := Nat.zero_lt_of_lt hdeg,
             slope := prPureSlope r f.natDegree }] =
          {((0 : ℝ), (r : ℝ)), ((f.natDegree : ℝ), (0 : ℝ))} := by
        ext x
        constructor
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
            ext <;> simp
            have hn0 : (f.natDegree : ℝ) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
            field_simp [hn0]
            ring
        · intro hx
          simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            rw [hx]
            ext <;> simp
            have hn0 : (f.natDegree : ℝ) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
            field_simp [hn0]
            ring
      rw [hverts] at hp
      have hlinep : p.2 = (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * p.1 := by
        rw [convexHull_pair] at hp
        rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
        have hx : p.1 = b * (f.natDegree : ℝ) := by
          rw [← hpab]
          simp
        have hy : p.2 = a * (r : ℝ) := by
          rw [← hpab]
          simp
        rw [hy, hx]
        have hn0 : (f.natDegree : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
        field_simp [hn0]
        nlinarith [hab]
      have hpxi : p.1 = (i : ℝ) := by simpa using hpx
      have hpyz : p.2 ≤ (z : ℝ) := by simpa using hpy
      rw [← hpxi]
      rw [← hlinep]
      exact hpyz
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hn0 : (0 : ℝ) < (f.natDegree : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hdeg
    have hfactor : (0 : ℝ) < 1 - (1 : ℝ) / (f.natDegree : ℝ) := by
      field_simp [ne_of_gt hn0]
      nlinarith [show (1 : ℝ) < f.natDegree by exact_mod_cast hdeg]
    have hstrict : (r : ℝ) <
        (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) + (i : ℝ) * (r : ℝ) := by
      have hpos : (0 : ℝ) <
          (i : ℝ) * (r : ℝ) * (1 - (1 : ℝ) / (f.natDegree : ℝ)) := by
        positivity
      field_simp [ne_of_gt hn0] at hpos ⊢
      nlinarith
    have hzR : (r : ℝ) < (z : ℝ) + (i : ℝ) * (r : ℝ) := by
      nlinarith
    have hzInt : (r : ℤ) < z + (i : ℤ) * (r : ℤ) := by
      exact_mod_cast hzR
    have hzTop : (((r : ℤ) : WithTop ℤ)) <
        ((z + (i : ℤ) * (r : ℤ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast hzInt
    rw [← hz]
    convert hzTop using 1

example {data : NewtonPolygonData} {d : ℕ} (hd : 0 < d)
    (h : StrictlyIncreasingSlopes data) :
    StrictlyIncreasingSlopes
      (data.map fun seg : SegmentData =>
        { length := d * seg.length,
          length_pos := Nat.mul_pos hd seg.length_pos,
          slope := seg.slope / (d : ℚ) }) := by
  induction data with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b tail =>
          rcases h with ⟨hab, htail⟩
          constructor
          · exact div_lt_div_of_pos_right hab (by exact_mod_cast hd : (0 : ℚ) < d)
          · exact ih htail

example {data : NewtonPolygonData} {d : ℕ} (hd : 0 < d) :
    totalLength
      (data.map fun seg : SegmentData =>
        { length := d * seg.length,
          length_pos := Nat.mul_pos hd seg.length_pos,
          slope := seg.slope }) = d * totalLength data := by
  induction data with
  | nil => simp [totalLength]
  | cons seg rest ih =>
      simp [totalLength, ih, Nat.mul_add]

example {data : NewtonPolygonData} {d : ℕ} (hd : 0 < d)
    (h : StrictlyIncreasingSlopes data) :
    StrictlyIncreasingSlopes
      (data.map fun seg : SegmentData =>
        { length := seg.length * d,
          length_pos := Nat.mul_pos seg.length_pos hd,
          slope := seg.slope / (d : ℚ) }) := by
  induction data with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b tail =>
          rcases h with ⟨hab, htail⟩
          constructor
          · exact div_lt_div_of_pos_right hab (by exact_mod_cast hd : (0 : ℚ) < d)
          · exact ih htail

example {data : NewtonPolygonData} {d : ℕ} (hd : 0 < d) :
    totalLength
      (data.map fun seg : SegmentData =>
        { length := seg.length * d,
          length_pos := Nat.mul_pos seg.length_pos hd,
          slope := seg.slope }) = totalLength data * d := by
  induction data with
  | nil => simp [totalLength]
  | cons seg rest ih =>
      simp [totalLength, ih, Nat.add_mul]

example {K : Type*} [Field K] {ord : K → WithTop ℤ} {f g : K[X]}
    {data : NewtonPolygonData} (hNP : HasNewtonPolygonData ord f data)
    (hg : 0 < g.natDegree) :
    (f.comp g).natDegree =
      totalLength
        (data.map fun seg : SegmentData =>
          { length := seg.length * g.natDegree,
            length_pos := Nat.mul_pos seg.length_pos hg,
            slope := seg.slope / (g.natDegree : ℚ) }) := by
  have htotal : ∀ data : NewtonPolygonData,
      totalLength
        (data.map fun seg : SegmentData =>
          { length := seg.length * g.natDegree,
            length_pos := Nat.mul_pos seg.length_pos hg,
            slope := seg.slope / (g.natDegree : ℚ) }) = totalLength data * g.natDegree := by
    intro data
    induction data with
    | nil => simp [totalLength]
    | cons seg rest ih => simp [totalLength, ih, Nat.add_mul]
  rw [Polynomial.natDegree_comp]
  rw [HasNewtonPolygonData.natDegree_eq_totalLength hNP]
  rw [htotal data]

private theorem prPure_comp_leadingCoeff_zero
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) (hg : PrPure (v : K → WithTop ℤ) r g)
    (hgdeg : g.natDegree ≠ 0) :
    v (f.comp g).leadingCoeff = (((0 : ℤ) : WithTop ℤ)) := by
  rw [Polynomial.leadingCoeff_comp hgdeg]
  rw [AddValuation.map_mul, AddValuation.map_pow]
  rw [PrPure.leadingCoeff_valuation hf, PrPure.leadingCoeff_valuation hg]
  simp

example {K : Type*} [Field K] {ord : K → WithTop ℤ} {r : ℕ} {f g : K[X]}
    (hf : PrPure ord r f) (hg : PrPure ord r g) :
    0 < (f.comp g).natDegree := by
  rw [Polynomial.natDegree_comp]
  exact Nat.mul_pos (PrPure.natDegree_pos hf) (PrPure.natDegree_pos hg)

example {K : Type*} [CommSemiring K] {f g : K[X]} :
    (f.comp g).coeff 0 = f.eval (g.coeff 0) := by
  rw [coeff_zero_eq_eval_zero, eval_comp, coeff_zero_eq_eval_zero]

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f : K[X]} {c : K}
    (h0 : v (f.coeff 0) = (((r : ℤ) : WithTop ℤ)))
    (htail : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * c ^ i)) :
    v (f.eval c) = (((r : ℤ) : WithTop ℤ)) := by
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_range_succ']
  have hsum : (((r : ℤ) : WithTop ℤ)) <
      v (∑ k ∈ Finset.range f.natDegree, f.coeff (k + 1) * c ^ (k + 1)) := by
    apply AddValuation.map_lt_sum
    · simp
    · intro k hk
      exact htail (k + 1) (by simp [Finset.mem_range.mp hk])
  have hconst : v (f.coeff 0 * c ^ 0) = (((r : ℤ) : WithTop ℤ)) := by
    simpa using h0
  rw [AddValuation.map_add_eq_of_lt_right v]
  · exact hconst
  · rw [hconst]
    exact hsum

private theorem prPure_comp_coeff_zero_from_tail
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f)
    (htail : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.coeff 0) ^ i)) :
    v ((f.comp g).coeff 0) = (((r : ℤ) : WithTop ℤ)) := by
  rw [coeff_zero_eq_eval_zero, eval_comp]
  have htail' : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.eval 0) ^ i) := by
    intro i hi
    simpa [← coeff_zero_eq_eval_zero] using htail i hi
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_range_succ']
  have hsum : (((r : ℤ) : WithTop ℤ)) <
      v (∑ k ∈ Finset.range f.natDegree,
          f.coeff (k + 1) * (g.eval 0) ^ (k + 1)) := by
    apply AddValuation.map_lt_sum
    · simp
    · intro k hk
      exact htail' (k + 1) (by simp [Finset.mem_range.mp hk])
  have hconst : v (f.coeff 0 * (g.eval 0) ^ 0) = (((r : ℤ) : WithTop ℤ)) := by
    simpa using PrPure.coeff_zero_valuation hf
  rw [AddValuation.map_add_eq_of_lt_right v]
  · exact hconst
  · rw [hconst]
    exact hsum

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r i : ℕ} {f g : K[X]}
    (hg : PrPure (v : K → WithTop ℤ) r g) :
    v (f.coeff i * (g.coeff 0) ^ i) =
      v (f.coeff i) + i • (((r : ℤ) : WithTop ℤ)) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, PrPure.coeff_zero_valuation hg]

private theorem comp_const_tail_terms_from_shift
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hshift : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i) + i • (((r : ℤ) : WithTop ℤ))) :
    ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.coeff 0) ^ i) := by
  intro i hi
  rw [AddValuation.map_mul, AddValuation.map_pow, PrPure.coeff_zero_valuation hg]
  exact hshift i hi

private theorem prPure_from_comp_const_and_pure
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) (hg : PrPure (v : K → WithTop ℤ) r g)
    (hconst : v ((f.comp g).coeff 0) = (((r : ℤ) : WithTop ℤ)))
    (hpure : PureAt (v : K → WithTop ℤ) (f.comp g)
      (prPureSlope r (f.comp g).natDegree)) :
    PrPure (v : K → WithTop ℤ) r (f.comp g) := by
  refine ⟨PrPure.r_pos hf, ?_⟩
  refine ⟨?_, hconst, ?_, hpure⟩
  · rw [Polynomial.natDegree_comp]
    exact Nat.mul_pos (PrPure.natDegree_pos hf) (PrPure.natDegree_pos hg)
  · have hgdeg : g.natDegree ≠ 0 := Nat.ne_of_gt (PrPure.natDegree_pos hg)
    rw [Polynomial.leadingCoeff_comp hgdeg]
    rw [AddValuation.map_mul, AddValuation.map_pow]
    rw [PrPure.leadingCoeff_valuation hf, PrPure.leadingCoeff_valuation hg]
    simp

private theorem prPure_from_tail_and_pure
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) (hg : PrPure (v : K → WithTop ℤ) r g)
    (htail : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.coeff 0) ^ i))
    (hpure : PureAt (v : K → WithTop ℤ) (f.comp g)
      (prPureSlope r (f.comp g).natDegree)) :
    PrPure (v : K → WithTop ℤ) r (f.comp g) := by
  refine ⟨PrPure.r_pos hf, ?_⟩
  refine ⟨?_, ?_, ?_, hpure⟩
  · rw [Polynomial.natDegree_comp]
    exact Nat.mul_pos (PrPure.natDegree_pos hf) (PrPure.natDegree_pos hg)
  · rw [coeff_zero_eq_eval_zero, eval_comp]
    have htail' : ∀ i ∈ Finset.Icc 1 f.natDegree,
        (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.eval 0) ^ i) := by
      intro i hi
      simpa [← coeff_zero_eq_eval_zero] using htail i hi
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_range_succ']
    have hsum : (((r : ℤ) : WithTop ℤ)) <
        v (∑ k ∈ Finset.range f.natDegree,
            f.coeff (k + 1) * (g.eval 0) ^ (k + 1)) := by
      apply AddValuation.map_lt_sum
      · simp
      · intro k hk
        exact htail' (k + 1) (by simp [Finset.mem_range.mp hk])
    have hconst : v (f.coeff 0 * (g.eval 0) ^ 0) = (((r : ℤ) : WithTop ℤ)) := by
      simpa using PrPure.coeff_zero_valuation hf
    rw [AddValuation.map_add_eq_of_lt_right v]
    · exact hconst
    · rw [hconst]
      exact hsum
  · have hgdeg : g.natDegree ≠ 0 := Nat.ne_of_gt (PrPure.natDegree_pos hg)
    rw [Polynomial.leadingCoeff_comp hgdeg]
    rw [AddValuation.map_mul, AddValuation.map_pow]
    rw [PrPure.leadingCoeff_valuation hf, PrPure.leadingCoeff_valuation hg]
    simp

private theorem prPure_comp_coeff_zero_from_hNP
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) (hg : PrPure (v : K → WithTop ℤ) r g)
    (hdeg : 1 < f.natDegree)
    (hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph (r : ℚ)
      [{ length := f.natDegree, length_pos := Nat.zero_lt_of_lt hdeg,
         slope := prPureSlope r f.natDegree }]) :
    v ((f.comp g).coeff 0) = (((r : ℤ) : WithTop ℤ)) := by
  rw [coeff_zero_eq_eval_zero, eval_comp]
  have hr : 0 < r := PrPure.r_pos hf
  have hshift : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i) + i • (((r : ℤ) : WithTop ℤ)) := by
    intro i hi
    by_cases hcoeff : f.coeff i = 0
    · simp [hcoeff, AddValuation.map_zero]
    · have hvne : v (f.coeff i) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hcoeff
      rcases WithTop.ne_top_iff_exists.mp hvne with ⟨z, hz⟩
      have hi_le : i ≤ f.natDegree := by exact (Finset.mem_Icc.mp hi).2
      have hline : (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) ≤ (z : ℝ) := by
        have hpt : ((i : ℝ), (z : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
          exact coefficientSupport_subset_newtonPolygon (v : K → WithTop ℤ) f
            ⟨i, z, hi_le, hcoeff, hz.symm, rfl⟩
        rw [hNP] at hpt
        rcases hpt with ⟨p, hp, hpx, hpy⟩
        have hverts : verticesSet (r : ℚ)
            [{ length := f.natDegree, length_pos := Nat.zero_lt_of_lt hdeg,
               slope := prPureSlope r f.natDegree }] =
            {((0 : ℝ), (r : ℝ)), ((f.natDegree : ℝ), (0 : ℝ))} := by
          ext x
          constructor
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (f.natDegree : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
              field_simp [hn0]
              ring
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (f.natDegree : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
              field_simp [hn0]
              ring
        rw [hverts] at hp
        have hlinep : p.2 = (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * p.1 := by
          rw [convexHull_pair] at hp
          rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
          have hx : p.1 = b * (f.natDegree : ℝ) := by
            rw [← hpab]
            simp
          have hy : p.2 = a * (r : ℝ) := by
            rw [← hpab]
            simp
          rw [hy, hx]
          have hn0 : (f.natDegree : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
          field_simp [hn0]
          nlinarith [hab]
        have hpxi : p.1 = (i : ℝ) := by simpa using hpx
        have hpyz : p.2 ≤ (z : ℝ) := by simpa using hpy
        rw [← hpxi]
        rw [← hlinep]
        exact hpyz
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hn0 : (0 : ℝ) < (f.natDegree : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hdeg
      have hfactor : (0 : ℝ) < 1 - (1 : ℝ) / (f.natDegree : ℝ) := by
        field_simp [ne_of_gt hn0]
        nlinarith [show (1 : ℝ) < f.natDegree by exact_mod_cast hdeg]
      have hstrict : (r : ℝ) <
          (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) + (i : ℝ) * (r : ℝ) := by
        have hpos : (0 : ℝ) <
            (i : ℝ) * (r : ℝ) * (1 - (1 : ℝ) / (f.natDegree : ℝ)) := by
          positivity
        field_simp [ne_of_gt hn0] at hpos ⊢
        nlinarith
      have hzR : (r : ℝ) < (z : ℝ) + (i : ℝ) * (r : ℝ) := by
        nlinarith
      have hzInt : (r : ℤ) < z + (i : ℤ) * (r : ℤ) := by
        exact_mod_cast hzR
      have hzTop : (((r : ℤ) : WithTop ℤ)) <
          ((z + (i : ℤ) * (r : ℤ) : ℤ) : WithTop ℤ) := by
        exact_mod_cast hzInt
      rw [← hz]
      convert hzTop using 1
  have htail' : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.eval 0) ^ i) := by
    intro i hi
    rw [AddValuation.map_mul, AddValuation.map_pow]
    rw [← coeff_zero_eq_eval_zero, PrPure.coeff_zero_valuation hg]
    exact hshift i hi
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_range_succ']
  have hsum : (((r : ℤ) : WithTop ℤ)) <
      v (∑ k ∈ Finset.range f.natDegree,
          f.coeff (k + 1) * (g.eval 0) ^ (k + 1)) := by
    apply AddValuation.map_lt_sum
    · simp
    · intro k hk
      exact htail' (k + 1) (by simp [Finset.mem_range.mp hk])
  have hconst : v (f.coeff 0 * (g.eval 0) ^ 0) = (((r : ℤ) : WithTop ℤ)) := by
    simpa using PrPure.coeff_zero_valuation hf
  rw [AddValuation.map_add_eq_of_lt_right v]
  · exact hconst
  · rw [hconst]
    exact hsum

private theorem prPure_comp_coeff_zero_from_PrPure
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) (hg : PrPure (v : K → WithTop ℤ) r g)
    (hdeg : 1 < f.natDegree) :
    v ((f.comp g).coeff 0) = (((r : ℤ) : WithTop ℤ)) := by
  have hNP_r0 : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph (r : ℚ)
      [{ length := f.natDegree, length_pos := PrPure.natDegree_pos hf,
         slope := prPureSlope r f.natDegree }] := by
    let data : NewtonPolygonData :=
      [{ length := f.natDegree, length_pos := PrPure.natDegree_pos hf,
         slope := prPureSlope r f.natDegree }]
    have hdata : HasNewtonPolygonData (v : K → WithTop ℤ) f data := by
      dsimp [data]
      exact PureAt.hasNewtonPolygonData (PrPure.pureAt hf)
    rcases HasNewtonPolygonData.exists_startHeight hdata with ⟨s, hNP⟩
    have hn : 0 < f.natDegree := PrPure.natDegree_pos hf
    have hs_eq : s = (r : ℚ) := by
      have hr_le_s : (r : ℝ) ≤ (s : ℝ) := by
        have hstartPoly : ((0 : ℝ), (s : ℝ)) ∈ polygonEpigraph s data := by
          exact start_mem_polygonEpigraph s data
        have hstartNP : ((0 : ℝ), (s : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
          rw [hNP]
          exact hstartPoly
        rcases hstartNP with ⟨p, hp, hpx, hpy⟩
        have hpx0 : p.1 = 0 := by simpa using hpx
        let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ (q.1 = 0 → (r : ℝ) ≤ q.2)}
        have hWconv : Convex ℝ W := by
          intro x hx y hy a b ha hb hab
          constructor
          · change 0 ≤ a * x.1 + b * y.1
            exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
          · intro hzero
            have hsumx : a * x.1 + b * y.1 = 0 := by simpa using hzero
            have hax : a * x.1 = 0 := by
              have hnonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
              have hby_nonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
              nlinarith
            have hby : b * y.1 = 0 := by
              have hnonneg : 0 ≤ b * y.1 := mul_nonneg hb hy.1
              have hax_nonneg : 0 ≤ a * x.1 := mul_nonneg ha hx.1
              nlinarith
            have hxlower : a * (r : ℝ) ≤ a * x.2 := by
              by_cases ha0 : a = 0
              · simp [ha0]
              · have hx0 : x.1 = 0 := by
                  rcases mul_eq_zero.mp hax with ha_zero | hx_zero
                  · exact (ha0 ha_zero).elim
                  · exact hx_zero
                exact mul_le_mul_of_nonneg_left (hx.2 hx0) ha
            have hylower : b * (r : ℝ) ≤ b * y.2 := by
              by_cases hb0 : b = 0
              · simp [hb0]
              · have hy0 : y.1 = 0 := by
                  rcases mul_eq_zero.mp hby with hb_zero | hy_zero
                  · exact (hb0 hb_zero).elim
                  · exact hy_zero
                exact mul_le_mul_of_nonneg_left (hy.2 hy0) hb
            have hsumlower :
                a * (r : ℝ) + b * (r : ℝ) ≤ a * x.2 + b * y.2 :=
              add_le_add hxlower hylower
            change (r : ℝ) ≤ a * x.2 + b * y.2
            calc
              (r : ℝ) = a * (r : ℝ) + b * (r : ℝ) := by
                rw [← add_mul, hab, one_mul]
              _ ≤ a * x.2 + b * y.2 := hsumlower
        have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
          intro q hq
          rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
          constructor
          · change (0 : ℝ) ≤ (i : ℝ)
            exact_mod_cast Nat.zero_le i
          · intro hx0
            have hx0' : (i : ℝ) = 0 := by simpa using hx0
            have hi0 : i = 0 := by exact_mod_cast hx0'
            subst i
            have hzeq : ((z : ℤ) : WithTop ℤ) = (((r : ℤ) : WithTop ℤ)) := by
              rw [← hz, PrPure.coeff_zero_valuation hf]
            have hzint : z = (r : ℤ) := WithTop.coe_eq_coe.mp hzeq
            rw [hzint]
            exact_mod_cast le_rfl
        have hpW : p ∈ W := convexHull_min hsub hWconv hp
        exact le_trans (hpW.2 hpx0) hpy
      have hs_le_r : (s : ℝ) ≤ (r : ℝ) := by
        have hconstNP : ((0 : ℝ), (r : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
          apply coefficientSupport_subset_newtonPolygon
          refine ⟨0, (r : ℤ), Nat.zero_le _, ?_, ?_, ?_⟩
          · rw [← AddValuation.ne_top_iff v]
            rw [PrPure.coeff_zero_valuation hf]
            simp
          · exact PrPure.coeff_zero_valuation hf
          · simp
        have hconstPoly : ((0 : ℝ), (r : ℝ)) ∈ polygonEpigraph s data := by
          rw [← hNP]
          exact hconstNP
        rcases hconstPoly with ⟨p, hp, hpx, hpy⟩
        have hverts : verticesSet s data =
            {((0 : ℝ), (s : ℝ)), ((f.natDegree : ℝ), (s : ℝ) - (r : ℝ))} := by
          dsimp [data]
          ext x
          constructor
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (f.natDegree : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
              field_simp [hn0]
              ring
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (f.natDegree : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
              field_simp [hn0]
              ring
        rw [hverts] at hp
        rw [convexHull_pair] at hp
        rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
        have hp0 : p.1 = 0 := by simpa using hpx
        have hx : p.1 = b * (f.natDegree : ℝ) := by
          rw [← hpab]
          simp
        have hb0 : b = 0 := by
          have hnpos : (0 : ℝ) < (f.natDegree : ℝ) := by exact_mod_cast hn
          nlinarith
        have ha1 : a = 1 := by nlinarith
        have hy : p.2 = (s : ℝ) := by
          rw [← hpab, hb0, ha1]
          simp
        rw [← hy]
        exact hpy
      have hsR : (s : ℝ) = (r : ℝ) := le_antisymm hs_le_r hr_le_s
      exact_mod_cast hsR
    subst s
    exact hNP
  have hNP : newtonPolygon (v : K → WithTop ℤ) f = polygonEpigraph (r : ℚ)
      [{ length := f.natDegree, length_pos := Nat.zero_lt_of_lt hdeg,
         slope := prPureSlope r f.natDegree }] := by
    simpa using hNP_r0
  rw [coeff_zero_eq_eval_zero, eval_comp]
  have hr : 0 < r := PrPure.r_pos hf
  have hshift : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i) + i • (((r : ℤ) : WithTop ℤ)) := by
    intro i hi
    by_cases hcoeff : f.coeff i = 0
    · simp [hcoeff, AddValuation.map_zero]
    · have hvne : v (f.coeff i) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hcoeff
      rcases WithTop.ne_top_iff_exists.mp hvne with ⟨z, hz⟩
      have hi_le : i ≤ f.natDegree := by exact (Finset.mem_Icc.mp hi).2
      have hline :
          (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) ≤ (z : ℝ) := by
        have hpt : ((i : ℝ), (z : ℝ)) ∈ newtonPolygon (v : K → WithTop ℤ) f := by
          exact coefficientSupport_subset_newtonPolygon (v : K → WithTop ℤ) f
            ⟨i, z, hi_le, hcoeff, hz.symm, rfl⟩
        rw [hNP] at hpt
        rcases hpt with ⟨p, hp, hpx, hpy⟩
        have hverts : verticesSet (r : ℚ)
            [{ length := f.natDegree, length_pos := Nat.zero_lt_of_lt hdeg,
               slope := prPureSlope r f.natDegree }] =
            {((0 : ℝ), (r : ℝ)), ((f.natDegree : ℝ), (0 : ℝ))} := by
          ext x
          constructor
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (f.natDegree : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
              field_simp [hn0]
              ring
          · intro hx
            simp [verticesSet, verticesFrom, SegmentData.nextVertex, prPureSlope] at hx ⊢
            rcases hx with hx | hx
            · left
              exact hx
            · right
              rw [hx]
              ext <;> simp
              have hn0 : (f.natDegree : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
              field_simp [hn0]
              ring
        rw [hverts] at hp
        have hlinep : p.2 = (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * p.1 := by
          rw [convexHull_pair] at hp
          rcases hp with ⟨a, b, ha, hb, hab, hpab⟩
          have hx : p.1 = b * (f.natDegree : ℝ) := by
            rw [← hpab]
            simp
          have hy : p.2 = a * (r : ℝ) := by
            rw [← hpab]
            simp
          rw [hy, hx]
          have hn0 : (f.natDegree : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hdeg)
          field_simp [hn0]
          nlinarith [hab]
        have hpxi : p.1 = (i : ℝ) := by simpa using hpx
        have hpyz : p.2 ≤ (z : ℝ) := by simpa using hpy
        rw [← hpxi]
        rw [← hlinep]
        exact hpyz
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hn0 : (0 : ℝ) < (f.natDegree : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hdeg
      have hfactor : (0 : ℝ) < 1 - (1 : ℝ) / (f.natDegree : ℝ) := by
        field_simp [ne_of_gt hn0]
        nlinarith [show (1 : ℝ) < f.natDegree by exact_mod_cast hdeg]
      have hstrict : (r : ℝ) <
          (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) + (i : ℝ) * (r : ℝ) := by
        have hpos : (0 : ℝ) <
            (i : ℝ) * (r : ℝ) * (1 - (1 : ℝ) / (f.natDegree : ℝ)) := by
          positivity
        field_simp [ne_of_gt hn0] at hpos ⊢
        nlinarith
      have hzR : (r : ℝ) < (z : ℝ) + (i : ℝ) * (r : ℝ) := by
        nlinarith
      have hzInt : (r : ℤ) < z + (i : ℤ) * (r : ℤ) := by
        exact_mod_cast hzR
      have hzTop : (((r : ℤ) : WithTop ℤ)) <
          ((z + (i : ℤ) * (r : ℤ) : ℤ) : WithTop ℤ) := by
        exact_mod_cast hzInt
      rw [← hz]
      convert hzTop using 1
  have htail' : ∀ i ∈ Finset.Icc 1 f.natDegree,
      (((r : ℤ) : WithTop ℤ)) < v (f.coeff i * (g.eval 0) ^ i) := by
    intro i hi
    rw [AddValuation.map_mul, AddValuation.map_pow]
    rw [← coeff_zero_eq_eval_zero, PrPure.coeff_zero_valuation hg]
    exact hshift i hi
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_range_succ']
  have hsum : (((r : ℤ) : WithTop ℤ)) <
      v (∑ k ∈ Finset.range f.natDegree,
          f.coeff (k + 1) * (g.eval 0) ^ (k + 1)) := by
    apply AddValuation.map_lt_sum
    · simp
    · intro k hk
      exact htail' (k + 1) (by simp [Finset.mem_range.mp hk])
  have hconst : v (f.coeff 0 * (g.eval 0) ^ 0) = (((r : ℤ) : WithTop ℤ)) := by
    simpa using PrPure.coeff_zero_valuation hf
  rw [AddValuation.map_add_eq_of_lt_right v]
  · exact hconst
  · rw [hconst]
    exact hsum

example {K : Type*} [Field K] {f g : K[X]} {k : ℕ} :
    (f.comp g).coeff k =
      ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (g ^ i).coeff k := by
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
  simp [Polynomial.coeff_C_mul]

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {f g : K[X]} {k : ℕ}
    {M : WithTop ℤ}
    (hterms : ∀ i ∈ Finset.range (f.natDegree + 1),
      M ≤ v (f.coeff i * (g ^ i).coeff k)) :
    M ≤ v ((f.comp g).coeff k) := by
  rw [show (f.comp g).coeff k =
      ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (g ^ i).coeff k by
    rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
    simp [Polynomial.coeff_C_mul]]
  exact AddValuation.map_le_sum v hterms

example {r e : ℕ} (hr : 0 < r) (he : 1 < e) :
    (0 : ℚ) < (r : ℚ) + prPureSlope r e := by
  dsimp [prPureSlope]
  have hepos : (0 : ℚ) < (e : ℚ) := by exact_mod_cast (Nat.zero_lt_of_lt he)
  have heone : (1 : ℚ) < (e : ℚ) := by exact_mod_cast he
  have hnum : (0 : ℚ) < (r : ℚ) * ((e : ℚ) - 1) := by
    exact mul_pos (by exact_mod_cast hr) (sub_pos.mpr heone)
  have hdiv : (0 : ℚ) < ((r : ℚ) * ((e : ℚ) - 1)) / (e : ℚ) :=
    div_pos hnum hepos
  convert hdiv using 1
  field_simp [ne_of_gt hepos]
  ring

example {K : Type*} [Semiring K] {ord : K → WithTop ℤ} {r : ℕ} {f : K[X]}
    (h : PrPure ord r f) (hdeg : 1 < f.natDegree) :
    (0 : ℚ) < (r : ℚ) + prPureSlope r f.natDegree := by
  dsimp [prPureSlope]
  have hepos : (0 : ℚ) < (f.natDegree : ℚ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hdeg)
  have heone : (1 : ℚ) < (f.natDegree : ℚ) := by exact_mod_cast hdeg
  have hnum : (0 : ℚ) < (r : ℚ) * ((f.natDegree : ℚ) - 1) := by
    exact mul_pos (by exact_mod_cast PrPure.r_pos h) (sub_pos.mpr heone)
  have hdiv : (0 : ℚ) <
      ((r : ℚ) * ((f.natDegree : ℚ) - 1)) / (f.natDegree : ℚ) :=
    div_pos hnum hepos
  convert hdiv using 1
  field_simp [ne_of_gt hepos]
  ring

example {K : Type*} [Field K] {k : ℕ} {g : K[X]} :
    (g ^ k).natDegree = k * g.natDegree := by
  exact Polynomial.natDegree_pow g k

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r k : ℕ} {g : K[X]}
    (hg : PrPure (v : K → WithTop ℤ) r g) :
    v ((g ^ k).coeff 0) = k • (((r : ℤ) : WithTop ℤ)) := by
  rw [coeff_zero_eq_eval_zero]
  rw [Polynomial.eval_pow]
  rw [← coeff_zero_eq_eval_zero]
  rw [AddValuation.map_pow]
  rw [PrPure.coeff_zero_valuation hg]

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r k : ℕ} {g : K[X]}
    (hg : PrPure (v : K → WithTop ℤ) r g) :
    v (g ^ k).leadingCoeff = (((0 : ℤ) : WithTop ℤ)) := by
  rw [Polynomial.leadingCoeff_pow]
  rw [AddValuation.map_pow]
  rw [PrPure.leadingCoeff_valuation hg]
  simp

private theorem prPure_power_coeff_line_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r d : ℕ} {g : K[X]}
    (hdeg : g.natDegree = d)
    (hgline : ∀ (j : ℕ) (z : ℤ), j ≤ d → g.coeff j ≠ 0 →
      v (g.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (j : ℝ) ≤ (z : ℝ)) :
    ∀ (i k : ℕ) (z : ℤ), (g ^ i).coeff k ≠ 0 →
      v ((g ^ i).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤ (z : ℝ) := by
  intro i
  induction i with
  | zero =>
      intro k z hcoeff hval
      have hk : k = 0 := by
        by_contra hk
        have hzero : (g ^ 0).coeff k = 0 := by
          rw [pow_zero, Polynomial.coeff_one]
          simp [hk]
        exact hcoeff hzero
      subst k
      have hzTop : (((0 : ℤ) : WithTop ℤ)) = ((z : ℤ) : WithTop ℤ) := by
        rw [← hval]
        simp
      have hzInt : (0 : ℤ) = z := WithTop.coe_eq_coe.mp hzTop
      rw [← hzInt]
      simp
  | succ i ih =>
      intro k z hcoeff hval
      by_contra hnot
      have hzlt : (z : ℝ) < ((i + 1 : ℕ) : ℝ) * (r : ℝ) -
          ((r : ℝ) / (d : ℝ)) * (k : ℝ) := lt_of_not_ge hnot
      have hcoeff_sum : (g ^ (i + 1)).coeff k =
          ∑ x ∈ Finset.antidiagonal k, g.coeff x.1 * (g ^ i).coeff x.2 := by
        rw [pow_succ']
        exact Polynomial.coeff_mul g (g ^ i) k
      have hterms : ∀ x ∈ Finset.antidiagonal k,
          ((z : ℤ) : WithTop ℤ) < v (g.coeff x.1 * (g ^ i).coeff x.2) := by
        intro x hx
        by_cases hterm : g.coeff x.1 * (g ^ i).coeff x.2 = 0
        · rw [hterm, AddValuation.map_zero]
          exact WithTop.coe_lt_top z
        · have hgcoeff : g.coeff x.1 ≠ 0 := by
            intro hzero
            exact hterm (by simp [hzero])
          have hpcoeff : (g ^ i).coeff x.2 ≠ 0 := by
            intro hzero
            exact hterm (by simp [hzero])
          have hvgne : v (g.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
            rw [AddValuation.ne_top_iff v]
            exact hgcoeff
          have hvpne : v ((g ^ i).coeff x.2) ≠ (⊤ : WithTop ℤ) := by
            rw [AddValuation.ne_top_iff v]
            exact hpcoeff
          rcases WithTop.ne_top_iff_exists.mp hvgne with ⟨zg, hzg⟩
          rcases WithTop.ne_top_iff_exists.mp hvpne with ⟨zp, hzp⟩
          have hgle : x.1 ≤ d := by
            have hle := Polynomial.le_natDegree_of_ne_zero (p := g) hgcoeff
            simpa [hdeg] using hle
          have hgLower : (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (x.1 : ℝ) ≤
              (zg : ℝ) :=
            hgline x.1 zg hgle hgcoeff hzg.symm
          have hpLower : (i : ℝ) * (r : ℝ) -
              ((r : ℝ) / (d : ℝ)) * (x.2 : ℝ) ≤ (zp : ℝ) :=
            ih x.2 zp hpcoeff hzp.symm
          have hxsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
          have hxsumR : (x.1 : ℝ) + (x.2 : ℝ) = (k : ℝ) := by
            exact_mod_cast hxsum
          have htarget : ((i + 1 : ℕ) : ℝ) * (r : ℝ) -
              ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤ (zg : ℝ) + (zp : ℝ) := by
            have hsumLower := add_le_add hgLower hpLower
            have hrewrite :
                (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (x.1 : ℝ) +
                    ((i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (x.2 : ℝ)) =
                  ((i + 1 : ℕ) : ℝ) * (r : ℝ) -
                    ((r : ℝ) / (d : ℝ)) * (k : ℝ) := by
              rw [← hxsumR]
              have hi : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
              rw [hi]
              ring
            rwa [hrewrite] at hsumLower
          have hzsumR : (z : ℝ) < (zg : ℝ) + (zp : ℝ) :=
            lt_of_lt_of_le hzlt htarget
          have hzsumInt : z < zg + zp := by exact_mod_cast hzsumR
          have hzTop : ((z : ℤ) : WithTop ℤ) < (((zg + zp : ℤ)) : WithTop ℤ) := by
            exact_mod_cast hzsumInt
          rw [AddValuation.map_mul]
          rw [← hzg, ← hzp]
          convert hzTop using 1
      have hsumstrict : ((z : ℤ) : WithTop ℤ) <
          v (∑ x ∈ Finset.antidiagonal k, g.coeff x.1 * (g ^ i).coeff x.2) := by
        apply AddValuation.map_lt_sum
        · simp
        · exact hterms
      rw [← hcoeff_sum, hval] at hsumstrict
      exact (lt_irrefl (((z : ℤ) : WithTop ℤ))) hsumstrict

private theorem prPure_pow_pureAt
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r k : ℕ} {g : K[X]}
    (hg : PrPure (v : K → WithTop ℤ) r g) (hk : 0 < k) :
    PureAt (v : K → WithTop ℤ) (g ^ k) (prPureSlope r g.natDegree) := by
  let d := g.natDegree
  have hd : 0 < d := PrPure.natDegree_pos hg
  have hpowPos : 0 < k * d := Nat.mul_pos hk hd
  have hpowDeg : (g ^ k).natDegree = k * d := by
    simp [d, Polynomial.natDegree_pow]
  have hdata : HasNewtonPolygonData (v : K → WithTop ℤ) g
      [{ length := d, length_pos := hd, slope := prPureSlope r d }] := by
    simpa [d] using PureAt.hasNewtonPolygonData (PrPure.pureAt hg)
  rcases HasNewtonPolygonData.exists_startHeight hdata with ⟨sg, hNPg⟩
  have hsg : sg = (r : ℚ) := by
    have hNPg' : newtonPolygon (v : K → WithTop ℤ) g = polygonEpigraph sg
        [{ length := g.natDegree, length_pos := PrPure.natDegree_pos hg,
           slope := prPureSlope r g.natDegree }] := by
      simpa [d] using hNPg
    exact prPure_startHeight_eq hg hNPg'
  subst sg
  have hgLine : ∀ (j : ℕ) (z : ℤ), j ≤ d → g.coeff j ≠ 0 →
      v (g.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (j : ℝ) ≤ (z : ℝ) := by
    intro j z hj hcoeff hz
    exact oneSegment_line_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (r := r) (n := d) (i := j)
      (z := z) (f := g) hd hNPg (by simpa [d] using hj) hcoeff hz
  have hnsmul_const_all :
      ∀ t : ℕ, t • (((r : ℤ) : WithTop ℤ)) =
        ((((t : ℤ) * (r : ℤ) : ℤ)) : WithTop ℤ) := by
    intro t
    induction t with
    | zero =>
        simp
    | succ t ih =>
        rw [succ_nsmul, ih]
        change (((t : ℤ) * (r : ℤ) + (r : ℤ) : ℤ) : WithTop ℤ) =
          ((((Nat.succ t : ℤ) * (r : ℤ) : ℤ)) : WithTop ℤ)
        congr 1
        norm_num
        ring
  have hnsmul_const :
      k • (((r : ℤ) : WithTop ℤ)) =
        ((((k : ℤ) * (r : ℤ) : ℤ)) : WithTop ℤ) :=
    hnsmul_const_all k
  have hconst : v ((g ^ k).coeff 0) =
      ((((k : ℤ) * (r : ℤ) : ℤ)) : WithTop ℤ) := by
    rw [coeff_zero_eq_eval_zero]
    rw [Polynomial.eval_pow]
    rw [← coeff_zero_eq_eval_zero]
    rw [AddValuation.map_pow]
    rw [PrPure.coeff_zero_valuation hg]
    exact hnsmul_const
  have hlead : v (g ^ k).leadingCoeff = (((0 : ℤ) : WithTop ℤ)) := by
    rw [Polynomial.leadingCoeff_pow]
    rw [AddValuation.map_pow]
    rw [PrPure.leadingCoeff_valuation hg]
    simp
  have hstart :
      (k : ℚ) * (r : ℚ) = ((((k : ℤ) * (r : ℤ) : ℤ)) : ℚ) := by
    norm_num
  have hend : (k : ℚ) * (r : ℚ) + (k * d : ℕ) * prPureSlope r d = (0 : ℚ) := by
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    simp [prPureSlope]
    field_simp [hdQ]
    ring
  have hcoeffLower : ∀ i z, i ≤ k * d → (g ^ k).coeff i ≠ 0 →
      v ((g ^ k).coeff i) = ((z : ℤ) : WithTop ℤ) →
      ((k : ℚ) * (r : ℚ) : ℚ) + (prPureSlope r d : ℚ) * (i : ℚ) ≤ (z : ℝ) := by
    intro i z _ hcoeff hz
    have hraw := prPure_power_coeff_line_lower
      (v := v) (r := r) (d := d) (g := g) rfl hgLine k i z hcoeff hz
    have hrewrite :
        (((k : ℚ) * (r : ℚ) : ℚ) + (prPureSlope r d : ℚ) * (i : ℚ) : ℚ) =
          ((k : ℚ) * (r : ℚ) - ((r : ℚ) / (d : ℚ)) * (i : ℚ) : ℚ) := by
      simp [prPureSlope]
      ring
    have hrewriteR :
        (((k : ℚ) * (r : ℚ) : ℚ) + (prPureSlope r d : ℚ) * (i : ℚ) : ℝ) =
          (k : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (i : ℝ) := by
      simp [prPureSlope]
      ring
    rw [hrewriteR]
    exact hraw
  have hnp : HasNewtonPolygonData (v : K → WithTop ℤ) (g ^ k)
      [{ length := k * d, length_pos := hpowPos, slope := prPureSlope r d }] := by
    exact oneSegment_of_endpoint_and_affine_lower
      (v := v) (start := (k : ℚ) * (r : ℚ)) (slope := prPureSlope r d)
      (n := k * d) (f := g ^ k)
      (z0 := (k : ℤ) * (r : ℤ)) (zN := 0)
      hpowPos hpowDeg hconst hlead hstart hend hcoeffLower
  refine ⟨by simpa [hpowDeg] using hpowPos, ?_⟩
  simpa [d, hpowDeg] using hnp

private theorem comp_coeff_line_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r e d : ℕ}
    {f g : K[X]}
    (he : 0 < e) (hd : 0 < d)
    (hfdeg : f.natDegree = e) (hgdeg : g.natDegree = d)
    (hfline : ∀ (i : ℕ) (z : ℤ), i ≤ e → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (e : ℝ)) * (i : ℝ) ≤ (z : ℝ))
    (hgline : ∀ (j : ℕ) (z : ℤ), j ≤ d → g.coeff j ≠ 0 →
      v (g.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (j : ℝ) ≤ (z : ℝ)) :
    ∀ (k : ℕ) (z : ℤ), k ≤ e * d → (f.comp g).coeff k ≠ 0 →
      v ((f.comp g).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / ((e * d : ℕ) : ℝ)) * (k : ℝ) ≤ (z : ℝ) := by
  have hpowLine : ∀ (i k : ℕ) (z : ℤ), (g ^ i).coeff k ≠ 0 →
      v ((g ^ i).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤ (z : ℝ) := by
    intro i
    induction i with
    | zero =>
        intro k z hcoeff hval
        have hk : k = 0 := by
          by_contra hk
          have hzero : (g ^ 0).coeff k = 0 := by
            rw [pow_zero, Polynomial.coeff_one]
            simp [hk]
          exact hcoeff hzero
        subst k
        have hzTop : (((0 : ℤ) : WithTop ℤ)) = ((z : ℤ) : WithTop ℤ) := by
          rw [← hval]
          simp
        have hzInt : (0 : ℤ) = z := WithTop.coe_eq_coe.mp hzTop
        rw [← hzInt]
        simp
    | succ i ih =>
        intro k z hcoeff hval
        by_contra hnot
        have hzlt : (z : ℝ) < ((i + 1 : ℕ) : ℝ) * (r : ℝ) -
            ((r : ℝ) / (d : ℝ)) * (k : ℝ) := lt_of_not_ge hnot
        have hcoeff_sum : (g ^ (i + 1)).coeff k =
            ∑ x ∈ Finset.antidiagonal k, g.coeff x.1 * (g ^ i).coeff x.2 := by
          rw [pow_succ']
          exact Polynomial.coeff_mul g (g ^ i) k
        have hterms : ∀ x ∈ Finset.antidiagonal k,
            ((z : ℤ) : WithTop ℤ) < v (g.coeff x.1 * (g ^ i).coeff x.2) := by
          intro x hx
          by_cases hterm : g.coeff x.1 * (g ^ i).coeff x.2 = 0
          · rw [hterm, AddValuation.map_zero]
            exact WithTop.coe_lt_top z
          · have hgcoeff : g.coeff x.1 ≠ 0 := by
              intro hzero
              exact hterm (by simp [hzero])
            have hpcoeff : (g ^ i).coeff x.2 ≠ 0 := by
              intro hzero
              exact hterm (by simp [hzero])
            have hvgne : v (g.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
              rw [AddValuation.ne_top_iff v]
              exact hgcoeff
            have hvpne : v ((g ^ i).coeff x.2) ≠ (⊤ : WithTop ℤ) := by
              rw [AddValuation.ne_top_iff v]
              exact hpcoeff
            rcases WithTop.ne_top_iff_exists.mp hvgne with ⟨zg, hzg⟩
            rcases WithTop.ne_top_iff_exists.mp hvpne with ⟨zp, hzp⟩
            have hgle : x.1 ≤ d := by
              have hle := Polynomial.le_natDegree_of_ne_zero (p := g) hgcoeff
              simpa [hgdeg] using hle
            have hgLower : (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (x.1 : ℝ) ≤
                (zg : ℝ) :=
              hgline x.1 zg hgle hgcoeff hzg.symm
            have hpLower : (i : ℝ) * (r : ℝ) -
                ((r : ℝ) / (d : ℝ)) * (x.2 : ℝ) ≤ (zp : ℝ) :=
              ih x.2 zp hpcoeff hzp.symm
            have hxsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
            have hxsumR : (x.1 : ℝ) + (x.2 : ℝ) = (k : ℝ) := by
              exact_mod_cast hxsum
            have htarget : ((i + 1 : ℕ) : ℝ) * (r : ℝ) -
                ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤ (zg : ℝ) + (zp : ℝ) := by
              have hsumLower := add_le_add hgLower hpLower
              have hrewrite :
                  (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (x.1 : ℝ) +
                      ((i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (x.2 : ℝ)) =
                    ((i + 1 : ℕ) : ℝ) * (r : ℝ) -
                      ((r : ℝ) / (d : ℝ)) * (k : ℝ) := by
                rw [← hxsumR]
                have hi : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
                rw [hi]
                ring
              rwa [hrewrite] at hsumLower
            have hzsumR : (z : ℝ) < (zg : ℝ) + (zp : ℝ) :=
              lt_of_lt_of_le hzlt htarget
            have hzsumInt : z < zg + zp := by exact_mod_cast hzsumR
            have hzTop : ((z : ℤ) : WithTop ℤ) < (((zg + zp : ℤ)) : WithTop ℤ) := by
              exact_mod_cast hzsumInt
            rw [AddValuation.map_mul]
            rw [← hzg, ← hzp]
            convert hzTop using 1
        have hsumstrict : ((z : ℤ) : WithTop ℤ) <
            v (∑ x ∈ Finset.antidiagonal k, g.coeff x.1 * (g ^ i).coeff x.2) := by
          apply AddValuation.map_lt_sum
          · simp
          · exact hterms
        rw [← hcoeff_sum, hval] at hsumstrict
        exact (lt_irrefl (((z : ℤ) : WithTop ℤ))) hsumstrict
  intro k z hk hcoeff hval
  by_contra hnot
  have hzlt : (z : ℝ) < (r : ℝ) - ((r : ℝ) / ((e * d : ℕ) : ℝ)) * (k : ℝ) :=
    lt_of_not_ge hnot
  have hcoeff_sum : (f.comp g).coeff k =
      ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (g ^ i).coeff k := by
    rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
    simp [Polynomial.coeff_C_mul]
  have hterms : ∀ i ∈ Finset.range (f.natDegree + 1),
      ((z : ℤ) : WithTop ℤ) < v (f.coeff i * (g ^ i).coeff k) := by
    intro i hi
    by_cases hterm : f.coeff i * (g ^ i).coeff k = 0
    · rw [hterm, AddValuation.map_zero]
      exact WithTop.coe_lt_top z
    · have hfcoeff : f.coeff i ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hpcoeff : (g ^ i).coeff k ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hvfne : v (f.coeff i) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hfcoeff
      have hvpne : v ((g ^ i).coeff k) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hpcoeff
      rcases WithTop.ne_top_iff_exists.mp hvfne with ⟨zf, hzf⟩
      rcases WithTop.ne_top_iff_exists.mp hvpne with ⟨zp, hzp⟩
      have hile : i ≤ e := by
        have hilt : i < f.natDegree + 1 := Finset.mem_range.mp hi
        have hile' : i ≤ f.natDegree := Nat.lt_succ_iff.mp hilt
        simpa [hfdeg] using hile'
      have hfLower : (r : ℝ) - ((r : ℝ) / (e : ℝ)) * (i : ℝ) ≤ (zf : ℝ) :=
        hfline i zf hile hfcoeff hzf.symm
      have hpLower : (i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤
          (zp : ℝ) :=
        hpowLine i k zp hpcoeff hzp.symm
      have hkle : k ≤ i * d := by
        have hle := Polynomial.le_natDegree_of_ne_zero (p := g ^ i) hpcoeff
        simpa [Polynomial.natDegree_pow, hgdeg] using hle
      have htarget : (r : ℝ) - ((r : ℝ) / ((e * d : ℕ) : ℝ)) * (k : ℝ) ≤
          (zf : ℝ) + (zp : ℝ) := by
        have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have hkR : (k : ℝ) ≤ (i : ℝ) * (d : ℝ) := by exact_mod_cast hkle
        have hsum := add_le_add hfLower hpLower
        have hrNonneg : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
        have heSubNonneg : (0 : ℝ) ≤ (e : ℝ) - 1 := by
          have he1 : (1 : ℕ) ≤ e := Nat.succ_le_of_lt he
          exact sub_nonneg.mpr (by exact_mod_cast he1)
        have hkdiff : (0 : ℝ) ≤ (i : ℝ) * (d : ℝ) - (k : ℝ) :=
          sub_nonneg.mpr hkR
        have hnonneg : (0 : ℝ) ≤
            (r : ℝ) * ((e : ℝ) - 1) * ((i : ℝ) * (d : ℝ) - (k : ℝ)) :=
          mul_nonneg (mul_nonneg hrNonneg heSubNonneg) hkdiff
        have hedR : ((e * d : ℕ) : ℝ) = (e : ℝ) * (d : ℝ) := by norm_num
        rw [hedR]
        field_simp [ne_of_gt heR, ne_of_gt hdR] at hsum ⊢
        nlinarith
      have hzsumR : (z : ℝ) < (zf : ℝ) + (zp : ℝ) := lt_of_lt_of_le hzlt htarget
      have hzsumInt : z < zf + zp := by exact_mod_cast hzsumR
      have hzTop : ((z : ℤ) : WithTop ℤ) < (((zf + zp : ℤ)) : WithTop ℤ) := by
        exact_mod_cast hzsumInt
      rw [AddValuation.map_mul]
      rw [← hzf, ← hzp]
      convert hzTop using 1
  have hsumstrict : ((z : ℤ) : WithTop ℤ) <
      v (∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (g ^ i).coeff k) := by
    apply AddValuation.map_lt_sum
    · simp
    · exact hterms
  rw [← hcoeff_sum, hval] at hsumstrict
  exact (lt_irrefl (((z : ℤ) : WithTop ℤ))) hsumstrict

private theorem comp_coeff_affine_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {start slope : ℚ} {r d : ℕ} {f g : K[X]}
    (hd : 0 < d) (hgdeg : g.natDegree = d)
    (hpos : (0 : ℝ) < (r : ℝ) + (slope : ℝ))
    (hfline : ∀ (i : ℕ) (z : ℤ), i ≤ f.natDegree → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (start : ℝ) + (slope : ℝ) * (i : ℝ) ≤ (z : ℝ))
    (hgline : ∀ (j : ℕ) (z : ℤ), j ≤ d → g.coeff j ≠ 0 →
      v (g.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (j : ℝ) ≤ (z : ℝ)) :
    ∀ (k : ℕ) (z : ℤ), (f.comp g).coeff k ≠ 0 →
      v ((f.comp g).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (start : ℝ) + ((slope : ℝ) / (d : ℝ)) * (k : ℝ) ≤ (z : ℝ) := by
  have hpowLine : ∀ (i k : ℕ) (z : ℤ), (g ^ i).coeff k ≠ 0 →
      v ((g ^ i).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤ (z : ℝ) :=
    prPure_power_coeff_line_lower (v := v) (r := r) (d := d) (g := g) hgdeg hgline
  intro k z hcoeff hval
  by_contra hnot
  have hzlt : (z : ℝ) <
      (start : ℝ) + ((slope : ℝ) / (d : ℝ)) * (k : ℝ) := lt_of_not_ge hnot
  have hcoeff_sum : (f.comp g).coeff k =
      ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (g ^ i).coeff k := by
    rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
    simp [Polynomial.coeff_C_mul]
  have hterms : ∀ i ∈ Finset.range (f.natDegree + 1),
      ((z : ℤ) : WithTop ℤ) < v (f.coeff i * (g ^ i).coeff k) := by
    intro i hi
    by_cases hterm : f.coeff i * (g ^ i).coeff k = 0
    · rw [hterm, AddValuation.map_zero]
      exact WithTop.coe_lt_top z
    · have hfcoeff : f.coeff i ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hpcoeff : (g ^ i).coeff k ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hvfne : v (f.coeff i) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hfcoeff
      have hvpne : v ((g ^ i).coeff k) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hpcoeff
      rcases WithTop.ne_top_iff_exists.mp hvfne with ⟨zf, hzf⟩
      rcases WithTop.ne_top_iff_exists.mp hvpne with ⟨zp, hzp⟩
      have hile : i ≤ f.natDegree := by
        have hilt : i < f.natDegree + 1 := Finset.mem_range.mp hi
        exact Nat.lt_succ_iff.mp hilt
      have hfLower : (start : ℝ) + (slope : ℝ) * (i : ℝ) ≤ (zf : ℝ) :=
        hfline i zf hile hfcoeff hzf.symm
      have hpLower : (i : ℝ) * (r : ℝ) - ((r : ℝ) / (d : ℝ)) * (k : ℝ) ≤
          (zp : ℝ) :=
        hpowLine i k zp hpcoeff hzp.symm
      have hkle : k ≤ i * d := by
        have hle := Polynomial.le_natDegree_of_ne_zero (p := g ^ i) hpcoeff
        simpa [Polynomial.natDegree_pow, hgdeg] using hle
      have htarget :
          (start : ℝ) + ((slope : ℝ) / (d : ℝ)) * (k : ℝ) ≤
            (zf : ℝ) + (zp : ℝ) := by
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have hkR : (k : ℝ) ≤ (i : ℝ) * (d : ℝ) := by exact_mod_cast hkle
        have hsum := add_le_add hfLower hpLower
        have hnonneg : (0 : ℝ) ≤
            ((r : ℝ) + (slope : ℝ)) * ((i : ℝ) * (d : ℝ) - (k : ℝ)) :=
          mul_nonneg (le_of_lt hpos) (sub_nonneg.mpr hkR)
        field_simp [ne_of_gt hdR] at hsum ⊢
        nlinarith
      have hzsumR : (z : ℝ) < (zf : ℝ) + (zp : ℝ) := lt_of_lt_of_le hzlt htarget
      have hzsumInt : z < zf + zp := by exact_mod_cast hzsumR
      have hzTop : ((z : ℤ) : WithTop ℤ) < (((zf + zp : ℤ)) : WithTop ℤ) := by
        exact_mod_cast hzsumInt
      rw [AddValuation.map_mul]
      rw [← hzf, ← hzp]
      convert hzTop using 1
  have hsumstrict : ((z : ℤ) : WithTop ℤ) <
      v (∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (g ^ i).coeff k) := by
    apply AddValuation.map_lt_sum
    · simp
    · exact hterms
  rw [← hcoeff_sum, hval] at hsumstrict
  exact (lt_irrefl (((z : ℤ) : WithTop ℤ))) hsumstrict

private theorem pureAt_comp_prPure
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {r : ℕ} {slope : ℚ} {f g : K[X]}
    (hf : PureAt (v : K → WithTop ℤ) f slope)
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos : (0 : ℝ) < (r : ℝ) + (slope : ℝ)) :
    PureAt (v : K → WithTop ℤ) (f.comp g) (slope / (g.natDegree : ℚ)) := by
  have hfpos : 0 < f.natDegree := PureAt.natDegree_pos hf
  have hgpos : 0 < g.natDegree := PrPure.natDegree_pos hg
  have hfgdeg : (f.comp g).natDegree = f.natDegree * g.natDegree := by
    rw [Polynomial.natDegree_comp]
  have hfgpos : 0 < (f.comp g).natDegree := by
    rw [hfgdeg]
    exact Nat.mul_pos hfpos hgpos
  have hdata : HasNewtonPolygonData (v : K → WithTop ℤ) f
      [{ length := f.natDegree, length_pos := hfpos, slope := slope }] := by
    exact PureAt.hasNewtonPolygonData hf
  rcases HasNewtonPolygonData.exists_startHeight hdata with ⟨start, hNP⟩
  have hcoeff0ne : f.coeff 0 ≠ 0 :=
    oneSegment_coeff_zero_ne (v := v) (start := start) (slope := slope)
      (n := f.natDegree) (f := f) hfpos hNP
  have hv0ne : v (f.coeff 0) ≠ (⊤ : WithTop ℤ) := by
    rw [AddValuation.ne_top_iff v]
    exact hcoeff0ne
  rcases WithTop.ne_top_iff_exists.mp hv0ne with ⟨z0, hz0raw⟩
  have h0 : v (f.coeff 0) = ((z0 : ℤ) : WithTop ℤ) := hz0raw.symm
  have hstart : start = (z0 : ℚ) :=
    oneSegment_start_eq_coeff_zero_of_valuation
      (v := v) (start := start) (slope := slope)
      (n := f.natDegree) (f := f) hfpos hNP h0
  have hfne : f ≠ 0 := by
    intro hfzero
    exact hcoeff0ne (by simp [hfzero])
  have hleadne : f.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hfne
  have hvleadne : v f.leadingCoeff ≠ (⊤ : WithTop ℤ) := by
    rw [AddValuation.ne_top_iff v]
    exact hleadne
  rcases WithTop.ne_top_iff_exists.mp hvleadne with ⟨zN, hzNraw⟩
  have hlead : v f.leadingCoeff = ((zN : ℤ) : WithTop ℤ) := hzNraw.symm
  have hend : start + (f.natDegree : ℚ) * slope = (zN : ℚ) :=
    oneSegment_end_eq_leadingCoeff_of_valuation
      (v := v) (start := start) (slope := slope)
      (n := f.natDegree) (f := f) hfpos rfl hNP hlead
  have hfline : ∀ (i : ℕ) (z : ℤ), i ≤ f.natDegree → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (start : ℝ) + (slope : ℝ) * (i : ℝ) ≤ (z : ℝ) := by
    intro i z hi hcoeff hz
    exact oneSegment_affine_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (start := start) (slope := slope)
      (n := f.natDegree) (i := i) (z := z) (f := f) hfpos hNP hi hcoeff hz
  have hgline : ∀ (j : ℕ) (z : ℤ), j ≤ g.natDegree → g.coeff j ≠ 0 →
      v (g.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (g.natDegree : ℝ)) * (j : ℝ) ≤ (z : ℝ) := by
    intro j z hj hcoeff hz
    have hgdata : HasNewtonPolygonData (v : K → WithTop ℤ) g
        [{ length := g.natDegree, length_pos := hgpos,
           slope := prPureSlope r g.natDegree }] := by
      exact PureAt.hasNewtonPolygonData (PrPure.pureAt hg)
    rcases HasNewtonPolygonData.exists_startHeight hgdata with ⟨sg, hNPg⟩
    have hsg : sg = (r : ℚ) := prPure_startHeight_eq hg hNPg
    subst sg
    exact oneSegment_line_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (r := r) (n := g.natDegree) (i := j)
      (z := z) (f := g) hgpos hNPg hj hcoeff hz
  have hconst : v ((f.comp g).coeff 0) = ((z0 : ℤ) : WithTop ℤ) := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    have htail : ∀ i ∈ Finset.Icc 1 f.natDegree,
        ((z0 : ℤ) : WithTop ℤ) < v (f.coeff i * (g.eval 0) ^ i) := by
      intro i hi
      by_cases hcoeff : f.coeff i = 0
      · simp [hcoeff, AddValuation.map_zero]
      · have hvne : v (f.coeff i) ≠ (⊤ : WithTop ℤ) := by
          rw [AddValuation.ne_top_iff v]
          exact hcoeff
        rcases WithTop.ne_top_iff_exists.mp hvne with ⟨zi, hzi⟩
        have hile : i ≤ f.natDegree := (Finset.mem_Icc.mp hi).2
        have hfLower : (start : ℝ) + (slope : ℝ) * (i : ℝ) ≤ (zi : ℝ) :=
          hfline i zi hile hcoeff hzi.symm
        have hstartR : (start : ℝ) = (z0 : ℝ) := by exact_mod_cast hstart
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hzR : (z0 : ℝ) < (zi : ℝ) + (i : ℝ) * (r : ℝ) := by
          have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
          nlinarith [hfLower, hstartR, hpos, hiR]
        have hzInt : z0 < zi + (i : ℤ) * (r : ℤ) := by exact_mod_cast hzR
        have hzTop : ((z0 : ℤ) : WithTop ℤ) <
            (((zi + (i : ℤ) * (r : ℤ) : ℤ)) : WithTop ℤ) := by
          exact_mod_cast hzInt
        rw [AddValuation.map_mul, AddValuation.map_pow]
        rw [← coeff_zero_eq_eval_zero, PrPure.coeff_zero_valuation hg]
        rw [← hzi]
        convert hzTop using 1
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_range_succ']
    have hsum : ((z0 : ℤ) : WithTop ℤ) <
        v (∑ k ∈ Finset.range f.natDegree,
            f.coeff (k + 1) * (g.eval 0) ^ (k + 1)) := by
      apply AddValuation.map_lt_sum
      · simp
      · intro k hk
        exact htail (k + 1) (by simp [Finset.mem_range.mp hk])
    have hconstTerm : v (f.coeff 0 * (g.eval 0) ^ 0) = ((z0 : ℤ) : WithTop ℤ) := by
      simpa using h0
    rw [AddValuation.map_add_eq_of_lt_right v]
    · exact hconstTerm
    · rw [hconstTerm]
      exact hsum
  have hleadComp : v (f.comp g).leadingCoeff = ((zN : ℤ) : WithTop ℤ) := by
    have hgdeg_ne : g.natDegree ≠ 0 := Nat.ne_of_gt hgpos
    rw [Polynomial.leadingCoeff_comp hgdeg_ne]
    rw [AddValuation.map_mul, AddValuation.map_pow]
    rw [PrPure.leadingCoeff_valuation hg]
    rw [hlead]
    simp
  have hcompLower : ∀ i z, i ≤ f.natDegree * g.natDegree →
      (f.comp g).coeff i ≠ 0 →
      v ((f.comp g).coeff i) = ((z : ℤ) : WithTop ℤ) →
      (start : ℝ) + ((slope / (g.natDegree : ℚ) : ℚ) : ℝ) * (i : ℝ) ≤
        (z : ℝ) := by
    intro i z hi hcoeff hz
    simpa using comp_coeff_affine_lower
      (v := v) (start := start) (slope := slope) (r := r)
      (d := g.natDegree) (f := f) (g := g)
      hgpos rfl hpos hfline hgline i z hcoeff hz
  have hendComp :
      start + ((f.natDegree * g.natDegree : ℕ) : ℚ) *
          (slope / (g.natDegree : ℚ)) = (zN : ℚ) := by
    have hgdQ : (g.natDegree : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hgpos
    rw [← hend]
    field_simp [hgdQ]
    rw [Nat.cast_mul]
    ring
  have hnp : HasNewtonPolygonData (v : K → WithTop ℤ) (f.comp g)
      [{ length := f.natDegree * g.natDegree,
         length_pos := Nat.mul_pos hfpos hgpos,
         slope := slope / (g.natDegree : ℚ) }] := by
    exact oneSegment_of_endpoint_and_affine_lower
      (v := v) (start := start) (slope := slope / (g.natDegree : ℚ))
      (n := f.natDegree * g.natDegree) (f := f.comp g)
      (z0 := z0) (zN := zN) (Nat.mul_pos hfpos hgpos) hfgdeg
      hconst hleadComp hstart hendComp hcompLower
  refine ⟨hfgpos, ?_⟩
  simpa [hfgdeg] using hnp

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    {data : NewtonPolygonData} (hNP : HasNewtonPolygonData (v : K → WithTop ℤ) f data)
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos : ∀ seg ∈ data, (0 : ℝ) < (r : ℝ) + (seg.slope : ℝ)) :
    ∃ factors : List K[X],
      f.comp g = factors.prod ∧
        List.Forall₂
          (fun factor (seg : SegmentData) =>
            factor.natDegree = seg.length ∧ PureAt (v : K → WithTop ℤ) factor seg.slope)
          factors
          (data.map fun seg : SegmentData =>
            { length := seg.length * g.natDegree,
              length_pos := Nat.mul_pos seg.length_pos (PrPure.natDegree_pos hg),
              slope := seg.slope / (g.natDegree : ℚ) }) := by
  rcases blackbox_np_factor_by_segments hNP with ⟨factors, hprod, hforall⟩
  refine ⟨factors.map fun factor : K[X] => factor.comp g, ?_, ?_⟩
  · rw [← Polynomial.list_prod_comp, hprod]
  · clear hNP hprod
    induction hforall with
    | nil => simp
    | cons hseg htail ih =>
        simp only [List.map_cons, List.forall₂_cons]
        constructor
        · constructor
          · rw [Polynomial.natDegree_comp, hseg.1]
          · exact pureAt_comp_prPure hseg.2 hg (hpos _ (by simp))
        · exact ih (by
            intro seg hmem
            exact hpos seg (by simp [hmem]))

private theorem prPure_comp_prPure
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {f g : K[X]}
    (hf : PrPure (v : K → WithTop ℤ) r f) (hg : PrPure (v : K → WithTop ℤ) r g)
    (hdeg : 1 < f.natDegree) :
    PrPure (v : K → WithTop ℤ) r (f.comp g) := by
  have hfpos : 0 < f.natDegree := PrPure.natDegree_pos hf
  have hgpos : 0 < g.natDegree := PrPure.natDegree_pos hg
  have hcompDeg : (f.comp g).natDegree = f.natDegree * g.natDegree := by
    rw [Polynomial.natDegree_comp]
  have hcompPos : 0 < (f.comp g).natDegree := by
    rw [hcompDeg]
    exact Nat.mul_pos hfpos hgpos
  have hconst : v ((f.comp g).coeff 0) = (((r : ℤ) : WithTop ℤ)) :=
    prPure_comp_coeff_zero_from_PrPure hf hg hdeg
  have hlead : v (f.comp g).leadingCoeff = (((0 : ℤ) : WithTop ℤ)) := by
    have hgdeg : g.natDegree ≠ 0 := Nat.ne_of_gt hgpos
    rw [Polynomial.leadingCoeff_comp hgdeg]
    rw [AddValuation.map_mul, AddValuation.map_pow]
    rw [PrPure.leadingCoeff_valuation hf, PrPure.leadingCoeff_valuation hg]
    simp
  have hfline : ∀ (i : ℕ) (z : ℤ), i ≤ f.natDegree → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (f.natDegree : ℝ)) * (i : ℝ) ≤ (z : ℝ) := by
    intro i z hi hcoeff hz
    have hdata : HasNewtonPolygonData (v : K → WithTop ℤ) f
        [{ length := f.natDegree, length_pos := hfpos,
           slope := prPureSlope r f.natDegree }] := by
      exact PureAt.hasNewtonPolygonData (PrPure.pureAt hf)
    rcases HasNewtonPolygonData.exists_startHeight hdata with ⟨s, hNP⟩
    have hs : s = (r : ℚ) := prPure_startHeight_eq hf hNP
    subst s
    exact oneSegment_line_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (r := r) (n := f.natDegree) (i := i)
      (z := z) (f := f) hfpos hNP hi hcoeff hz
  have hgline : ∀ (j : ℕ) (z : ℤ), j ≤ g.natDegree → g.coeff j ≠ 0 →
      v (g.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / (g.natDegree : ℝ)) * (j : ℝ) ≤ (z : ℝ) := by
    intro j z hj hcoeff hz
    have hdata : HasNewtonPolygonData (v : K → WithTop ℤ) g
        [{ length := g.natDegree, length_pos := hgpos,
           slope := prPureSlope r g.natDegree }] := by
      exact PureAt.hasNewtonPolygonData (PrPure.pureAt hg)
    rcases HasNewtonPolygonData.exists_startHeight hdata with ⟨s, hNP⟩
    have hs : s = (r : ℚ) := prPure_startHeight_eq hg hNP
    subst s
    exact oneSegment_line_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (r := r) (n := g.natDegree) (i := j)
      (z := z) (f := g) hgpos hNP hj hcoeff hz
  have hcompLower : ∀ (k : ℕ) (z : ℤ), k ≤ f.natDegree * g.natDegree →
      (f.comp g).coeff k ≠ 0 →
      v ((f.comp g).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (r : ℝ) - ((r : ℝ) / ((f.natDegree * g.natDegree : ℕ) : ℝ)) *
          (k : ℝ) ≤ (z : ℝ) := by
    exact comp_coeff_line_lower
      (v := v) (r := r) (e := f.natDegree) (d := g.natDegree) (f := f) (g := g)
      hfpos hgpos rfl rfl hfline hgline
  have hnp : HasNewtonPolygonData (v : K → WithTop ℤ) (f.comp g)
      [{ length := f.natDegree * g.natDegree,
         length_pos := Nat.mul_pos hfpos hgpos,
         slope := prPureSlope r (f.natDegree * g.natDegree) }] := by
    exact oneSegment_of_endpoint_and_lower
      (v := v) (r := r) (n := f.natDegree * g.natDegree) (f := f.comp g)
      (Nat.mul_pos hfpos hgpos) hcompDeg hconst hlead hcompLower
  refine ⟨PrPure.r_pos hf, ?_⟩
  refine ⟨hcompPos, hconst, hlead, ?_⟩
  refine ⟨hcompPos, ?_⟩
  simpa [hcompDeg] using hnp

example {K : Type*} [Field K] {p q : K[X]} {k : ℕ} :
    (p * q).coeff k = ∑ x ∈ Finset.antidiagonal k, p.coeff x.1 * q.coeff x.2 := by
  exact Polynomial.coeff_mul p q k

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {p q : K[X]} {k : ℕ}
    {M : WithTop ℤ}
    (hterms : ∀ x ∈ Finset.antidiagonal k, M ≤ v (p.coeff x.1 * q.coeff x.2)) :
    M ≤ v ((p * q).coeff k) := by
  rw [Polynomial.coeff_mul]
  exact AddValuation.map_le_sum v hterms

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {p q : K[X]} {a b : ℕ}
    {A B : WithTop ℤ}
    (hp : A ≤ v (p.coeff a)) (hq : B ≤ v (q.coeff b)) :
    A + B ≤ v (p.coeff a * q.coeff b) := by
  rw [AddValuation.map_mul]
  exact add_le_add hp hq

private theorem twoSegment_summand_line_lower
    {n i j k : ℕ} {s1 s2 start1 start2 : ℚ}
    (hs : (s1 : ℝ) < (s2 : ℝ))
    (hk : i + j = k)
    (hi : i ≤ n) :
    (if k ≤ n then
      (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (k : ℝ)
    else
      (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (n : ℝ) +
        (s2 : ℝ) * ((k - n : ℕ) : ℝ)) ≤
      (start1 : ℝ) + (s1 : ℝ) * (i : ℝ) +
        ((start2 : ℝ) + (s2 : ℝ) * (j : ℝ)) := by
  have hdiff : (0 : ℝ) < (s2 : ℝ) - (s1 : ℝ) := sub_pos.mpr hs
  by_cases hkn : k ≤ n
  · simp [hkn]
    have hkR : (i : ℝ) + (j : ℝ) = (k : ℝ) := by exact_mod_cast hk
    have hjnonneg : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
    have hprod : (0 : ℝ) ≤ ((s2 : ℝ) - (s1 : ℝ)) * (j : ℝ) :=
      mul_nonneg (le_of_lt hdiff) hjnonneg
    have hrewrite :
        ((start1 : ℝ) + (s1 : ℝ) * (i : ℝ) +
            ((start2 : ℝ) + (s2 : ℝ) * (j : ℝ))) -
          ((start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (k : ℝ)) =
            ((s2 : ℝ) - (s1 : ℝ)) * (j : ℝ) := by
      rw [← hkR]
      ring
    nlinarith
  · simp [hkn]
    have hnle : n ≤ k := Nat.le_of_not_ge hkn
    have hkR : (i : ℝ) + (j : ℝ) = (k : ℝ) := by exact_mod_cast hk
    have hknR : ((k - n : ℕ) : ℝ) = (k : ℝ) - (n : ℝ) := Nat.cast_sub hnle
    have hinonneg : (0 : ℝ) ≤ (n : ℝ) - (i : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hi)
    have hprod : (0 : ℝ) ≤ ((s2 : ℝ) - (s1 : ℝ)) * ((n : ℝ) - (i : ℝ)) :=
      mul_nonneg (le_of_lt hdiff) hinonneg
    have hrewrite :
        ((start1 : ℝ) + (s1 : ℝ) * (i : ℝ) +
            ((start2 : ℝ) + (s2 : ℝ) * (j : ℝ))) -
          ((start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (n : ℝ) +
            (s2 : ℝ) * ((k - n : ℕ) : ℝ)) =
            ((s2 : ℝ) - (s1 : ℝ)) * ((n : ℝ) - (i : ℝ)) := by
      rw [hknR, ← hkR]
      ring
    nlinarith

private theorem product_two_coeff_broken_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {p q : K[X]} {start1 start2 s1 s2 : ℚ} {n m : ℕ}
    (hdegp : p.natDegree = n) (hdegq : q.natDegree = m)
    (hs : (s1 : ℝ) < (s2 : ℝ))
    (hpline : ∀ (i : ℕ) (z : ℤ), i ≤ n → p.coeff i ≠ 0 →
      v (p.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (start1 : ℝ) + (s1 : ℝ) * (i : ℝ) ≤ (z : ℝ))
    (hqline : ∀ (j : ℕ) (z : ℤ), j ≤ m → q.coeff j ≠ 0 →
      v (q.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (start2 : ℝ) + (s2 : ℝ) * (j : ℝ) ≤ (z : ℝ)) :
    ∀ (k : ℕ) (z : ℤ), (p * q).coeff k ≠ 0 →
      v ((p * q).coeff k) = ((z : ℤ) : WithTop ℤ) →
      (if k ≤ n then
        (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (k : ℝ)
      else
        (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (n : ℝ) +
          (s2 : ℝ) * ((k - n : ℕ) : ℝ)) ≤ (z : ℝ) := by
  intro k z hcoeff hval
  by_contra hnot
  have hzlt : (z : ℝ) <
      (if k ≤ n then
        (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (k : ℝ)
      else
        (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (n : ℝ) +
          (s2 : ℝ) * ((k - n : ℕ) : ℝ)) := lt_of_not_ge hnot
  have hcoeff_sum : (p * q).coeff k =
      ∑ x ∈ Finset.antidiagonal k, p.coeff x.1 * q.coeff x.2 := by
    exact Polynomial.coeff_mul p q k
  have hterms : ∀ x ∈ Finset.antidiagonal k,
      ((z : ℤ) : WithTop ℤ) < v (p.coeff x.1 * q.coeff x.2) := by
    intro x hx
    by_cases hterm : p.coeff x.1 * q.coeff x.2 = 0
    · rw [hterm, AddValuation.map_zero]
      exact WithTop.coe_lt_top z
    · have hpcoeff : p.coeff x.1 ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hqcoeff : q.coeff x.2 ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hvpne : v (p.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hpcoeff
      have hvqne : v (q.coeff x.2) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hqcoeff
      rcases WithTop.ne_top_iff_exists.mp hvpne with ⟨zp, hzp⟩
      rcases WithTop.ne_top_iff_exists.mp hvqne with ⟨zq, hzq⟩
      have hile : x.1 ≤ n := by
        have hle := Polynomial.le_natDegree_of_ne_zero (p := p) hpcoeff
        simpa [hdegp] using hle
      have hjle : x.2 ≤ m := by
        have hle := Polynomial.le_natDegree_of_ne_zero (p := q) hqcoeff
        simpa [hdegq] using hle
      have hpLower : (start1 : ℝ) + (s1 : ℝ) * (x.1 : ℝ) ≤ (zp : ℝ) :=
        hpline x.1 zp hile hpcoeff hzp.symm
      have hqLower : (start2 : ℝ) + (s2 : ℝ) * (x.2 : ℝ) ≤ (zq : ℝ) :=
        hqline x.2 zq hjle hqcoeff hzq.symm
      have hxsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
      have hlineLower :
          (if k ≤ n then
            (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (k : ℝ)
          else
            (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (n : ℝ) +
              (s2 : ℝ) * ((k - n : ℕ) : ℝ)) ≤
            (start1 : ℝ) + (s1 : ℝ) * (x.1 : ℝ) +
              ((start2 : ℝ) + (s2 : ℝ) * (x.2 : ℝ)) :=
        twoSegment_summand_line_lower (n := n) (i := x.1) (j := x.2) (k := k)
          (s1 := s1) (s2 := s2) (start1 := start1) (start2 := start2)
          hs hxsum hile
      have htarget :
          (if k ≤ n then
            (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (k : ℝ)
          else
            (start1 : ℝ) + (start2 : ℝ) + (s1 : ℝ) * (n : ℝ) +
              (s2 : ℝ) * ((k - n : ℕ) : ℝ)) ≤ (zp : ℝ) + (zq : ℝ) := by
        have hsumLower := add_le_add hpLower hqLower
        exact le_trans hlineLower hsumLower
      have hzsumR : (z : ℝ) < (zp : ℝ) + (zq : ℝ) := lt_of_lt_of_le hzlt htarget
      have hzsumInt : z < zp + zq := by exact_mod_cast hzsumR
      have hzTop : ((z : ℤ) : WithTop ℤ) < (((zp + zq : ℤ)) : WithTop ℤ) := by
        exact_mod_cast hzsumInt
      rw [AddValuation.map_mul]
      rw [← hzp, ← hzq]
      convert hzTop using 1
  have hsumstrict : ((z : ℤ) : WithTop ℤ) <
      v (∑ x ∈ Finset.antidiagonal k, p.coeff x.1 * q.coeff x.2) := by
    apply AddValuation.map_lt_sum
    · simp
    · exact hterms
  rw [← hcoeff_sum, hval] at hsumstrict
  exact (lt_irrefl (((z : ℤ) : WithTop ℤ))) hsumstrict

private theorem product_two_middle_coeff_valuation
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {p q : K[X]} {start1 start2 s1 s2 : ℚ} {n m : ℕ} {zNp zQ0 : ℤ}
    (hdegp : p.natDegree = n) (hdegq : q.natDegree = m)
    (hs : (s1 : ℝ) < (s2 : ℝ))
    (hpLead : v p.leadingCoeff = ((zNp : ℤ) : WithTop ℤ))
    (hq0 : v (q.coeff 0) = ((zQ0 : ℤ) : WithTop ℤ))
    (hpEnd : start1 + (n : ℚ) * s1 = (zNp : ℚ))
    (hqStart : start2 = (zQ0 : ℚ))
    (hpline : ∀ (i : ℕ) (z : ℤ), i ≤ n → p.coeff i ≠ 0 →
      v (p.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (start1 : ℝ) + (s1 : ℝ) * (i : ℝ) ≤ (z : ℝ))
    (hqline : ∀ (j : ℕ) (z : ℤ), j ≤ m → q.coeff j ≠ 0 →
      v (q.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (start2 : ℝ) + (s2 : ℝ) * (j : ℝ) ≤ (z : ℝ)) :
    v ((p * q).coeff n) = (((zNp + zQ0 : ℤ)) : WithTop ℤ) := by
  have htarget_mem : (n, 0) ∈ Finset.antidiagonal n := by
    simp
  have hpLeadCoeff : p.coeff n = p.leadingCoeff := by
    rw [← hdegp, Polynomial.coeff_natDegree]
  have htargetVal :
      v (p.coeff n * q.coeff 0) = (((zNp + zQ0 : ℤ)) : WithTop ℤ) := by
    rw [AddValuation.map_mul, hpLeadCoeff, hpLead, hq0]
    rfl
  have hstrict : ∀ x ∈ Finset.antidiagonal n \ {(n, 0)},
      v (p.coeff n * q.coeff 0) < v (p.coeff x.1 * q.coeff x.2) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxanti, hxnot⟩
    have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hxanti
    have hxne : x ≠ (n, 0) := by
      intro hxeq
      exact hxnot (by simp [hxeq])
    have hx2pos : 0 < x.2 := by
      cases h2 : x.2 with
      | zero =>
          have hx1 : x.1 = n := by simpa [h2] using hxsum
          exact False.elim (hxne (by ext <;> simp [hx1, h2]))
      | succ t =>
          exact Nat.succ_pos t
    by_cases hterm : p.coeff x.1 * q.coeff x.2 = 0
    · rw [hterm, AddValuation.map_zero, htargetVal]
      exact WithTop.coe_lt_top (zNp + zQ0)
    · have hpcoeff : p.coeff x.1 ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hqcoeff : q.coeff x.2 ≠ 0 := by
        intro hzero
        exact hterm (by simp [hzero])
      have hvpne : v (p.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hpcoeff
      have hvqne : v (q.coeff x.2) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hqcoeff
      rcases WithTop.ne_top_iff_exists.mp hvpne with ⟨zp, hzp⟩
      rcases WithTop.ne_top_iff_exists.mp hvqne with ⟨zq, hzq⟩
      have hile : x.1 ≤ n := by
        have hle : x.1 ≤ x.1 + x.2 := Nat.le_add_right x.1 x.2
        simpa [hxsum] using hle
      have hjle : x.2 ≤ m := by
        have hle := Polynomial.le_natDegree_of_ne_zero (p := q) hqcoeff
        simpa [hdegq] using hle
      have hpLower : (start1 : ℝ) + (s1 : ℝ) * (x.1 : ℝ) ≤ (zp : ℝ) :=
        hpline x.1 zp hile hpcoeff hzp.symm
      have hqLower : (start2 : ℝ) + (s2 : ℝ) * (x.2 : ℝ) ≤ (zq : ℝ) :=
        hqline x.2 zq hjle hqcoeff hzq.symm
      have hpEndR : (start1 : ℝ) + (n : ℝ) * (s1 : ℝ) = (zNp : ℝ) := by
        have hpEndR' : ((start1 + (n : ℚ) * s1 : ℚ) : ℝ) = (zNp : ℝ) := by
          exact_mod_cast hpEnd
        simpa using hpEndR'
      have hqStartR : (start2 : ℝ) = (zQ0 : ℝ) := by exact_mod_cast hqStart
      have hxsumR : (x.1 : ℝ) + (x.2 : ℝ) = (n : ℝ) := by exact_mod_cast hxsum
      have hx2posR : (0 : ℝ) < (x.2 : ℝ) := by exact_mod_cast hx2pos
      have hzsumR : ((zNp + zQ0 : ℤ) : ℝ) < (zp : ℝ) + (zq : ℝ) := by
        have hgap : (0 : ℝ) < ((s2 : ℝ) - (s1 : ℝ)) * (x.2 : ℝ) :=
          mul_pos (sub_pos.mpr hs) hx2posR
        have hidentity :
            ((start1 : ℝ) + (s1 : ℝ) * (x.1 : ℝ) +
                ((start2 : ℝ) + (s2 : ℝ) * (x.2 : ℝ))) -
              ((start1 : ℝ) + (n : ℝ) * (s1 : ℝ) + (start2 : ℝ)) =
                ((s2 : ℝ) - (s1 : ℝ)) * (x.2 : ℝ) := by
          rw [← hxsumR]
          ring
        have htargetCast : ((zNp + zQ0 : ℤ) : ℝ) = (zNp : ℝ) + (zQ0 : ℝ) := by
          norm_num
        nlinarith [hpLower, hqLower, hpEndR, hqStartR, hgap, hidentity, htargetCast]
      have hzsumInt : zNp + zQ0 < zp + zq := by exact_mod_cast hzsumR
      have hzTop :
          (((zNp + zQ0 : ℤ)) : WithTop ℤ) <
            (((zp + zq : ℤ)) : WithTop ℤ) := by
        exact_mod_cast hzsumInt
      rw [htargetVal, AddValuation.map_mul, ← hzp, ← hzq]
      convert hzTop using 1
  have hsumVal :
      v (∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2) =
        v (p.coeff n * q.coeff 0) := by
    have h := Valuation.map_sum_eq_of_lt (AddValuation.toValuation v)
      (s := Finset.antidiagonal n)
      (f := fun x : ℕ × ℕ => p.coeff x.1 * q.coeff x.2)
      (j := (n, 0)) htarget_mem (by
      intro x hx
      simpa [AddValuation.toValuation_apply] using hstrict x hx)
    simpa [AddValuation.toValuation_apply] using h
  rw [Polynomial.coeff_mul]
  exact hsumVal.trans htargetVal

private theorem twoSegment_of_endpoint_and_broken_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {start s1 s2 : ℚ} {n m : ℕ} {f : K[X]} {z0 zM zN : ℤ}
    (hn : 0 < n) (hm : 0 < m) (hdeg : f.natDegree = n + m)
    (hs : (s1 : ℝ) < (s2 : ℝ))
    (h0 : v (f.coeff 0) = ((z0 : ℤ) : WithTop ℤ))
    (hmiddle : v (f.coeff n) = ((zM : ℤ) : WithTop ℤ))
    (hlead : v f.leadingCoeff = ((zN : ℤ) : WithTop ℤ))
    (hstart : start = (z0 : ℚ))
    (hmid : start + (n : ℚ) * s1 = (zM : ℚ))
    (hend : start + (n : ℚ) * s1 + (m : ℚ) * s2 = (zN : ℚ))
    (hlower : ∀ i z, i ≤ n + m → f.coeff i ≠ 0 →
      v (f.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (if i ≤ n then
        (start : ℝ) + (s1 : ℝ) * (i : ℝ)
      else
        (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
          (s2 : ℝ) * ((i - n : ℕ) : ℝ)) ≤ (z : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) f
      [{ length := n, length_pos := hn, slope := s1 },
       { length := m, length_pos := hm, slope := s2 }] := by
  let data : NewtonPolygonData :=
    [{ length := n, length_pos := hn, slope := s1 },
     { length := m, length_pos := hm, slope := s2 }]
  let v0 : ℝ × ℝ := ((0 : ℝ), (start : ℝ))
  let v1 : ℝ × ℝ := ((n : ℝ), (start : ℝ) + (n : ℝ) * (s1 : ℝ))
  let v2 : ℝ × ℝ :=
    (((n + m : ℕ) : ℝ),
      (start : ℝ) + (n : ℝ) * (s1 : ℝ) + (m : ℝ) * (s2 : ℝ))
  have hstartR : (start : ℝ) = (z0 : ℝ) := by exact_mod_cast hstart
  have hmidR : (start : ℝ) + (n : ℝ) * (s1 : ℝ) = (zM : ℝ) := by
    have hmidR' : ((start + (n : ℚ) * s1 : ℚ) : ℝ) = (zM : ℝ) := by
      exact_mod_cast hmid
    simpa using hmidR'
  have hendR :
      (start : ℝ) + (n : ℝ) * (s1 : ℝ) + (m : ℝ) * (s2 : ℝ) = (zN : ℝ) := by
    have hendR' :
        ((start + (n : ℚ) * s1 + (m : ℚ) * s2 : ℚ) : ℝ) = (zN : ℝ) := by
      exact_mod_cast hend
    simpa using hendR'
  have hverts : verticesSet start data = {v0, v1, v2} := by
    ext x
    constructor
    · intro hx
      simp [data, verticesSet, verticesFrom, SegmentData.nextVertex, v0, v1, v2] at hx ⊢
      rcases hx with hx | hx | hx
      · left
        exact hx
      · right
        left
        rw [hx]
      · right
        right
        rw [hx]
    · intro hx
      simp [data, verticesSet, verticesFrom, SegmentData.nextVertex, v0, v1, v2] at hx ⊢
      rcases hx with hx | hx | hx
      · left
        exact hx
      · right
        left
        rw [hx]
      · right
        right
        rw [hx]
  constructor
  · constructor
    · exact_mod_cast hs
    · simp
  constructor
  · simp [totalLength, hdeg]
  · refine ⟨start, ?_⟩
    apply Set.Subset.antisymm
    · intro q hq
      rcases hq with ⟨p, hp, hpx, hpy⟩
      let W : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ ((n + m : ℕ) : ℝ) ∧
        (start : ℝ) + (s1 : ℝ) * q.1 ≤ q.2 ∧
        (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
          (s2 : ℝ) * (q.1 - (n : ℝ)) ≤ q.2}
      have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
        intro q hq
        rcases hq with ⟨i, z, hi, hcoeff, hz, rfl⟩
        have hi' : i ≤ n + m := by simpa [hdeg] using hi
        constructor
        · change (0 : ℝ) ≤ (i : ℝ)
          exact_mod_cast Nat.zero_le i
        constructor
        · change (i : ℝ) ≤ ((n + m : ℕ) : ℝ)
          exact_mod_cast hi'
        have hbroken := hlower i z hi' hcoeff hz
        by_cases hin : i ≤ n
        · have hline1 : (start : ℝ) + (s1 : ℝ) * (i : ℝ) ≤ (z : ℝ) := by
            simpa [hin] using hbroken
          have hline2le1 :
              (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                  (s2 : ℝ) * ((i : ℝ) - (n : ℝ)) ≤
                (start : ℝ) + (s1 : ℝ) * (i : ℝ) := by
            have hiR : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
            nlinarith [hs]
          exact ⟨hline1, le_trans hline2le1 hline1⟩
        · have hnle : n ≤ i := Nat.le_of_not_ge hin
          have hline2 : (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
              (s2 : ℝ) * ((i : ℝ) - (n : ℝ)) ≤ (z : ℝ) := by
            have hcast : ((i - n : ℕ) : ℝ) = (i : ℝ) - (n : ℝ) :=
              Nat.cast_sub hnle
            simpa [hin, hcast] using hbroken
          have hline1le2 :
              (start : ℝ) + (s1 : ℝ) * (i : ℝ) ≤
                (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                  (s2 : ℝ) * ((i : ℝ) - (n : ℝ)) := by
            have hnR : (n : ℝ) ≤ (i : ℝ) := by exact_mod_cast hnle
            nlinarith [hs]
          exact ⟨le_trans hline1le2 hline2, hline2⟩
      have hWconv : Convex ℝ W := by
        intro x hx y hy a b ha hb hab
        constructor
        · change 0 ≤ a * x.1 + b * y.1
          exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
        constructor
        · change a * x.1 + b * y.1 ≤ ((n + m : ℕ) : ℝ)
          calc
            a * x.1 + b * y.1 ≤
                a * (((n + m : ℕ) : ℝ)) + b * (((n + m : ℕ) : ℝ)) :=
              add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
                (mul_le_mul_of_nonneg_left hy.2.1 hb)
            _ = ((n + m : ℕ) : ℝ) := by rw [← add_mul, hab, one_mul]
        constructor
        · change (start : ℝ) + (s1 : ℝ) * (a * x.1 + b * y.1) ≤
            a * x.2 + b * y.2
          have hxline :
              a * ((start : ℝ) + (s1 : ℝ) * x.1) ≤ a * x.2 :=
            mul_le_mul_of_nonneg_left hx.2.2.1 ha
          have hyline :
              b * ((start : ℝ) + (s1 : ℝ) * y.1) ≤ b * y.2 :=
            mul_le_mul_of_nonneg_left hy.2.2.1 hb
          have hsum :
              a * ((start : ℝ) + (s1 : ℝ) * x.1) +
                  b * ((start : ℝ) + (s1 : ℝ) * y.1) ≤
                a * x.2 + b * y.2 :=
            add_le_add hxline hyline
          have haff :
              (start : ℝ) + (s1 : ℝ) * (a * x.1 + b * y.1) =
                a * ((start : ℝ) + (s1 : ℝ) * x.1) +
                  b * ((start : ℝ) + (s1 : ℝ) * y.1) := by
            calc
              (start : ℝ) + (s1 : ℝ) * (a * x.1 + b * y.1) =
                  (a + b) * (start : ℝ) + (s1 : ℝ) * (a * x.1 + b * y.1) := by
                rw [hab]
                ring
              _ = a * ((start : ℝ) + (s1 : ℝ) * x.1) +
                  b * ((start : ℝ) + (s1 : ℝ) * y.1) := by
                ring
          rw [haff]
          exact hsum
        · change (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
              (s2 : ℝ) * ((a * x.1 + b * y.1) - (n : ℝ)) ≤
            a * x.2 + b * y.2
          have hxline :
              a * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (x.1 - (n : ℝ))) ≤ a * x.2 :=
            mul_le_mul_of_nonneg_left hx.2.2.2 ha
          have hyline :
              b * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (y.1 - (n : ℝ))) ≤ b * y.2 :=
            mul_le_mul_of_nonneg_left hy.2.2.2 hb
          have hsum :
              a * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (x.1 - (n : ℝ))) +
                  b * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (y.1 - (n : ℝ))) ≤
                a * x.2 + b * y.2 :=
            add_le_add hxline hyline
          have haff :
              (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                  (s2 : ℝ) * ((a * x.1 + b * y.1) - (n : ℝ)) =
                a * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (x.1 - (n : ℝ))) +
                  b * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (y.1 - (n : ℝ))) := by
            calc
              (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                  (s2 : ℝ) * ((a * x.1 + b * y.1) - (n : ℝ)) =
                (a + b) * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) -
                    (s2 : ℝ) * (n : ℝ)) + (s2 : ℝ) * (a * x.1 + b * y.1) := by
                rw [hab]
                ring
              _ = a * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (x.1 - (n : ℝ))) +
                  b * ((start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                    (s2 : ℝ) * (y.1 - (n : ℝ))) := by
                ring
          rw [haff]
          exact hsum
      have hpW : p ∈ W := convexHull_min hsub hWconv hp
      have hqW : q ∈ W := by
        constructor
        · rw [← hpx]
          exact hpW.1
        constructor
        · rw [← hpx]
          exact hpW.2.1
        constructor
        · have hlinep :
              (start : ℝ) + (s1 : ℝ) * q.1 =
                (start : ℝ) + (s1 : ℝ) * p.1 := by rw [← hpx]
          rw [hlinep]
          exact le_trans hpW.2.2.1 hpy
        · have hlinep :
              (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                  (s2 : ℝ) * (q.1 - (n : ℝ)) =
                (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
                  (s2 : ℝ) * (p.1 - (n : ℝ)) := by rw [← hpx]
          rw [hlinep]
          exact le_trans hpW.2.2.2 hpy
      rcases hqW with ⟨hqx0, hqxN, hqline1, hqline2⟩
      by_cases hqxle : q.1 ≤ (n : ℝ)
      · let p0 : ℝ × ℝ := (q.1, (start : ℝ) + (s1 : ℝ) * q.1)
        refine ⟨p0, ?_, rfl, hqline1⟩
        have hpair_subset : ({v0, v1} : Set (ℝ × ℝ)) ⊆ verticesSet start data := by
          intro x hx
          rw [hverts]
          simp at hx ⊢
          rcases hx with hx | hx
          · left
            exact hx
          · right
            left
            exact hx
        apply convexHull_mono hpair_subset
        rw [convexHull_pair]
        refine ⟨1 - q.1 / (n : ℝ), q.1 / (n : ℝ), ?_, ?_, ?_, ?_⟩
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          field_simp [ne_of_gt hnpos]
          nlinarith
        · exact div_nonneg hqx0 (by exact_mod_cast hn.le)
        · field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]
          ring
        · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          ext
          · simp [p0, v0, v1]
            field_simp [hn0]
          · simp [p0, v0, v1]
            field_simp [hn0]
            ring
      · let p0 : ℝ × ℝ :=
          (q.1, (start : ℝ) + (s1 : ℝ) * (n : ℝ) +
            (s2 : ℝ) * (q.1 - (n : ℝ)))
        refine ⟨p0, ?_, rfl, hqline2⟩
        have hnleq : (n : ℝ) ≤ q.1 := le_of_not_ge hqxle
        have hpair_subset : ({v1, v2} : Set (ℝ × ℝ)) ⊆ verticesSet start data := by
          intro x hx
          rw [hverts]
          simp at hx ⊢
          rcases hx with hx | hx
          · right
            left
            exact hx
          · right
            right
            exact hx
        apply convexHull_mono hpair_subset
        rw [convexHull_pair]
        refine ⟨1 - (q.1 - (n : ℝ)) / (m : ℝ),
          (q.1 - (n : ℝ)) / (m : ℝ), ?_, ?_, ?_, ?_⟩
        · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
          field_simp [ne_of_gt hmpos]
          have hqle : q.1 ≤ (n : ℝ) + (m : ℝ) := by
            simpa using hqxN
          nlinarith
        · exact div_nonneg (sub_nonneg.mpr hnleq) (by exact_mod_cast hm.le)
        · field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hm]
          ring
        · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
          have hnm : (((n + m : ℕ) : ℝ)) = (n : ℝ) + (m : ℝ) := by norm_num
          ext
          · simp [p0, v1, v2, hnm]
            field_simp [hm0]
            ring
          · simp [p0, v1, v2, hnm]
            field_simp [hm0]
            ring
    · change lowerConvexEpigraph (verticesSet start data) ⊆
        lowerConvexEpigraph (coefficientSupportPoints (v : K → WithTop ℤ) f)
      apply lowerConvexEpigraph_mono
      intro p hp
      rw [hverts] at hp
      rcases hp with hp | hp | hp
      · rw [hp]
        refine ⟨0, z0, Nat.zero_le _, ?_, h0, ?_⟩
        · rw [← AddValuation.ne_top_iff v]
          rw [h0]
          simp
        · ext <;> simp [v0, hstartR]
      · rw [hp]
        refine ⟨n, zM, ?_, ?_, hmiddle, ?_⟩
        · rw [hdeg]
          exact Nat.le_add_right n m
        · rw [← AddValuation.ne_top_iff v]
          rw [hmiddle]
          simp
        · ext <;> simp [v1, hmidR]
      · rw [hp]
        refine ⟨n + m, zN, ?_, ?_, ?_, ?_⟩
        · rw [← hdeg]
        · rw [← AddValuation.ne_top_iff v]
          rw [← hdeg, Polynomial.coeff_natDegree, hlead]
          simp
        · rw [← hdeg, Polynomial.coeff_natDegree]
          exact hlead
        · ext <;> simp [v2, hendR]

private theorem product_two_pure_strict_slopes
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {p q : K[X]} {s1 s2 : ℚ}
    (hp : PureAt (v : K → WithTop ℤ) p s1)
    (hq : PureAt (v : K → WithTop ℤ) q s2)
    (hs : (s1 : ℝ) < (s2 : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) (p * q)
      [{ length := p.natDegree, length_pos := PureAt.natDegree_pos hp, slope := s1 },
       { length := q.natDegree, length_pos := PureAt.natDegree_pos hq, slope := s2 }] := by
  let n := p.natDegree
  let m := q.natDegree
  have hpPos : 0 < n := PureAt.natDegree_pos hp
  have hqPos : 0 < m := PureAt.natDegree_pos hq
  have hpne : p ≠ 0 := by
    intro hpzero
    have : n = 0 := by simp [n, hpzero]
    exact Nat.ne_of_gt hpPos this
  have hqne : q ≠ 0 := by
    intro hqzero
    have : m = 0 := by simp [m, hqzero]
    exact Nat.ne_of_gt hqPos this
  have hpData : HasNewtonPolygonData (v : K → WithTop ℤ) p
      [{ length := n, length_pos := hpPos, slope := s1 }] := by
    simpa [n] using PureAt.hasNewtonPolygonData hp
  have hqData : HasNewtonPolygonData (v : K → WithTop ℤ) q
      [{ length := m, length_pos := hqPos, slope := s2 }] := by
    simpa [m] using PureAt.hasNewtonPolygonData hq
  rcases HasNewtonPolygonData.exists_startHeight hpData with ⟨sp, hpNP⟩
  rcases HasNewtonPolygonData.exists_startHeight hqData with ⟨sq, hqNP⟩
  have hp0ne : p.coeff 0 ≠ 0 :=
    oneSegment_coeff_zero_ne (v := v) (start := sp) (slope := s1)
      (n := n) (f := p) hpPos hpNP
  have hq0ne : q.coeff 0 ≠ 0 :=
    oneSegment_coeff_zero_ne (v := v) (start := sq) (slope := s2)
      (n := m) (f := q) hqPos hqNP
  have hpLeadNe : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hqLeadNe : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hqne
  have hvp0ne : v (p.coeff 0) ≠ (⊤ : WithTop ℤ) := by
    rw [AddValuation.ne_top_iff v]
    exact hp0ne
  have hvq0ne : v (q.coeff 0) ≠ (⊤ : WithTop ℤ) := by
    rw [AddValuation.ne_top_iff v]
    exact hq0ne
  have hvpLeadNe : v p.leadingCoeff ≠ (⊤ : WithTop ℤ) := by
    rw [AddValuation.ne_top_iff v]
    exact hpLeadNe
  have hvqLeadNe : v q.leadingCoeff ≠ (⊤ : WithTop ℤ) := by
    rw [AddValuation.ne_top_iff v]
    exact hqLeadNe
  rcases WithTop.ne_top_iff_exists.mp hvp0ne with ⟨zp0, hzp0raw⟩
  rcases WithTop.ne_top_iff_exists.mp hvq0ne with ⟨zq0, hzq0raw⟩
  rcases WithTop.ne_top_iff_exists.mp hvpLeadNe with ⟨zpN, hzpNraw⟩
  rcases WithTop.ne_top_iff_exists.mp hvqLeadNe with ⟨zqN, hzqNraw⟩
  have hp0val : v (p.coeff 0) = ((zp0 : ℤ) : WithTop ℤ) := hzp0raw.symm
  have hq0val : v (q.coeff 0) = ((zq0 : ℤ) : WithTop ℤ) := hzq0raw.symm
  have hpLeadVal : v p.leadingCoeff = ((zpN : ℤ) : WithTop ℤ) := hzpNraw.symm
  have hqLeadVal : v q.leadingCoeff = ((zqN : ℤ) : WithTop ℤ) := hzqNraw.symm
  have hsp : sp = (zp0 : ℚ) :=
    oneSegment_start_eq_coeff_zero_of_valuation
      (v := v) (start := sp) (slope := s1) (n := n) (f := p)
      hpPos hpNP hp0val
  have hsq : sq = (zq0 : ℚ) :=
    oneSegment_start_eq_coeff_zero_of_valuation
      (v := v) (start := sq) (slope := s2) (n := m) (f := q)
      hqPos hqNP hq0val
  have hpEnd : sp + (n : ℚ) * s1 = (zpN : ℚ) :=
    oneSegment_end_eq_leadingCoeff_of_valuation
      (v := v) (start := sp) (slope := s1) (n := n) (f := p)
      hpPos rfl hpNP hpLeadVal
  have hqEnd : sq + (m : ℚ) * s2 = (zqN : ℚ) :=
    oneSegment_end_eq_leadingCoeff_of_valuation
      (v := v) (start := sq) (slope := s2) (n := m) (f := q)
      hqPos rfl hqNP hqLeadVal
  have hpLine : ∀ (i : ℕ) (z : ℤ), i ≤ n → p.coeff i ≠ 0 →
      v (p.coeff i) = ((z : ℤ) : WithTop ℤ) →
      (sp : ℝ) + (s1 : ℝ) * (i : ℝ) ≤ (z : ℝ) := by
    intro i z hi hcoeff hz
    exact oneSegment_affine_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (start := sp) (slope := s1)
      (n := n) (i := i) (z := z) (f := p) hpPos hpNP
      (by simpa [n] using hi) hcoeff hz
  have hqLine : ∀ (j : ℕ) (z : ℤ), j ≤ m → q.coeff j ≠ 0 →
      v (q.coeff j) = ((z : ℤ) : WithTop ℤ) →
      (sq : ℝ) + (s2 : ℝ) * (j : ℝ) ≤ (z : ℝ) := by
    intro j z hj hcoeff hz
    exact oneSegment_affine_lower_of_newtonPolygon_eq
      (ord := (v : K → WithTop ℤ)) (start := sq) (slope := s2)
      (n := m) (i := j) (z := z) (f := q) hqPos hqNP
      (by simpa [m] using hj) hcoeff hz
  have hprodDeg : (p * q).natDegree = n + m := by
    simpa [n, m] using Polynomial.natDegree_mul hpne hqne
  have hprod0 : v ((p * q).coeff 0) = (((zp0 + zq0 : ℤ)) : WithTop ℤ) := by
    have hcoeff0 : (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
      rw [Polynomial.coeff_mul]
      simp
    rw [hcoeff0, AddValuation.map_mul, hp0val, hq0val]
    rfl
  have hprodMid : v ((p * q).coeff n) =
      (((zpN + zq0 : ℤ)) : WithTop ℤ) := by
    exact product_two_middle_coeff_valuation
      (v := v) (p := p) (q := q) (start1 := sp) (start2 := sq)
      (s1 := s1) (s2 := s2) (n := n) (m := m)
      (zNp := zpN) (zQ0 := zq0) rfl rfl hs hpLeadVal hq0val hpEnd hsq
      hpLine hqLine
  have hprodLead : v (p * q).leadingCoeff =
      (((zpN + zqN : ℤ)) : WithTop ℤ) := by
    rw [Polynomial.leadingCoeff_mul, AddValuation.map_mul, hpLeadVal, hqLeadVal]
    rfl
  have hstartProd : sp + sq = ((zp0 + zq0 : ℤ) : ℚ) := by
    rw [hsp, hsq]
    norm_num
  have hmidProd : sp + sq + (n : ℚ) * s1 = ((zpN + zq0 : ℤ) : ℚ) := by
    rw [show ((zpN + zq0 : ℤ) : ℚ) = (zpN : ℚ) + (zq0 : ℚ) by norm_num]
    rw [← hpEnd, hsq]
    ring
  have hendProd :
      sp + sq + (n : ℚ) * s1 + (m : ℚ) * s2 = ((zpN + zqN : ℤ) : ℚ) := by
    rw [show ((zpN + zqN : ℤ) : ℚ) = (zpN : ℚ) + (zqN : ℚ) by norm_num]
    rw [← hpEnd, ← hqEnd]
    ring
  have hprodLower : ∀ i z, i ≤ n + m → (p * q).coeff i ≠ 0 →
      v ((p * q).coeff i) = ((z : ℤ) : WithTop ℤ) →
      (if i ≤ n then
        ((sp + sq : ℚ) : ℝ) + (s1 : ℝ) * (i : ℝ)
      else
        ((sp + sq : ℚ) : ℝ) + (s1 : ℝ) * (n : ℝ) +
          (s2 : ℝ) * ((i - n : ℕ) : ℝ)) ≤ (z : ℝ) := by
    intro i z _ hcoeff hz
    have hraw := product_two_coeff_broken_lower
      (v := v) (p := p) (q := q) (start1 := sp) (start2 := sq)
      (s1 := s1) (s2 := s2) (n := n) (m := m)
      rfl rfl hs hpLine hqLine i z hcoeff hz
    by_cases hin : i ≤ n
    · simpa [hin, Rat.cast_add, add_assoc] using hraw
    · simpa [hin, Rat.cast_add, add_assoc] using hraw
  simpa [n, m] using
    twoSegment_of_endpoint_and_broken_lower
      (v := v) (start := sp + sq) (s1 := s1) (s2 := s2)
      (n := n) (m := m) (f := p * q)
      (z0 := zp0 + zq0) (zM := zpN + zq0) (zN := zpN + zqN)
      hpPos hqPos hprodDeg hs hprod0 hprodMid hprodLead hstartProd hmidProd hendProd
      hprodLower

example (factors : List ℚ[X]) (g : ℚ[X]) :
    factors.prod.comp g = (factors.map fun h : ℚ[X] => h.comp g).prod := by
  exact Polynomial.list_prod_comp factors g

example {K : Type*} [Field K] {ord : K → WithTop ℤ} {f g : K[X]}
    {data : NewtonPolygonData} (hNP : HasNewtonPolygonData ord f data) :
    ∃ factors : List K[X],
      f.comp g = (factors.map fun factor : K[X] => factor.comp g).prod ∧
        List.Forall₂
          (fun factor seg => factor.natDegree = seg.length ∧ PureAt ord factor seg.slope)
          factors data := by
  rcases blackbox_np_factor_by_segments hNP with ⟨factors, hprod, hforall⟩
  refine ⟨factors, ?_, hforall⟩
  rw [← Polynomial.list_prod_comp, hprod]

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {r : ℕ} {g : K[X]}
    {factors : List K[X]} {data : NewtonPolygonData}
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos : ∀ seg ∈ data, (0 : ℝ) < (r : ℝ) + (seg.slope : ℝ))
    (hforall : List.Forall₂
      (fun factor seg =>
        factor.natDegree = seg.length ∧ PureAt (v : K → WithTop ℤ) factor seg.slope)
      factors data) :
    List.Forall₂
      (fun composed seg => composed.natDegree = seg.length * g.natDegree ∧
        PureAt (v : K → WithTop ℤ) composed (seg.slope / (g.natDegree : ℚ)))
      (factors.map fun factor : K[X] => factor.comp g) data := by
  rw [List.forall₂_map_left_iff]
  induction hforall with
  | nil => simp
  | cons hseg htail ih =>
      simp only [List.forall₂_cons]
      constructor
      · constructor
        · rw [Polynomial.natDegree_comp, hseg.1]
        · exact pureAt_comp_prPure hseg.2 hg (hpos _ (by simp))
      · exact ih (by
          intro seg hmem
          exact hpos seg (by simp [hmem]))

/- Arbitrary-list Newton polygon assembly: helpers, the N-segment
criterion, the product-of-pure-factors theorem
(LEM_PRODUCT_OF_PURE_STRICT_SLOPES), and the full main stretching
theorem (THM_MAIN_STRETCH_STRONG). -/

private theorem npAssembly_totalLength_append (l₁ l₂ : NewtonPolygonData) :
    totalLength (l₁ ++ l₂) = totalLength l₁ + totalLength l₂ := by
  induction l₁ with
  | nil => simp
  | cons seg rest ih => simp [ih, Nat.add_assoc]

private theorem npAssembly_take_succ (data : NewtonPolygonData) (t : ℕ)
    (ht : t < data.length) :
    data.take (t + 1) = data.take t ++ [data[t]'ht] := by
  rw [List.take_succ, List.getElem?_eq_getElem ht]
  rfl

private theorem npAssembly_totalLength_take_succ (data : NewtonPolygonData) (t : ℕ)
    (ht : t < data.length) :
    totalLength (data.take (t + 1)) =
      totalLength (data.take t) + (data[t]'ht).length := by
  rw [npAssembly_take_succ data t ht, npAssembly_totalLength_append]
  simp

private theorem npAssembly_totalLength_take_le (data : NewtonPolygonData) (t : ℕ) :
    totalLength (data.take t) ≤ totalLength data := by
  conv_rhs => rw [← List.take_append_drop t data]
  rw [npAssembly_totalLength_append]
  exact Nat.le_add_right _ _

private theorem npAssembly_slopeSum_take_succ (data : NewtonPolygonData) (t : ℕ)
    (ht : t < data.length) :
    ((data.take (t + 1)).map (fun seg => (seg.length : ℚ) * seg.slope)).sum =
      ((data.take t).map (fun seg => (seg.length : ℚ) * seg.slope)).sum +
        ((data[t]'ht).length : ℚ) * (data[t]'ht).slope := by
  rw [npAssembly_take_succ data t ht, List.map_append, List.sum_append]
  simp

private theorem npAssembly_mem_verticesFrom (data : NewtonPolygonData) :
    ∀ (p : ℝ × ℝ) (x : ℝ × ℝ), x ∈ verticesFrom p data ↔
      ∃ t, t ≤ data.length ∧
        x = (p.1 + (totalLength (data.take t) : ℝ),
             p.2 + ((((data.take t).map (fun seg => (seg.length : ℚ) * seg.slope)).sum : ℚ) : ℝ)) := by
  induction data with
  | nil =>
      intro p x
      simp only [verticesFrom_nil, List.mem_singleton, List.length_nil]
      constructor
      · intro h
        refine ⟨0, le_rfl, ?_⟩
        rw [h]
        ext <;> simp
      · rintro ⟨t, ht, hx⟩
        have ht0 : t = 0 := Nat.le_zero.mp ht
        subst ht0
        rw [hx]
        ext <;> simp
  | cons seg rest ih =>
      intro p x
      rw [verticesFrom_cons]
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with hx | hx
        · refine ⟨0, Nat.zero_le _, ?_⟩
          rw [hx]
          ext <;> simp
        · rcases (ih (seg.nextVertex p) x).mp hx with ⟨t, ht, hx'⟩
          refine ⟨t + 1, Nat.succ_le_succ ht, ?_⟩
          rw [hx']
          have h1 : ((seg :: rest).take (t + 1)) = seg :: rest.take t := by
            simp [List.take_succ_cons]
          rw [h1]
          ext
          · simp [SegmentData.nextVertex, totalLength]
            push_cast
            ring
          · simp [SegmentData.nextVertex]
            push_cast
            ring
      · rintro ⟨t, ht, hx⟩
        cases t with
        | zero =>
            apply List.mem_cons.mpr
            left
            rw [hx]
            ext <;> simp
        | succ t' =>
            apply List.mem_cons.mpr
            right
            apply (ih (seg.nextVertex p) x).mpr
            refine ⟨t', Nat.le_of_succ_le_succ ht, ?_⟩
            rw [hx]
            have h1 : ((seg :: rest).take (t' + 1)) = seg :: rest.take t' := by
              simp [List.take_succ_cons]
            rw [h1]
            ext
            · simp [SegmentData.nextVertex, totalLength]
              push_cast
              ring
            · simp [SegmentData.nextVertex]
              push_cast
              ring

private theorem npAssembly_exists_segment (data : NewtonPolygonData) :
    ∀ w : ℝ, data ≠ [] → 0 ≤ w → w ≤ (totalLength data : ℝ) →
      ∃ t, ∃ ht : t < data.length,
        (totalLength (data.take t) : ℝ) ≤ w ∧
        w ≤ (totalLength (data.take (t + 1)) : ℝ) := by
  induction data with
  | nil =>
      intro w hne _ _
      exact absurd rfl hne
  | cons seg rest ih =>
      intro w _ hw0 hwL
      by_cases hcase : w ≤ (seg.length : ℝ)
      · refine ⟨0, Nat.succ_pos _, ?_, ?_⟩
        · simpa using hw0
        · simpa [totalLength] using hcase
      · push_neg at hcase
        have hLcast : (totalLength (seg :: rest) : ℝ) =
            (seg.length : ℝ) + (totalLength rest : ℝ) := by
          rw [totalLength_cons]
          push_cast
          ring
        have hrest : rest ≠ [] := by
          intro h
          subst h
          rw [hLcast] at hwL
          simp [totalLength] at hwL
          linarith
        have hwL' : w - (seg.length : ℝ) ≤ (totalLength rest : ℝ) := by
          rw [hLcast] at hwL
          linarith
        rcases ih (w - (seg.length : ℝ)) hrest (by linarith) hwL' with ⟨t, ht, hlo, hhi⟩
        refine ⟨t + 1, Nat.succ_lt_succ ht, ?_, ?_⟩
        · have h1 : totalLength ((seg :: rest).take (t + 1)) =
              seg.length + totalLength (rest.take t) := by
            simp [totalLength]
          rw [h1]
          push_cast
          linarith
        · have h1 : totalLength ((seg :: rest).take (t + 2)) =
              seg.length + totalLength (rest.take (t + 1)) := by
            simp [totalLength]
          rw [h1]
          push_cast
          linarith

private theorem npAssembly_strictSlopes_tail {a : SegmentData} {data : NewtonPolygonData}
    (h : StrictlyIncreasingSlopes (a :: data)) : StrictlyIncreasingSlopes data := by
  cases data with
  | nil => trivial
  | cons b rest => exact h.2

private theorem npAssembly_strictSlopes_head_lt :
    ∀ (data : NewtonPolygonData) (a : SegmentData),
      StrictlyIncreasingSlopes (a :: data) →
      ∀ t (ht : t < data.length), a.slope < (data[t]'ht).slope := by
  intro data
  induction data with
  | nil =>
      intro a _ t ht
      exact absurd ht (Nat.not_lt_zero t)
  | cons b rest ih =>
      intro a hinc t ht
      cases t with
      | zero => simpa using hinc.1
      | succ t' =>
          have ht' : t' < rest.length := Nat.lt_of_succ_lt_succ ht
          have h1 : b.slope < (rest[t']'ht').slope := ih b hinc.2 t' ht'
          have h2 : ((b :: rest)[t' + 1]'ht) = rest[t']'ht' := by
            simp
          rw [h2]
          exact lt_trans hinc.1 h1

private theorem npAssembly_polygon_of_vertices_and_lines
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {f : K[X]} {data : NewtonPolygonData} {z : ℕ → ℤ}
    (hne : data ≠ [])
    (hinc : StrictlyIncreasingSlopes data)
    (hdeg : f.natDegree = totalLength data)
    (hvert : ∀ t, t ≤ data.length →
      v (f.coeff (totalLength (data.take t))) = ((z t : ℤ) : WithTop ℤ))
    (hstep : ∀ t (ht : t < data.length),
      (z (t + 1) : ℚ) = (z t : ℚ) + ((data[t]'ht).length : ℚ) * (data[t]'ht).slope)
    (hlower : ∀ i zz, f.coeff i ≠ 0 → v (f.coeff i) = ((zz : ℤ) : WithTop ℤ) →
      ∀ t (ht : t < data.length),
        (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
          ((i : ℝ) - (totalLength (data.take t) : ℝ)) ≤ (zz : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) f data := by
  have hzsum : ∀ t, t ≤ data.length → (z t : ℚ) = (z 0 : ℚ) +
      ((data.take t).map (fun seg => (seg.length : ℚ) * seg.slope)).sum := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t iht =>
        intro ht
        have ht' : t < data.length := Nat.lt_of_succ_le ht
        rw [hstep t ht', iht (Nat.le_of_lt ht'), npAssembly_slopeSum_take_succ data t ht']
        ring
  have hvertex_support : ∀ t, t ≤ data.length →
      ((totalLength (data.take t) : ℝ), ((z t : ℤ) : ℝ)) ∈
        coefficientSupportPoints (v : K → WithTop ℤ) f := by
    intro t ht
    refine ⟨totalLength (data.take t), z t, ?_, ?_, hvert t ht, rfl⟩
    · rw [hdeg]
      exact npAssembly_totalLength_take_le data t
    · rw [← AddValuation.ne_top_iff v, hvert t ht]
      simp
  have hvertset : ∀ x : ℝ × ℝ, x ∈ verticesSet ((z 0 : ℤ) : ℚ) data ↔
      ∃ t, t ≤ data.length ∧
        x = ((totalLength (data.take t) : ℝ), ((z t : ℤ) : ℝ)) := by
    intro x
    have hbase : x ∈ verticesSet ((z 0 : ℤ) : ℚ) data ↔
        x ∈ verticesFrom ((0 : ℝ), (((z 0 : ℤ) : ℚ) : ℝ)) data := Iff.rfl
    rw [hbase, npAssembly_mem_verticesFrom data]
    constructor
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, ht, ?_⟩
      rw [hx]
      have hz : (((z t : ℤ) : ℚ) : ℝ) =
          (((z 0 : ℤ) : ℚ) : ℝ) +
            ((((data.take t).map (fun seg => (seg.length : ℚ) * seg.slope)).sum : ℚ) : ℝ) := by
        rw [← Rat.cast_add]
        exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) (hzsum t ht)
      ext
      · simp
      · simp only []
        rw [← hz]
        push_cast
        ring
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, ht, ?_⟩
      rw [hx]
      have hz : (((z t : ℤ) : ℚ) : ℝ) =
          (((z 0 : ℤ) : ℚ) : ℝ) +
            ((((data.take t).map (fun seg => (seg.length : ℚ) * seg.slope)).sum : ℚ) : ℝ) := by
        rw [← Rat.cast_add]
        exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) (hzsum t ht)
      ext
      · simp
      · simp only []
        rw [← hz]
        push_cast
        ring
  refine ⟨hinc, hdeg, ⟨((z 0 : ℤ) : ℚ), ?_⟩⟩
  apply Set.Subset.antisymm
  · intro q hq
    rcases hq with ⟨p, hp, hpx, hpy⟩
    let W : Set (ℝ × ℝ) := {w : ℝ × ℝ | 0 ≤ w.1 ∧ w.1 ≤ (totalLength data : ℝ) ∧
      ∀ t, ∀ ht : t < data.length,
        (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
          (w.1 - (totalLength (data.take t) : ℝ)) ≤ w.2}
    have hsub : coefficientSupportPoints (v : K → WithTop ℤ) f ⊆ W := by
      intro w hw
      rcases hw with ⟨i, zi, hi, hcoeff, hz, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · change (0 : ℝ) ≤ (i : ℝ)
        exact_mod_cast Nat.zero_le i
      · change (i : ℝ) ≤ (totalLength data : ℝ)
        have hi' : i ≤ totalLength data := by simpa [hdeg] using hi
        exact_mod_cast hi'
      · intro t ht
        exact hlower i zi hcoeff hz t ht
    have hWconv : Convex ℝ W := by
      intro x hx y hy a b ha hb hab
      refine ⟨?_, ?_, ?_⟩
      · change 0 ≤ a * x.1 + b * y.1
        exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      · change a * x.1 + b * y.1 ≤ (totalLength data : ℝ)
        calc
          a * x.1 + b * y.1 ≤
              a * (totalLength data : ℝ) + b * (totalLength data : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
              (mul_le_mul_of_nonneg_left hy.2.1 hb)
          _ = (totalLength data : ℝ) := by rw [← add_mul, hab, one_mul]
      · intro t ht
        have hxt := hx.2.2 t ht
        have hyt := hy.2.2 t ht
        change (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
            ((a * x.1 + b * y.1) - (totalLength (data.take t) : ℝ)) ≤
          a * x.2 + b * y.2
        have hxline : a * ((z t : ℝ) + ((data[t]'ht).slope : ℝ) *
            (x.1 - (totalLength (data.take t) : ℝ))) ≤ a * x.2 :=
          mul_le_mul_of_nonneg_left hxt ha
        have hyline : b * ((z t : ℝ) + ((data[t]'ht).slope : ℝ) *
            (y.1 - (totalLength (data.take t) : ℝ))) ≤ b * y.2 :=
          mul_le_mul_of_nonneg_left hyt hb
        have haff : (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
            ((a * x.1 + b * y.1) - (totalLength (data.take t) : ℝ)) =
              a * ((z t : ℝ) + ((data[t]'ht).slope : ℝ) *
                (x.1 - (totalLength (data.take t) : ℝ))) +
              b * ((z t : ℝ) + ((data[t]'ht).slope : ℝ) *
                (y.1 - (totalLength (data.take t) : ℝ))) := by
          calc
            (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
                ((a * x.1 + b * y.1) - (totalLength (data.take t) : ℝ)) =
              (a + b) * ((z t : ℝ) - ((data[t]'ht).slope : ℝ) *
                  (totalLength (data.take t) : ℝ)) +
                ((data[t]'ht).slope : ℝ) * (a * x.1 + b * y.1) := by
              rw [hab]
              ring
            _ = a * ((z t : ℝ) + ((data[t]'ht).slope : ℝ) *
                  (x.1 - (totalLength (data.take t) : ℝ))) +
                b * ((z t : ℝ) + ((data[t]'ht).slope : ℝ) *
                  (y.1 - (totalLength (data.take t) : ℝ))) := by
              ring
        rw [haff]
        exact add_le_add hxline hyline
    have hpW : p ∈ W := convexHull_min hsub hWconv hp
    obtain ⟨hp0, hpL, hplines⟩ := hpW
    have hq0 : 0 ≤ q.1 := by rw [← hpx]; exact hp0
    have hqL : q.1 ≤ (totalLength data : ℝ) := by rw [← hpx]; exact hpL
    rcases npAssembly_exists_segment data q.1 hne hq0 hqL with ⟨t, ht, hlo, hhi⟩
    have hℓpos : (0 : ℝ) < ((data[t]'ht).length : ℝ) := by
      exact_mod_cast (data[t]'ht).length_pos
    have hℓne : ((data[t]'ht).length : ℝ) ≠ 0 := ne_of_gt hℓpos
    have hx1 : (totalLength (data.take (t + 1)) : ℝ) =
        (totalLength (data.take t) : ℝ) + ((data[t]'ht).length : ℝ) := by
      rw [npAssembly_totalLength_take_succ data t ht]
      push_cast
      ring
    have hzt1 : ((z (t + 1) : ℤ) : ℝ) = ((z t : ℤ) : ℝ) +
        ((data[t]'ht).length : ℝ) * ((data[t]'ht).slope : ℝ) := by
      have h := hstep t ht
      have h' : ((z (t + 1) : ℚ) : ℝ) =
          (((z t : ℚ) + ((data[t]'ht).length : ℚ) * (data[t]'ht).slope : ℚ) : ℝ) := by
        exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) h
      push_cast at h'
      push_cast
      linarith
    refine ⟨(q.1, ((z t : ℤ) : ℝ) + ((data[t]'ht).slope : ℝ) *
        (q.1 - (totalLength (data.take t) : ℝ))), ?_, rfl, ?_⟩
    · have hpair : ({((totalLength (data.take t) : ℝ), ((z t : ℤ) : ℝ)),
          ((totalLength (data.take (t + 1)) : ℝ), ((z (t + 1) : ℤ) : ℝ))} : Set (ℝ × ℝ)) ⊆
          verticesSet ((z 0 : ℤ) : ℚ) data := by
        intro y hy
        rcases hy with hy | hy
        · exact (hvertset y).mpr ⟨t, Nat.le_of_lt ht, hy⟩
        · exact (hvertset y).mpr ⟨t + 1, Nat.succ_le_of_lt ht, hy⟩
      apply convexHull_mono hpair
      rw [convexHull_pair]
      refine ⟨1 - (q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ),
        (q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ),
        ?_, ?_, by ring, ?_⟩
      · have hqle : q.1 - (totalLength (data.take t) : ℝ) ≤ ((data[t]'ht).length : ℝ) := by
          rw [hx1] at hhi
          linarith
        have : (q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ) ≤ 1 := by
          rw [div_le_one hℓpos]
          exact hqle
        linarith
      · exact div_nonneg (by linarith) (le_of_lt hℓpos)
      · ext
        · show (1 - (q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ)) *
              (totalLength (data.take t) : ℝ) +
            ((q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ)) *
              (totalLength (data.take (t + 1)) : ℝ) = q.1
          rw [hx1]
          field_simp
          ring
        · show (1 - (q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ)) *
              ((z t : ℤ) : ℝ) +
            ((q.1 - (totalLength (data.take t) : ℝ)) / ((data[t]'ht).length : ℝ)) *
              ((z (t + 1) : ℤ) : ℝ) =
            ((z t : ℤ) : ℝ) + ((data[t]'ht).slope : ℝ) *
              (q.1 - (totalLength (data.take t) : ℝ))
          rw [hzt1]
          field_simp
          ring
    · have h1 : (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
          (q.1 - (totalLength (data.take t) : ℝ)) =
        (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
          (p.1 - (totalLength (data.take t) : ℝ)) := by
        rw [hpx]
      show (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
          (q.1 - (totalLength (data.take t) : ℝ)) ≤ q.2
      rw [h1]
      exact le_trans (hplines t ht) hpy
  · show polygonEpigraph ((z 0 : ℤ) : ℚ) data ⊆ newtonPolygon (v : K → WithTop ℤ) f
    apply lowerConvexEpigraph_mono
    intro x hx
    rcases (hvertset x).mp hx with ⟨t, ht, rfl⟩
    exact hvertex_support t ht

private theorem npAssembly_product_vertex_and_lower
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {factors : List K[X]} {data : NewtonPolygonData}
    (hforall : List.Forall₂ (fun q seg => q.natDegree = seg.length ∧
        PureAt (v : K → WithTop ℤ) q seg.slope) factors data) :
    StrictlyIncreasingSlopes data →
    factors.prod ≠ 0 ∧
    factors.prod.natDegree = totalLength data ∧
    ∃ z : ℕ → ℤ,
      (∀ t, t ≤ data.length →
        v (factors.prod.coeff (totalLength (data.take t))) = ((z t : ℤ) : WithTop ℤ)) ∧
      (∀ t, ∀ ht : t < data.length,
        (z (t + 1) : ℚ) = (z t : ℚ) + ((data[t]'ht).length : ℚ) * (data[t]'ht).slope) ∧
      (∀ i zz, factors.prod.coeff i ≠ 0 →
        v (factors.prod.coeff i) = ((zz : ℤ) : WithTop ℤ) →
        ∀ t, ∀ ht : t < data.length,
          (z t : ℝ) + ((data[t]'ht).slope : ℝ) *
            ((i : ℝ) - (totalLength (data.take t) : ℝ)) ≤ (zz : ℝ)) := by
  induction hforall with
  | nil =>
      intro _
      refine ⟨one_ne_zero, by simp, fun _ => 0, ?_, ?_, ?_⟩
      · intro t ht
        have ht0 : t = 0 := Nat.le_zero.mp ht
        subst ht0
        show v ((List.prod ([] : List K[X])).coeff
          (totalLength (List.take 0 ([] : NewtonPolygonData)))) = ((0 : ℤ) : WithTop ℤ)
        simp only [List.prod_nil, List.take_nil, totalLength_nil]
        rw [show ((1 : K[X]).coeff 0) = (1 : K) by simp]
        rw [AddValuation.map_one]
        rfl
      · intro t ht
        exact absurd ht (Nat.not_lt_zero t)
      · intro i zz _ _ t ht
        exact absurd ht (Nat.not_lt_zero t)
  | @cons p seg rest dtail hpseg htail ih =>
      intro hinc
      have hincTail : StrictlyIncreasingSlopes dtail := npAssembly_strictSlopes_tail hinc
      have hheadlt : ∀ t (ht : t < dtail.length), seg.slope < (dtail[t]'ht).slope :=
        npAssembly_strictSlopes_head_lt dtail seg hinc
      obtain ⟨hPne, hPdeg, z, hPvert, hPstep, hPlower⟩ := ih hincTail
      have hdp : 0 < p.natDegree := PureAt.natDegree_pos hpseg.2
      obtain ⟨start, hNPp⟩ :=
        HasNewtonPolygonData.exists_startHeight (PureAt.hasNewtonPolygonData hpseg.2)
      have hp0ne : p.coeff 0 ≠ 0 := oneSegment_coeff_zero_ne hdp hNPp
      have hpne : p ≠ 0 := by
        intro h
        exact hp0ne (by simp [h])
      have hpLeadne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpne
      have hvp0 : v (p.coeff 0) ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hp0ne
      have hvpN : v p.leadingCoeff ≠ (⊤ : WithTop ℤ) := by
        rw [AddValuation.ne_top_iff v]
        exact hpLeadne
      obtain ⟨zp0, hzp0⟩ := WithTop.ne_top_iff_exists.mp hvp0
      obtain ⟨zpN, hzpN⟩ := WithTop.ne_top_iff_exists.mp hvpN
      have hp0val : v (p.coeff 0) = ((zp0 : ℤ) : WithTop ℤ) := hzp0.symm
      have hpLeadval : v p.leadingCoeff = ((zpN : ℤ) : WithTop ℤ) := hzpN.symm
      have hstart : start = (zp0 : ℚ) :=
        oneSegment_start_eq_coeff_zero_of_valuation hdp hNPp hp0val
      have hpEndQ : start + (p.natDegree : ℚ) * seg.slope = (zpN : ℚ) :=
        oneSegment_end_eq_leadingCoeff_of_valuation hdp rfl hNPp hpLeadval
      have hpEnd : (zp0 : ℚ) + (seg.length : ℚ) * seg.slope = (zpN : ℚ) := by
        rw [hstart, hpseg.1] at hpEndQ
        exact hpEndQ
      have hpline : ∀ (i : ℕ) (zi : ℤ), p.coeff i ≠ 0 →
          v (p.coeff i) = ((zi : ℤ) : WithTop ℤ) →
          (zp0 : ℝ) + (seg.slope : ℝ) * (i : ℝ) ≤ (zi : ℝ) := by
        intro i zi hci hzi
        have h := oneSegment_affine_lower_of_newtonPolygon_eq hdp hNPp
          (Polynomial.le_natDegree_of_ne_zero hci) hci hzi
        rw [hstart] at h
        exact_mod_cast h
      have hprodne : p * rest.prod ≠ 0 := mul_ne_zero hpne hPne
      simp only [List.prod_cons, totalLength_cons, List.length_cons]
      refine ⟨hprodne, by rw [Polynomial.natDegree_mul hpne hPne, hpseg.1, hPdeg],
        fun t => match t with | 0 => zp0 + z 0 | (t' + 1) => zpN + z t', ?_, ?_, ?_⟩
      · intro t ht
        cases t with
        | zero =>
            show v ((p * rest.prod).coeff (totalLength ((seg :: dtail).take 0))) =
              ((zp0 + z 0 : ℤ) : WithTop ℤ)
            have h0 : totalLength ((seg :: dtail).take 0) = 0 := rfl
            rw [h0]
            have hc : (p * rest.prod).coeff 0 = p.coeff 0 * rest.prod.coeff 0 := by
              rw [Polynomial.coeff_mul]
              simp
            have hz0 : v (rest.prod.coeff 0) = ((z 0 : ℤ) : WithTop ℤ) := by
              simpa using hPvert 0 (Nat.zero_le _)
            rw [hc, AddValuation.map_mul, hp0val, hz0]
            rfl
        | succ t' =>
            have ht' : t' ≤ dtail.length := Nat.le_of_succ_le_succ ht
            show v ((p * rest.prod).coeff (totalLength ((seg :: dtail).take (t' + 1)))) =
              ((zpN + z t' : ℤ) : WithTop ℤ)
            have hidx : totalLength ((seg :: dtail).take (t' + 1)) =
                seg.length + totalLength (dtail.take t') := by
              rw [List.take_succ_cons, totalLength_cons]
            rw [hidx]
            have hPX : v (rest.prod.coeff (totalLength (dtail.take t'))) =
                ((z t' : ℤ) : WithTop ℤ) := hPvert t' ht'
            have hpLeadCoeff : p.coeff seg.length = p.leadingCoeff := by
              rw [← hpseg.1, Polynomial.coeff_natDegree]
            have htargetVal : v (p.coeff seg.length *
                rest.prod.coeff (totalLength (dtail.take t'))) =
                ((zpN + z t' : ℤ) : WithTop ℤ) := by
              rw [AddValuation.map_mul, hpLeadCoeff, hpLeadval, hPX]
              rfl
            have htarget_mem : (seg.length, totalLength (dtail.take t')) ∈
                Finset.antidiagonal (seg.length + totalLength (dtail.take t')) := by
              simp
            have hstrict : ∀ x ∈ Finset.antidiagonal
                (seg.length + totalLength (dtail.take t')) \
                {(seg.length, totalLength (dtail.take t'))},
                v (p.coeff seg.length * rest.prod.coeff (totalLength (dtail.take t'))) <
                  v (p.coeff x.1 * rest.prod.coeff x.2) := by
              intro x hx
              rcases Finset.mem_sdiff.mp hx with ⟨hxanti, hxnot⟩
              have hxsum : x.1 + x.2 = seg.length + totalLength (dtail.take t') :=
                Finset.mem_antidiagonal.mp hxanti
              by_cases hterm : p.coeff x.1 * rest.prod.coeff x.2 = 0
              · rw [hterm, AddValuation.map_zero, htargetVal]
                exact WithTop.coe_lt_top _
              · have hpc : p.coeff x.1 ≠ 0 := by
                  intro h
                  exact hterm (by simp [h])
                have hPc : rest.prod.coeff x.2 ≠ 0 := by
                  intro h
                  exact hterm (by simp [h])
                have hx1le : x.1 ≤ seg.length := by
                  have h := Polynomial.le_natDegree_of_ne_zero hpc
                  rwa [hpseg.1] at h
                have hx2le : x.2 ≤ totalLength dtail := by
                  have h := Polynomial.le_natDegree_of_ne_zero hPc
                  rwa [hPdeg] at h
                have hxne : x ≠ (seg.length, totalLength (dtail.take t')) := by
                  intro h
                  exact hxnot (by simp [h])
                have hx1lt : x.1 < seg.length := by
                  rcases Nat.lt_or_ge x.1 seg.length with h | h
                  · exact h
                  · exfalso
                    have h1 : x.1 = seg.length := le_antisymm hx1le h
                    have h2 : x.2 = totalLength (dtail.take t') := by omega
                    exact hxne (Prod.ext h1 h2)
                have hx2gt : totalLength (dtail.take t') < x.2 := by omega
                have ht'lt : t' < dtail.length := by
                  by_contra hcon
                  have h1 : dtail.take t' = dtail :=
                    List.take_of_length_le (Nat.le_of_not_lt hcon)
                  rw [h1] at hx2gt
                  omega
                have hvzi : v (p.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
                  rw [AddValuation.ne_top_iff v]
                  exact hpc
                have hvzj : v (rest.prod.coeff x.2) ≠ (⊤ : WithTop ℤ) := by
                  rw [AddValuation.ne_top_iff v]
                  exact hPc
                obtain ⟨zi, hzi⟩ := WithTop.ne_top_iff_exists.mp hvzi
                obtain ⟨zj, hzj⟩ := WithTop.ne_top_iff_exists.mp hvzj
                have hziv : v (p.coeff x.1) = ((zi : ℤ) : WithTop ℤ) := hzi.symm
                have hzjv : v (rest.prod.coeff x.2) = ((zj : ℤ) : WithTop ℤ) := hzj.symm
                have hlow1 : (zp0 : ℝ) + (seg.slope : ℝ) * (x.1 : ℝ) ≤ (zi : ℝ) :=
                  hpline x.1 zi hpc hziv
                have hlow2 : (z t' : ℝ) + ((dtail[t']'ht'lt).slope : ℝ) *
                    ((x.2 : ℝ) - (totalLength (dtail.take t') : ℝ)) ≤ (zj : ℝ) :=
                  hPlower x.2 zj hPc hzjv t' ht'lt
                have hslt : (seg.slope : ℝ) < ((dtail[t']'ht'lt).slope : ℝ) := by
                  exact_mod_cast hheadlt t' ht'lt
                have hpEndR : (zp0 : ℝ) + (seg.length : ℝ) * (seg.slope : ℝ) = (zpN : ℝ) := by
                  exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hpEnd
                have hxsumR : (x.1 : ℝ) + (x.2 : ℝ) =
                    (seg.length : ℝ) + (totalLength (dtail.take t') : ℝ) := by
                  exact_mod_cast hxsum
                have hδpos : (0 : ℝ) < (x.2 : ℝ) - (totalLength (dtail.take t') : ℝ) := by
                  have h1 : (totalLength (dtail.take t') : ℝ) < (x.2 : ℝ) := by
                    exact_mod_cast hx2gt
                  linarith
                have hlow1' : (zp0 : ℝ) + (seg.slope : ℝ) *
                    ((seg.length : ℝ) - ((x.2 : ℝ) -
                      (totalLength (dtail.take t') : ℝ))) ≤ (zi : ℝ) := by
                  have hx1R : (x.1 : ℝ) = (seg.length : ℝ) -
                      ((x.2 : ℝ) - (totalLength (dtail.take t') : ℝ)) := by
                    linarith
                  rw [← hx1R]
                  exact hlow1
                have hzsumR : ((zpN : ℝ) + (z t' : ℝ)) < (zi : ℝ) + (zj : ℝ) := by
                  nlinarith [mul_pos (sub_pos.mpr hslt) hδpos, hlow1', hlow2, hpEndR]
                have hzsumInt : zpN + z t' < zi + zj := by
                  exact_mod_cast hzsumR
                have hzTop : ((zpN + z t' : ℤ) : WithTop ℤ) <
                    ((zi + zj : ℤ) : WithTop ℤ) := by
                  exact_mod_cast hzsumInt
                rw [htargetVal, AddValuation.map_mul, hziv, hzjv]
                convert hzTop using 1
            have hsumVal : v (∑ x ∈ Finset.antidiagonal
                (seg.length + totalLength (dtail.take t')),
                p.coeff x.1 * rest.prod.coeff x.2) =
                v (p.coeff seg.length *
                  rest.prod.coeff (totalLength (dtail.take t'))) := by
              have h := Valuation.map_sum_eq_of_lt (AddValuation.toValuation v)
                (s := Finset.antidiagonal (seg.length + totalLength (dtail.take t')))
                (f := fun x : ℕ × ℕ => p.coeff x.1 * rest.prod.coeff x.2)
                (j := (seg.length, totalLength (dtail.take t'))) htarget_mem
                (by
                  intro x hx
                  simpa [AddValuation.toValuation_apply] using hstrict x hx)
              simpa [AddValuation.toValuation_apply] using h
            rw [Polynomial.coeff_mul]
            exact hsumVal.trans htargetVal
      · intro t ht
        cases t with
        | zero =>
            show ((zpN + z 0 : ℤ) : ℚ) = ((zp0 + z 0 : ℤ) : ℚ) +
              (((seg :: dtail)[0]'ht).length : ℚ) * ((seg :: dtail)[0]'ht).slope
            have h0 : ((seg :: dtail)[0]'ht) = seg := rfl
            rw [h0]
            push_cast
            linarith [hpEnd]
        | succ t'' =>
            have ht'' : t'' < dtail.length := Nat.lt_of_succ_lt_succ ht
            show ((zpN + z (t'' + 1) : ℤ) : ℚ) = ((zpN + z t'' : ℤ) : ℚ) +
              (((seg :: dtail)[t'' + 1]'ht).length : ℚ) *
                ((seg :: dtail)[t'' + 1]'ht).slope
            have h1 : ((seg :: dtail)[t'' + 1]'ht) = dtail[t'']'ht'' := by
              simp
            rw [h1]
            have h2 := hPstep t'' ht''
            push_cast at h2 ⊢
            linarith
      · intro k zz hcoeff hval t ht
        cases t with
        | zero =>
            show ((zp0 + z 0 : ℤ) : ℝ) + (((seg :: dtail)[0]'ht).slope : ℝ) *
              ((k : ℝ) - (totalLength ((seg :: dtail).take 0) : ℝ)) ≤ (zz : ℝ)
            have h0 : ((seg :: dtail)[0]'ht) = seg := rfl
            have h0' : totalLength ((seg :: dtail).take 0) = 0 := rfl
            rw [h0, h0']
            by_contra hnotle
            have hnot : (zz : ℝ) < ((zp0 + z 0 : ℤ) : ℝ) + (seg.slope : ℝ) *
                ((k : ℝ) - ((0 : ℕ) : ℝ)) := lt_of_not_ge hnotle
            have hterms : ∀ x ∈ Finset.antidiagonal k,
                ((zz : ℤ) : WithTop ℤ) < v (p.coeff x.1 * rest.prod.coeff x.2) := by
              intro x hx
              have hxsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
              by_cases hterm : p.coeff x.1 * rest.prod.coeff x.2 = 0
              · rw [hterm, AddValuation.map_zero]
                exact WithTop.coe_lt_top _
              · have hpc : p.coeff x.1 ≠ 0 := by
                  intro h
                  exact hterm (by simp [h])
                have hPc : rest.prod.coeff x.2 ≠ 0 := by
                  intro h
                  exact hterm (by simp [h])
                have hvzi : v (p.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
                  rw [AddValuation.ne_top_iff v]
                  exact hpc
                have hvzj : v (rest.prod.coeff x.2) ≠ (⊤ : WithTop ℤ) := by
                  rw [AddValuation.ne_top_iff v]
                  exact hPc
                obtain ⟨zi, hzi⟩ := WithTop.ne_top_iff_exists.mp hvzi
                obtain ⟨zj, hzj⟩ := WithTop.ne_top_iff_exists.mp hvzj
                have hziv : v (p.coeff x.1) = ((zi : ℤ) : WithTop ℤ) := hzi.symm
                have hzjv : v (rest.prod.coeff x.2) = ((zj : ℤ) : WithTop ℤ) := hzj.symm
                have hlow1 : (zp0 : ℝ) + (seg.slope : ℝ) * (x.1 : ℝ) ≤ (zi : ℝ) :=
                  hpline x.1 zi hpc hziv
                have hlow2 : (z 0 : ℝ) + (seg.slope : ℝ) * (x.2 : ℝ) ≤ (zj : ℝ) := by
                  by_cases hlen : 0 < dtail.length
                  · have hb := hPlower x.2 zj hPc hzjv 0 hlen
                    have hX0 : totalLength (dtail.take 0) = 0 := rfl
                    rw [hX0] at hb
                    push_cast at hb
                    have hσ : seg.slope < (dtail[0]'hlen).slope := hheadlt 0 hlen
                    have hσR : (seg.slope : ℝ) ≤ ((dtail[0]'hlen).slope : ℝ) := by
                      exact_mod_cast le_of_lt hσ
                    have hx2nn : (0 : ℝ) ≤ (x.2 : ℝ) := by
                      exact_mod_cast Nat.zero_le x.2
                    have hmul := mul_le_mul_of_nonneg_right hσR hx2nn
                    linarith
                  · have hlen0 : dtail.length = 0 := Nat.eq_zero_of_not_pos hlen
                    have hdeg0 : rest.prod.natDegree = 0 := by
                      rw [hPdeg]
                      cases dtail with
                      | nil => rfl
                      | cons a l => simp at hlen0
                    have hx2z : x.2 = 0 := by
                      have h := Polynomial.le_natDegree_of_ne_zero hPc
                      omega
                    have hz0eq : zj = z 0 := by
                      have h1 : v (rest.prod.coeff 0) = ((z 0 : ℤ) : WithTop ℤ) := by
                        simpa using hPvert 0 (Nat.zero_le _)
                      rw [hx2z] at hzjv
                      rw [hzjv] at h1
                      exact_mod_cast h1
                    rw [hx2z, hz0eq]
                    simp
                have hxsumR : (x.1 : ℝ) + (x.2 : ℝ) = (k : ℝ) := by
                  exact_mod_cast hxsum
                have hsum_lower : ((zp0 : ℝ) + (z 0 : ℝ)) +
                    (seg.slope : ℝ) * (k : ℝ) ≤ (zi : ℝ) + (zj : ℝ) := by
                  have hsk : (seg.slope : ℝ) * (k : ℝ) =
                      (seg.slope : ℝ) * (x.1 : ℝ) + (seg.slope : ℝ) * (x.2 : ℝ) := by
                    rw [← hxsumR]
                    ring
                  linarith [hlow1, hlow2]
                have hzzlt : (zz : ℝ) < (zi : ℝ) + (zj : ℝ) := by
                  push_cast at hnot
                  linarith
                have hzzInt : zz < zi + zj := by
                  exact_mod_cast hzzlt
                have hzzTop : ((zz : ℤ) : WithTop ℤ) < ((zi + zj : ℤ) : WithTop ℤ) := by
                  exact_mod_cast hzzInt
                rw [AddValuation.map_mul, hziv, hzjv]
                convert hzzTop using 1
            have hsumstrict : ((zz : ℤ) : WithTop ℤ) <
                v (∑ x ∈ Finset.antidiagonal k, p.coeff x.1 * rest.prod.coeff x.2) := by
              apply AddValuation.map_lt_sum
              · simp
              · exact hterms
            rw [← Polynomial.coeff_mul, hval] at hsumstrict
            exact lt_irrefl _ hsumstrict
        | succ t'' =>
            have ht'' : t'' < dtail.length := Nat.lt_of_succ_lt_succ ht
            show ((zpN + z t'' : ℤ) : ℝ) + (((seg :: dtail)[t'' + 1]'ht).slope : ℝ) *
              ((k : ℝ) - (totalLength ((seg :: dtail).take (t'' + 1)) : ℝ)) ≤ (zz : ℝ)
            have hgt : ((seg :: dtail)[t'' + 1]'ht) = dtail[t'']'ht'' := by
              simp
            have hidx : totalLength ((seg :: dtail).take (t'' + 1)) =
                seg.length + totalLength (dtail.take t'') := by
              rw [List.take_succ_cons, totalLength_cons]
            rw [hgt, hidx]
            by_contra hnotle
            have hnot : (zz : ℝ) < ((zpN + z t'' : ℤ) : ℝ) +
                ((dtail[t'']'ht'').slope : ℝ) *
                ((k : ℝ) - ((seg.length + totalLength (dtail.take t'') : ℕ) : ℝ)) :=
              lt_of_not_ge hnotle
            have hterms : ∀ x ∈ Finset.antidiagonal k,
                ((zz : ℤ) : WithTop ℤ) < v (p.coeff x.1 * rest.prod.coeff x.2) := by
              intro x hx
              have hxsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
              by_cases hterm : p.coeff x.1 * rest.prod.coeff x.2 = 0
              · rw [hterm, AddValuation.map_zero]
                exact WithTop.coe_lt_top _
              · have hpc : p.coeff x.1 ≠ 0 := by
                  intro h
                  exact hterm (by simp [h])
                have hPc : rest.prod.coeff x.2 ≠ 0 := by
                  intro h
                  exact hterm (by simp [h])
                have hx1le : x.1 ≤ seg.length := by
                  have h := Polynomial.le_natDegree_of_ne_zero hpc
                  rwa [hpseg.1] at h
                have hvzi : v (p.coeff x.1) ≠ (⊤ : WithTop ℤ) := by
                  rw [AddValuation.ne_top_iff v]
                  exact hpc
                have hvzj : v (rest.prod.coeff x.2) ≠ (⊤ : WithTop ℤ) := by
                  rw [AddValuation.ne_top_iff v]
                  exact hPc
                obtain ⟨zi, hzi⟩ := WithTop.ne_top_iff_exists.mp hvzi
                obtain ⟨zj, hzj⟩ := WithTop.ne_top_iff_exists.mp hvzj
                have hziv : v (p.coeff x.1) = ((zi : ℤ) : WithTop ℤ) := hzi.symm
                have hzjv : v (rest.prod.coeff x.2) = ((zj : ℤ) : WithTop ℤ) := hzj.symm
                have hlow1 : (zp0 : ℝ) + (seg.slope : ℝ) * (x.1 : ℝ) ≤ (zi : ℝ) :=
                  hpline x.1 zi hpc hziv
                have hlow2 : (z t'' : ℝ) + ((dtail[t'']'ht'').slope : ℝ) *
                    ((x.2 : ℝ) - (totalLength (dtail.take t'') : ℝ)) ≤ (zj : ℝ) :=
                  hPlower x.2 zj hPc hzjv t'' ht''
                have hslt : (seg.slope : ℝ) < ((dtail[t'']'ht'').slope : ℝ) := by
                  exact_mod_cast hheadlt t'' ht''
                have hpEndR : (zp0 : ℝ) + (seg.length : ℝ) * (seg.slope : ℝ) =
                    (zpN : ℝ) := by
                  exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hpEnd
                have hx1leR : (x.1 : ℝ) ≤ (seg.length : ℝ) := by
                  exact_mod_cast hx1le
                have hx2R : (x.2 : ℝ) = (k : ℝ) - (x.1 : ℝ) := by
                  have hxsumR : (x.1 : ℝ) + (x.2 : ℝ) = (k : ℝ) := by
                    exact_mod_cast hxsum
                  linarith
                rw [hx2R] at hlow2
                have hkey : ((zpN : ℝ) + (z t'' : ℝ)) + ((dtail[t'']'ht'').slope : ℝ) *
                    ((k : ℝ) - (seg.length : ℝ) - (totalLength (dtail.take t'') : ℝ)) ≤
                    (zi : ℝ) + (zj : ℝ) := by
                  nlinarith [hlow1, hlow2, hpEndR,
                    mul_nonneg (sub_nonneg.mpr (le_of_lt hslt))
                      (sub_nonneg.mpr hx1leR)]
                have hzzlt : (zz : ℝ) < (zi : ℝ) + (zj : ℝ) := by
                  push_cast at hnot
                  linarith
                have hzzInt : zz < zi + zj := by
                  exact_mod_cast hzzlt
                have hzzTop : ((zz : ℤ) : WithTop ℤ) <
                    ((zi + zj : ℤ) : WithTop ℤ) := by
                  exact_mod_cast hzzInt
                rw [AddValuation.map_mul, hziv, hzjv]
                convert hzzTop using 1
            have hsumstrict : ((zz : ℤ) : WithTop ℤ) <
                v (∑ x ∈ Finset.antidiagonal k, p.coeff x.1 * rest.prod.coeff x.2) := by
              apply AddValuation.map_lt_sum
              · simp
              · exact hterms
            rw [← Polynomial.coeff_mul, hval] at hsumstrict
            exact lt_irrefl _ hsumstrict

private theorem npAssembly_product_pure_strict_slopes
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {factors : List K[X]} {data : NewtonPolygonData}
    (hne : data ≠ [])
    (hforall : List.Forall₂ (fun q seg => q.natDegree = seg.length ∧
        PureAt (v : K → WithTop ℤ) q seg.slope) factors data)
    (hinc : StrictlyIncreasingSlopes data) :
    HasNewtonPolygonData (v : K → WithTop ℤ) factors.prod data := by
  obtain ⟨hne0, hdeg, z, hvert, hstep, hlower⟩ :=
    npAssembly_product_vertex_and_lower hforall hinc
  exact npAssembly_polygon_of_vertices_and_lines hne hinc hdeg hvert hstep hlower

private theorem npAssembly_strictSlopes_map_div (d : ℕ) (hd : 0 < d) :
    ∀ data : NewtonPolygonData, StrictlyIncreasingSlopes data →
      StrictlyIncreasingSlopes (data.map (fun seg =>
        ({ length := seg.length * d,
           length_pos := Nat.mul_pos seg.length_pos hd,
           slope := seg.slope / (d : ℚ) } : SegmentData))) := by
  intro data
  induction data with
  | nil => intro _; trivial
  | cons a rest ih =>
      intro h
      cases rest with
      | nil => trivial
      | cons b rest' =>
          refine ⟨?_, ?_⟩
          · show a.slope / (d : ℚ) < b.slope / (d : ℚ)
            exact div_lt_div_of_pos_right h.1 (by exact_mod_cast hd)
          · exact ih h.2

private theorem npAssembly_main_stretch_strong
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {r : ℕ} {f g : K[X]} {data : NewtonPolygonData}
    (hne : data ≠ [])
    (hNP : HasNewtonPolygonData (v : K → WithTop ℤ) f data)
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos : ∀ seg ∈ data, (0 : ℝ) < (r : ℝ) + (seg.slope : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) (f.comp g)
      (data.map (fun seg =>
        ({ length := seg.length * g.natDegree,
           length_pos := Nat.mul_pos seg.length_pos (PrPure.natDegree_pos hg),
           slope := seg.slope / (g.natDegree : ℚ) } : SegmentData))) := by
  have hinc' : StrictlyIncreasingSlopes (data.map (fun seg =>
      ({ length := seg.length * g.natDegree,
         length_pos := Nat.mul_pos seg.length_pos (PrPure.natDegree_pos hg),
         slope := seg.slope / (g.natDegree : ℚ) } : SegmentData))) :=
    npAssembly_strictSlopes_map_div g.natDegree (PrPure.natDegree_pos hg) data
      (HasNewtonPolygonData.strictSlopes hNP)
  have hne' : (data.map (fun seg =>
      ({ length := seg.length * g.natDegree,
         length_pos := Nat.mul_pos seg.length_pos (PrPure.natDegree_pos hg),
         slope := seg.slope / (g.natDegree : ℚ) } : SegmentData))) ≠ [] := by
    intro h
    exact hne (List.map_eq_nil_iff.mp h)
  rcases blackbox_np_factor_by_segments hNP with ⟨factors, hprod, hforall⟩
  have hcompProd : f.comp g = (factors.map (fun q : K[X] => q.comp g)).prod := by
    rw [← hprod, Polynomial.list_prod_comp]
  have hforall' : List.Forall₂ (fun q seg => q.natDegree = seg.length ∧
      PureAt (v : K → WithTop ℤ) q seg.slope)
      (factors.map (fun q : K[X] => q.comp g))
      (data.map (fun seg =>
        ({ length := seg.length * g.natDegree,
           length_pos := Nat.mul_pos seg.length_pos (PrPure.natDegree_pos hg),
           slope := seg.slope / (g.natDegree : ℚ) } : SegmentData))) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    clear hprod hcompProd hNP hne hne' hinc'
    induction hforall with
    | nil => exact List.Forall₂.nil
    | @cons q seg qs segs hqseg htail ih =>
        refine List.Forall₂.cons ⟨?_, ?_⟩
          (ih (fun s hs => hpos s (List.mem_cons_of_mem _ hs)))
        · show (q.comp g).natDegree = seg.length * g.natDegree
          rw [Polynomial.natDegree_comp, hqseg.1]
        · show PureAt (v : K → WithTop ℤ) (q.comp g) (seg.slope / (g.natDegree : ℚ))
          exact pureAt_comp_prPure hqseg.2 hg (hpos seg (by simp))
  rw [hcompProd]
  exact npAssembly_product_pure_strict_slopes hne' hforall' hinc'

private theorem main_stretch_one_segment
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {r : ℕ} {f g : K[X]} {seg : SegmentData}
    (hNP : HasNewtonPolygonData (v : K → WithTop ℤ) f [seg])
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos : (0 : ℝ) < (r : ℝ) + (seg.slope : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) (f.comp g)
      [{ length := seg.length * g.natDegree,
         length_pos := Nat.mul_pos seg.length_pos (PrPure.natDegree_pos hg),
         slope := seg.slope / (g.natDegree : ℚ) }] := by
  have hdeg : f.natDegree = seg.length := by
    simpa [totalLength] using HasNewtonPolygonData.natDegree_eq_totalLength hNP
  have hfpos : 0 < f.natDegree := by
    rw [hdeg]
    exact seg.length_pos
  have hpure : PureAt (v : K → WithTop ℤ) f seg.slope := by
    refine ⟨hfpos, ?_⟩
    simpa [hdeg] using hNP
  have hcomp := pureAt_comp_prPure hpure hg hpos
  simpa [Polynomial.natDegree_comp, hdeg] using PureAt.hasNewtonPolygonData hcomp

private theorem main_stretch_two_segments
    {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {r : ℕ} {f g : K[X]} {seg₁ seg₂ : SegmentData}
    (hNP : HasNewtonPolygonData (v : K → WithTop ℤ) f [seg₁, seg₂])
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos₁ : (0 : ℝ) < (r : ℝ) + (seg₁.slope : ℝ))
    (hpos₂ : (0 : ℝ) < (r : ℝ) + (seg₂.slope : ℝ)) :
    HasNewtonPolygonData (v : K → WithTop ℤ) (f.comp g)
      [{ length := seg₁.length * g.natDegree,
         length_pos := Nat.mul_pos seg₁.length_pos (PrPure.natDegree_pos hg),
         slope := seg₁.slope / (g.natDegree : ℚ) },
       { length := seg₂.length * g.natDegree,
         length_pos := Nat.mul_pos seg₂.length_pos (PrPure.natDegree_pos hg),
         slope := seg₂.slope / (g.natDegree : ℚ) }] := by
  rcases blackbox_np_factor_by_segments hNP with ⟨factors, hprod, hforall⟩
  cases factors with
  | nil =>
      cases hforall
  | cons p rest =>
  cases rest with
  | nil =>
      cases hforall with
      | cons hpseg htail => cases htail
  | cons q rest =>
  cases rest with
  | nil =>
    cases hforall with
    | cons hpseg htail =>
    cases htail with
    | cons hqseg hnil =>
    have hfg : f.comp g = (p.comp g) * (q.comp g) := by
      rw [← hprod]
      rw [Polynomial.list_prod_comp]
      simp
    have hpcomp : PureAt (v : K → WithTop ℤ) (p.comp g)
        (seg₁.slope / (g.natDegree : ℚ)) :=
      pureAt_comp_prPure hpseg.2 hg hpos₁
    have hqcomp : PureAt (v : K → WithTop ℤ) (q.comp g)
        (seg₂.slope / (g.natDegree : ℚ)) :=
      pureAt_comp_prPure hqseg.2 hg hpos₂
    have hstrict : ((seg₁.slope / (g.natDegree : ℚ) : ℚ) : ℝ) <
        ((seg₂.slope / (g.natDegree : ℚ) : ℚ) : ℝ) := by
      have hslopes := HasNewtonPolygonData.strictSlopes hNP
      simp only [StrictlyIncreasingSlopes] at hslopes
      have hstrictQ : seg₁.slope / (g.natDegree : ℚ) <
          seg₂.slope / (g.natDegree : ℚ) :=
        div_lt_div_of_pos_right hslopes.1
          (by exact_mod_cast PrPure.natDegree_pos hg : (0 : ℚ) < g.natDegree)
      exact_mod_cast hstrictQ
    have hprodNP := product_two_pure_strict_slopes
      (v := v) (p := p.comp g) (q := q.comp g)
      (s1 := seg₁.slope / (g.natDegree : ℚ))
      (s2 := seg₂.slope / (g.natDegree : ℚ))
      hpcomp hqcomp hstrict
    rw [hfg]
    simpa [Polynomial.natDegree_comp, hpseg.1, hqseg.1] using hprodNP
  | cons extra rest =>
      cases hforall with
      | cons hpseg htail =>
      cases htail with
      | cons hqseg htail₂ => cases htail₂

example {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}
    {r : ℕ} {f g : K[X]} {data : NewtonPolygonData}
    (hne : data ≠ [])
    (hNP : HasNewtonPolygonData (v : K → WithTop ℤ) f data)
    (hg : PrPure (v : K → WithTop ℤ) r g)
    (hpos : ∀ seg ∈ data, (0 : ℝ) < (r : ℝ) + (seg.slope : ℝ)) :
    ∃ data' : NewtonPolygonData,
      HasNewtonPolygonData (v : K → WithTop ℤ) (f.comp g) data' ∧
      data'.length = data.length ∧
      data'.map (fun seg => seg.slope) =
        data.map (fun seg => seg.slope / (g.natDegree : ℚ)) := by
  refine ⟨_, npAssembly_main_stretch_strong hne hNP hg hpos, ?_, ?_⟩
  · rw [List.length_map]
  · rw [List.map_map]
    rfl

end QwenModels
