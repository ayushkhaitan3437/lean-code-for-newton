import QwenModels.NewtonPolygon

namespace QwenModels

open Polynomial

def PureAt {K : Type*} [Semiring K]
    (ord : K → WithTop ℤ) (f : K[X]) (slope : ℚ) : Prop :=
  ∃ hdeg : 0 < f.natDegree,
    HasNewtonPolygonData ord f
      [{ length := f.natDegree, length_pos := hdeg, slope := slope }]

def prPureSlope (r degree : ℕ) : ℚ :=
  - (r : ℚ) / (degree : ℚ)

def PrPure {K : Type*} [Semiring K]
    (ord : K → WithTop ℤ) (r : ℕ) (f : K[X]) : Prop :=
  0 < r ∧
    ∃ _ : 0 < f.natDegree,
      ord (f.coeff 0) = (((r : ℤ) : WithTop ℤ)) ∧
      ord f.leadingCoeff = (((0 : ℤ) : WithTop ℤ)) ∧
      PureAt ord f (prPureSlope r f.natDegree)

namespace PureAt

theorem natDegree_pos {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {f : K[X]} {slope : ℚ} (h : PureAt ord f slope) : 0 < f.natDegree :=
  h.choose

theorem hasNewtonPolygonData {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {f : K[X]} {slope : ℚ} (h : PureAt ord f slope) :
    HasNewtonPolygonData ord f
      [{ length := f.natDegree, length_pos := h.choose, slope := slope }] :=
  h.choose_spec

end PureAt

namespace PrPure

theorem r_pos {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {r : ℕ} {f : K[X]} (h : PrPure ord r f) : 0 < r :=
  h.1

theorem natDegree_pos {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {r : ℕ} {f : K[X]} (h : PrPure ord r f) : 0 < f.natDegree :=
  h.2.choose

theorem coeff_zero_valuation {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {r : ℕ} {f : K[X]} (h : PrPure ord r f) :
    ord (f.coeff 0) = (((r : ℤ) : WithTop ℤ)) :=
  h.2.choose_spec.1

theorem leadingCoeff_valuation {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {r : ℕ} {f : K[X]} (h : PrPure ord r f) :
    ord f.leadingCoeff = (((0 : ℤ) : WithTop ℤ)) :=
  h.2.choose_spec.2.1

theorem pureAt {K : Type*} [Semiring K] {ord : K → WithTop ℤ}
    {r : ℕ} {f : K[X]} (h : PrPure ord r f) :
    PureAt ord f (prPureSlope r f.natDegree) :=
  h.2.choose_spec.2.2

end PrPure

end QwenModels
