import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

namespace QwenModels

open Polynomial

/-!
Data-level Newton polygon infrastructure.

Mathlib in this checkout has convex hulls and polynomial coefficients, but no
Newton polygon API.  The definitions below use an abstract additive valuation
`ord : K -> WithTop Int`, matching the paper's `ord_p : Q_p -> Z union {infty}`.
-/

structure SegmentData where
  length : ℕ
  length_pos : 0 < length
  slope : ℚ

namespace SegmentData

theorem length_ne_zero (seg : SegmentData) : seg.length ≠ 0 :=
  Nat.ne_of_gt seg.length_pos

def nextVertex (seg : SegmentData) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + (seg.length : ℝ), p.2 + (seg.length : ℝ) * (seg.slope : ℝ))

end SegmentData

abbrev NewtonPolygonData := List SegmentData

def totalLength : NewtonPolygonData → ℕ
  | [] => 0
  | seg :: rest => seg.length + totalLength rest

@[simp]
theorem totalLength_nil : totalLength [] = 0 := rfl

@[simp]
theorem totalLength_cons (seg : SegmentData) (rest : NewtonPolygonData) :
    totalLength (seg :: rest) = seg.length + totalLength rest := rfl

@[simp]
theorem totalLength_singleton (seg : SegmentData) :
    totalLength [seg] = seg.length := by
  simp [totalLength]

def StrictlyIncreasingSlopes : NewtonPolygonData → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a.slope < b.slope ∧ StrictlyIncreasingSlopes (b :: rest)

@[simp]
theorem StrictlyIncreasingSlopes.nil : StrictlyIncreasingSlopes [] := trivial

@[simp]
theorem StrictlyIncreasingSlopes.singleton (seg : SegmentData) :
    StrictlyIncreasingSlopes [seg] := trivial

def lowerConvexEpigraph (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q | ∃ p ∈ (convexHull ℝ) S, p.1 = q.1 ∧ p.2 ≤ q.2}

theorem subset_lowerConvexEpigraph (S : Set (ℝ × ℝ)) :
    S ⊆ lowerConvexEpigraph S := by
  intro p hp
  exact ⟨p, subset_convexHull ℝ S hp, rfl, le_rfl⟩

theorem lowerConvexEpigraph_mono {S T : Set (ℝ × ℝ)}
    (hST : S ⊆ T) : lowerConvexEpigraph S ⊆ lowerConvexEpigraph T := by
  intro q hq
  rcases hq with ⟨p, hp, hpx, hpy⟩
  exact ⟨p, convexHull_mono hST hp, hpx, hpy⟩

theorem lowerConvexEpigraph_upward {S : Set (ℝ × ℝ)} {p q : ℝ × ℝ}
    (hp : p ∈ lowerConvexEpigraph S) (hx : q.1 = p.1) (hy : p.2 ≤ q.2) :
    q ∈ lowerConvexEpigraph S := by
  rcases hp with ⟨c, hc, hcx, hcy⟩
  refine ⟨c, hc, ?_, le_trans hcy hy⟩
  rw [hcx, ← hx]

def coefficientSupportPoints {K : Type*} [Semiring K]
    (ord : K → WithTop ℤ) (f : K[X]) : Set (ℝ × ℝ) :=
  {pt | ∃ i z, i ≤ f.natDegree ∧ f.coeff i ≠ 0 ∧
    ord (f.coeff i) = ((z : ℤ) : WithTop ℤ) ∧ pt = ((i : ℝ), (z : ℝ))}

def newtonPolygon {K : Type*} [Semiring K]
    (ord : K → WithTop ℤ) (f : K[X]) : Set (ℝ × ℝ) :=
  lowerConvexEpigraph (coefficientSupportPoints ord f)

theorem coefficientSupport_subset_newtonPolygon {K : Type*} [Semiring K]
    (ord : K → WithTop ℤ) (f : K[X]) :
    coefficientSupportPoints ord f ⊆ newtonPolygon ord f :=
  subset_lowerConvexEpigraph _

def verticesFrom : ℝ × ℝ → NewtonPolygonData → List (ℝ × ℝ)
  | p, [] => [p]
  | p, seg :: rest => p :: verticesFrom (seg.nextVertex p) rest

theorem self_mem_verticesFrom (p : ℝ × ℝ) (data : NewtonPolygonData) :
    p ∈ verticesFrom p data := by
  cases data <;> simp [verticesFrom]

@[simp]
theorem verticesFrom_nil (p : ℝ × ℝ) : verticesFrom p [] = [p] := rfl

@[simp]
theorem verticesFrom_cons (p : ℝ × ℝ) (seg : SegmentData) (rest : NewtonPolygonData) :
    verticesFrom p (seg :: rest) = p :: verticesFrom (seg.nextVertex p) rest := rfl

def verticesSet (startHeight : ℚ) (data : NewtonPolygonData) : Set (ℝ × ℝ) :=
  {p | p ∈ verticesFrom ((0 : ℝ), (startHeight : ℝ)) data}

def polygonEpigraph (startHeight : ℚ) (data : NewtonPolygonData) : Set (ℝ × ℝ) :=
  lowerConvexEpigraph (verticesSet startHeight data)

theorem verticesSet_subset_polygonEpigraph (startHeight : ℚ) (data : NewtonPolygonData) :
    verticesSet startHeight data ⊆ polygonEpigraph startHeight data :=
  subset_lowerConvexEpigraph _

theorem start_mem_verticesSet (startHeight : ℚ) (data : NewtonPolygonData) :
    ((0 : ℝ), (startHeight : ℝ)) ∈ verticesSet startHeight data :=
  self_mem_verticesFrom _ data

theorem start_mem_polygonEpigraph (startHeight : ℚ) (data : NewtonPolygonData) :
    ((0 : ℝ), (startHeight : ℝ)) ∈ polygonEpigraph startHeight data :=
  verticesSet_subset_polygonEpigraph startHeight data (start_mem_verticesSet startHeight data)

def HasNewtonPolygonData {K : Type*} [Semiring K]
    (ord : K → WithTop ℤ) (f : K[X]) (data : NewtonPolygonData) : Prop :=
  StrictlyIncreasingSlopes data ∧
    f.natDegree = totalLength data ∧
    ∃ startHeight : ℚ, newtonPolygon ord f = polygonEpigraph startHeight data

theorem HasNewtonPolygonData.strictSlopes {K : Type*} [Semiring K]
    {ord : K → WithTop ℤ} {f : K[X]} {data : NewtonPolygonData}
    (h : HasNewtonPolygonData ord f data) : StrictlyIncreasingSlopes data :=
  h.1

theorem HasNewtonPolygonData.natDegree_eq_totalLength {K : Type*} [Semiring K]
    {ord : K → WithTop ℤ} {f : K[X]} {data : NewtonPolygonData}
    (h : HasNewtonPolygonData ord f data) : f.natDegree = totalLength data :=
  h.2.1

theorem HasNewtonPolygonData.exists_startHeight {K : Type*} [Semiring K]
    {ord : K → WithTop ℤ} {f : K[X]} {data : NewtonPolygonData}
    (h : HasNewtonPolygonData ord f data) :
    ∃ startHeight : ℚ, newtonPolygon ord f = polygonEpigraph startHeight data :=
  h.2.2

end QwenModels
