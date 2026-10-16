module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

@[expose] public section

open SimpleGraph Matrix Finset BigOperators

noncomputable section

set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Edge := G.edgeSet

/-- Directed adjacency summand: `w_{ab}` if `a ~ b`, else 0. -/
def adjWeight (w : Edge G → ℝ) (a b : V) : ℝ :=
  if h : G.Adj a b then w ⟨s(a, b), h⟩ else 0

/-- The weighted Laplacian, direct definition. -/
def weightedLapMatrix (w : Edge G → ℝ) : Matrix V V ℝ :=
  fun a b =>
    if h : G.Adj a b then -w ⟨s(a, b), h⟩
    else if a = b then ∑ c : V, adjWeight G w a c
    else 0

/-- The quadratic form is twice the edge sum. -/
lemma weightedLapMatrix_quadForm (w : Edge G → ℝ) (x : V → ℝ) :
    dotProduct x ((weightedLapMatrix G w).mulVec x) =
    ∑ a : V, ∑ b : V, adjWeight G w a b * (x a - x b)^2 := by
  simp only [dotProduct, Matrix.mulVec, weightedLapMatrix, adjWeight]
  simp only [Finset.mul_sum, Finset.sum_mul]
  sorry

end
