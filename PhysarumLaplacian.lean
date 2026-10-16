module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

open SimpleGraph Matrix Finset BigOperators

noncomputable section

set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]

abbrev Edge := G.edgeSet

def weightedIncMatrix (w : Edge G → ℝ) : Matrix V (Sym2 V) ℝ :=
  G.incMatrix ℝ * diagonal (fun e : Sym2 V =>
    (if h : e ∈ G.edgeSet then Real.sqrt (w ⟨e, h⟩) else 0 : ℝ))

def weightedLapMatrix (w : Edge G → ℝ) : Matrix V V ℝ :=
  weightedIncMatrix G w * (weightedIncMatrix G w)ᵀ

omit [G.LocallyFinite] in
theorem weightedLapMatrix_posSemidef (w : Edge G → ℝ) :
    (weightedLapMatrix G w).PosSemidef := by
  unfold weightedLapMatrix
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- If `x` is equal on adjacent vertices, `x` is constant along any walk. -/
lemma x_eq_along_walk (x : V → ℝ) (h : ∀ {a b : V}, G.Adj a b → x a = x b)
    {u v : V} (p : G.Walk u v) : x u = x v := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h hadj).trans ih

/-- If `x` is equal on every adjacent pair, `x` is constant on connected `G`. -/
lemma constant_of_adj_eq (hconn : G.Connected) (x : V → ℝ)
    (h : ∀ {a b : V}, G.Adj a b → x a = x b) :
    ∃ c : ℝ, ∀ v, x v = c := by
  haveI : Nonempty V := hconn.nonempty
  let v₀ : V := Classical.arbitrary V
  refine ⟨x v₀, fun v => ?_⟩
  obtain ⟨p⟩ : Nonempty (G.Walk v₀ v) := hconn.preconnected v₀ v
  exact (x_eq_along_walk (G := G) (x := x) h p).symm

def reducedLapMatrix (sink : V) (w : Edge G → ℝ) :
    Matrix {v // v ≠ sink} {v // v ≠ sink} ℝ :=
  (weightedLapMatrix G w).submatrix (fun v => v.val) (fun v => v.val)

theorem reducedLaplacian_posDef (sink : V) (L : Edge G → ℝ) (hL : ∀ e, 0 < L e)
    (D : Edge G → ℝ) (hD : ∀ e, 0 < D e) (hconn : G.Connected) :
    (reducedLapMatrix G sink (fun e => D e / L e)).PosDef := by
  let w : Edge G → ℝ := fun e => D e / L e
  have hw : ∀ e, 0 < w e := fun e => div_pos (hD e) (hL e)
  have h_psd := weightedLapMatrix_posSemidef G w
  have h_herm : (reducedLapMatrix G sink w).IsHermitian := by
    show ((weightedLapMatrix G w).submatrix
            (fun (v : {v // v ≠ sink}) => v.val)
            (fun (v : {v // v ≠ sink}) => v.val)).IsHermitian
    exact Matrix.IsHermitian.submatrix h_psd.1
            (fun (v : {v // v ≠ sink}) => v.val)
  refine ⟨h_herm, ?_⟩
  intro x hx
  -- x is nonzero on the reduced space
  -- Show xᵀ (reduced L) x > 0
  by_contra h_nonpos
  push_neg at h_nonpos
  -- Extend x to V by setting sink = 0
  let x' : V → ℝ := fun v => if h : v = sink then 0 else x ⟨v, h⟩
  -- x'ᵀ L x' = xᵀ L_reduced x, which is ≤ 0
  -- But x'ᵀ L x' = ‖M_wᵀ x'‖² ≥ 0
  -- So x'ᵀ L x' = 0
  -- Hence x' is constant on G, and since x' sink = 0, x' = 0
  -- Hence x = 0, contradicting hx
  sorry

end
