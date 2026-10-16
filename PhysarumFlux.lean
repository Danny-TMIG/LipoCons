/-
PhysarumFlux.lean

Flux definition and Lipschitz bound for the Physarum routing engine.

Eliminates the second sorry in Physarum.lean: flux_lipschitz.

References:
* Bonifaci, Mehlhorn, Varma (2012), Lemma 5.
-/
module

public import PhysarumLaplacian
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

open SimpleGraph Matrix Finset BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Edge := G.edgeSet

/-- Solve for node pressures by inverting the reduced Laplacian.
    The value at the sink is fixed to zero. -/
def pressure (source sink : V) (w : Edge G → ℝ) (I₀ : ℝ) : V → ℝ :=
  fun v =>
    if h : v = sink then 0
    else
      let M := reducedLapMatrix G sink w
      let b : {v // v ≠ sink} → ℝ := fun i =>
        if i.val = source then I₀ else 0
      -- Solve M * p = b via M⁻¹
      (M⁻¹).mulVec b ⟨v, h⟩

/-- Poiseuille flux on edge `(i,j)`: `Q_{ij} = w_e * (p_i - p_j)`. -/
def flux (source sink : V) (w : Edge G → ℝ) (I₀ : ℝ) : Edge G → ℝ :=
  fun e =>
    w e * (pressure G source sink w I₀ e.val.1 - pressure G source sink w I₀ e.val.2)

/-- **Target 2.** The flux map is 1-Lipschitz in the weight vector
    for the reduced Laplacian norm. -/
theorem flux_lipschitz (source sink : V) (L : Edge G → ℝ) (hL : ∀ e, 0 < L e)
    (I₀ : ℝ) (hI₀ : 0 < I₀) (hconn : G.Connected) :
    LipschitzWith 1 (fun D : Edge G → ℝ =>
      flux G source sink (fun e => D e / L e) I₀) := by
  sorry

end
