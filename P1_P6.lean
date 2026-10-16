module

public import LeanGO.Algorithm
public import LeanGO.Examples.Decision
public import LeanGO.Examples.PRS

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace P1_P6

/-! ## Shared infrastructure -/

def last {α : Type*} {n : ℕ} (u : Iic n → α) : α := u ⟨n, mem_Iic.mpr le_rfl⟩

@[fun_prop]
lemma measurable_last {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (fun u : Iic n → α => last u) :=
  measurable_pi_apply _

/-! ## Typeclass context — copied from LIPO -/

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]
variable {β : Type*} [MeasurableSpace β]

/-! ## P2 -/

noncomputable def P2 (μ : Measure α) [IsProbabilityMeasure μ] : Algorithm α β where
  ν := μ
  kernel_iter _ := Kernel.const _ μ

/-! ## P1 -/

variable (μ : Measure α) [IsProbabilityMeasure μ]
variable (grad_step : α → α) (hgrad : Measurable grad_step)

noncomputable def P1 : Algorithm α β where
  ν := μ
  kernel_iter n :=
    Kernel.deterministic
      (fun data : prod_iter_image α β n => grad_step (last data.1))
      (hgrad.comp (by fun_prop))

/-! ## P3 -/

variable (fitness : α → ℝ) (threshold : ℝ)

def selection_set (n : ℕ) (data : prod_iter_image α ℝ n) : Set α :=
  {_x | fitness (last data.1) < threshold}

omit [PseudoMetricSpace α] [BorelSpace α] [SecondCountableTopology α] in
lemma measurableSet_selection_prod (hfitness : Measurable fitness) :
    ∀ n, MeasurableSet
      {p : prod_iter_image α ℝ n × α | p.2 ∈ selection_set fitness threshold n p.1} := by
  intro n
  have h_meas : Measurable (fun p : prod_iter_image α ℝ n × α => fitness (last p.1.1)) :=
    hfitness.comp (by fun_prop)
  have h_set :
      {p : prod_iter_image α ℝ n × α | p.2 ∈ selection_set fitness threshold n p.1}
      = (fun p : prod_iter_image α ℝ n × α => fitness (last p.1.1)) ⁻¹' Set.Iio threshold :=
    rfl
  rw [h_set]
  exact measurableSet_Iio.preimage h_meas

variable (hfitness : Measurable fitness)
variable (h3 : ∀ n (data : prod_iter_image α ℝ n),
  μ (selection_set fitness threshold n data) ≠ 0)

noncomputable def P3 : Algorithm α ℝ :=
  Decision μ (decision := selection_set fitness threshold)
    (measurableSet_selection_prod fitness threshold hfitness) h3

/-! ## P4 — Memory reinforcement (LIPO-shaped) -/

variable (decay : ℝ)

def pheromone_set (n : ℕ) (data : prod_iter_image α ℝ n) : Set α :=
  {x | Tuple.max (fun i => data.2 i) ≤
       Tuple.min (fun i => data.2 i + decay * dist (data.1 i) x)}

lemma measurableSet_pheromone_prod :
    ∀ n, MeasurableSet
      {p : (prod_iter_image α ℝ n) × α | p.2 ∈ pheromone_set decay n p.1} := by
  intro n
  unfold pheromone_set
  simp only [Set.mem_ofPred_eq, measurableSet_setOfPred]
  refine Measurable.le' ?_ ?_
  · fun_prop
  · fun_prop

variable (h4 : ∀ n (data : prod_iter_image α ℝ n),
  μ (pheromone_set decay n data) ≠ 0)

noncomputable def P4 : Algorithm α ℝ :=
  Decision μ (fun n => measurableSet_pheromone_prod decay n) h4


/-! ## P5 — Threshold trigger (real line, parameterized by a probability measure). -/

variable (θ : ℝ) (μR : Measure ℝ) [IsProbabilityMeasure μR]

def threshold_set (n : ℕ) (_ : prod_iter_image ℝ ℝ n) : Set ℝ :=
  Set.Ioi θ

lemma measurableSet_threshold_prod :
    ∀ n, MeasurableSet
      {p : prod_iter_image ℝ ℝ n × ℝ | p.2 ∈ threshold_set θ n p.1} := by
  intro n
  unfold threshold_set
  have h : {p : prod_iter_image ℝ ℝ n × ℝ | p.2 ∈ Set.Ioi θ}
         = (fun p : prod_iter_image ℝ ℝ n × ℝ => p.2) ⁻¹' Set.Ioi θ := rfl
  rw [h]
  exact measurable_snd measurableSet_Ioi

variable (h5 : ∀ n (data : prod_iter_image ℝ ℝ n),
  μR (threshold_set θ n data) ≠ 0)

noncomputable def P5 : Algorithm ℝ ℝ :=
  Decision μR (fun n => measurableSet_threshold_prod θ n) h5

/-! ## P6 — Coupled synchrony (deterministic mean-field on ℝ). -/

variable (kuramoto_step : ℝ → ℝ → ℝ)
  (hkuramoto : Measurable (fun p : ℝ × ℝ => kuramoto_step p.1 p.2))

noncomputable def P6 (μR : Measure ℝ) [IsProbabilityMeasure μR] : Algorithm ℝ ℝ where
  ν := μR
  kernel_iter n :=
    Kernel.deterministic
      (fun data : prod_iter_image ℝ ℝ n =>
        kuramoto_step (last data.1)
          ((Finset.univ.sum (fun i : Iic n => data.2 i)) / ((n : ℝ) + 1)))
      (by
        change Measurable ((fun p : ℝ × ℝ => kuramoto_step p.1 p.2) ∘
          (fun data : prod_iter_image ℝ ℝ n =>
            (last data.1,
             (Finset.univ.sum (fun i : Iic n => data.2 i)) / ((n : ℝ) + 1))))
        exact hkuramoto.comp (by
          refine Measurable.prodMk ?_ ?_
          · fun_prop
          · refine Measurable.div_const ?_ _
            exact Finset.measurable_sum _ (fun i _ => by fun_prop)))

end P1_P6
