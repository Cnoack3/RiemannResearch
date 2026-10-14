/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Probability.DeterminantalPoissonLimit
import RiemannResearch.Probability.ProbabilityGeneratingCoefficients
import Mathlib.Tactic.Ring

/-!
# Conditional Poisson limits for actual finite-window counts

Source: the previously verified finite DPP law and spectral PGF identities,
combined with the elementary coefficient-continuity theorem. The hypotheses
are convergence of the trace and vanishing full squared kernel mass; no
arithmetic provider or zeta connection is asserted in this module.
-/

noncomputable section
open Filter Matrix MeasureTheory
open scoped BigOperators Topology Classical

namespace RiemannResearch.Probability.DPP

theorem realPGF_finite_count_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hp : ∀ S, 0 ≤ exactWeight Q S)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    realPGF (fun k => (((finiteLaw Q hp).map Finset.card) k).toReal) z =
      (1 + (z - 1) • Q).det := by
  rw [realPGF_map_finite (finiteLaw Q hp) Finset.card hz]
  have he : (∑ S : Finset ι, ((finiteLaw Q hp) S).toReal * z ^ S.card) =
      ∑ S : Finset ι, z ^ S.card * ((finiteLaw Q hp) S).toReal := by
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [he, finiteLaw_count_generating]
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- Every exact count probability converges to its Poisson value, in arbitrary
moving dimensions, from the trace and full squared kernel mass alone. -/
theorem moving_finite_dpp_count_tendsto_poisson
    (d : ℕ → ℕ) (Q : (N : ℕ) → Matrix (Fin (d N)) (Fin (d N)) ℝ)
    (hQ : ∀ N, (Q N).PosSemidef) (hI : ∀ N, (1 - Q N).PosSemidef)
    (rate : ℝ)
    (h1 : Tendsto (fun N => (Q N).trace) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, ∑ j, Q N i j ^ 2) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N => (((finiteLaw (Q N) (exactWeight_nonneg _ (hQ N) (hI N))).map
      Finset.card) k).toReal) atTop
      (𝓝 (Real.exp (-rate) * rate ^ k / k.factorial)) := by
  have hr : 0 ≤ rate := le_of_tendsto_of_tendsto tendsto_const_nhds h1
    (Filter.Eventually.of_forall (fun N =>
      Finset.sum_nonneg (fun i _ => (hQ N).diag_nonneg (i := i))))
  apply count_mass_tendsto_poisson_of_pgf _ rate hr
    (fun N j => ENNReal.toReal_nonneg) (fun N => pmf_hasSum_real _) _ k
  intro z hz
  have hh := moving_matrix_pgf_tendsto_poisson d Q hQ rate z h1 h2 ⟨hz.1.le, hz.2.le⟩
  apply hh.congr
  intro N
  symm
  exact realPGF_finite_count_eq_det (Q N) (exactWeight_nonneg _ (hQ N) (hI N))
    ⟨hz.1.le, hz.2.le⟩

/-- An actual finite spatial count has exactly the finite-kernel count mass. -/
theorem IsDPP.window_count_mass_eq_finite
    {ι α Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Set α} {K : α → α → ℝ}
    (h : IsDPP μ X K) (e : ι ↪ α)
    (hQ : (Matrix.of (fun i j : ι => K (e i) (e j))).PosSemidef)
    (hI : (1 - Matrix.of (fun i j : ι => K (e i) (e j))).PosSemidef) (k : ℕ) :
    μ.real {ω | (Finset.univ.filter (fun i => e i ∈ X ω)).card = k} =
      (((finiteLaw (Matrix.of (fun i j : ι => K (e i) (e j)))
        (exactWeight_nonneg _ hQ hI)).map Finset.card) k).toReal := by
  rw [finiteLaw_count_eq_bernoulliSubset_count _ hQ hI]
  have hl := h.window_count_law_eq_bernoulli e hQ hI
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  let c : (ι → Bool) → ℕ := fun x => (Finset.univ.filter (fun i => x i = true)).card
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  have hc : Measurable c := measurable_of_finite c
  have hm : Measurable (fun ω => (Finset.univ.filter (fun i => e i ∈ X ω)).card) := by
    simpa [c, r, Function.comp_def] using hc.comp hr
  have hv := congrArg (fun ν : Measure ℕ => (ν {k}).toReal) hl
  rw [Measure.map_apply hm (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at hv
  have he : (fun ω => (Finset.univ.filter (fun i => e i ∈ X ω)).card) ⁻¹' {k} =
      {ω | (Finset.univ.filter (fun i => e i ∈ X ω)).card = k} := by
    ext ω
    simp
  rw [he] at hv
  exact hv

/-- Conditional Poisson counting limit for the actual DPP, at every count. -/
theorem moving_window_count_mass_tendsto_poisson
    {α Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ N, IsProbabilityMeasure (μ N)]
    (X : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ)
    (h : ∀ N, IsDPP (μ N) (X N) (K N))
    (d : ℕ → ℕ) (e : (N : ℕ) → Fin (d N) ↪ α)
    (hQ : ∀ N, (Matrix.of (fun i j => K N (e N i) (e N j))).PosSemidef)
    (hI : ∀ N, (1 - Matrix.of (fun i j => K N (e N i) (e N j))).PosSemidef)
    (rate : ℝ)
    (h1 : Tendsto (fun N => ∑ i, K N (e N i) (e N i)) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, ∑ j, K N (e N i) (e N j) ^ 2) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N => (μ N).real
      {ω | (Finset.univ.filter (fun i => e N i ∈ X N ω)).card = k})
      atTop (𝓝 (Real.exp (-rate) * rate ^ k / k.factorial)) := by
  have hh := moving_finite_dpp_count_tendsto_poisson d
    (fun N => Matrix.of (fun i j => K N (e N i) (e N j))) hQ hI rate h1 h2 k
  apply hh.congr
  intro N
  symm
  exact (h N).window_count_mass_eq_finite (e N) (hQ N) (hI N) k

end RiemannResearch.Probability.DPP
