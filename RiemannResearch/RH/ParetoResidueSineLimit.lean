import RiemannResearch.RH.ParetoResidueMicroscopicGram
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sine-kernel limits of the grouped Pareto Gram

Source: the user's Ramanujan/DPP research agenda and the existing quantitative
microscopic Gram theorem. The finite-dimensional determinant argument is
continuity plus cancellation of the exponential row and column factors.

The comparison kernel sin(pi (x-y))/(pi (x-y)), with diagonal one, is the
standard sine-process correlation kernel. For the probabilistic interpretation,
see Arias de Reyna--Rodgers, arXiv:2311.13441, Section 5.1, and Soshnikov,
arXiv:math/0002099, Sections 2 and 3. Those references supply terminology and
context; no probabilistic assertion from them is assumed in these proofs.

These are determinants of grouped observation Gram matrices. They are not
identified here with the correlation functions of the separate Mellin sampling
law or the empirical zeta-zero process. The fixed-center theorem has no RH or
zero-location hypothesis. Moving centers retain the explicit error condition.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

theorem logPhaseKernel_sub_gauge (x y : ℝ) :
    logPhaseKernel (x - y) =
      Complex.exp (-((x : ℂ) / 2) * Complex.I) *
        (Complex.exp ((y : ℂ) / 2 * Complex.I) *
          (Real.sinc ((x - y) / 2) : ℂ)) := by
  unfold logPhaseKernel
  have he : -(((x - y : ℝ) : ℂ) / 2) * Complex.I =
      -((x : ℂ) / 2) * Complex.I + (y : ℂ) / 2 * Complex.I := by
    rw [Complex.ofReal_sub]
    ring
  rw [he, Complex.exp_add, mul_assoc]

theorem logPhaseKernel_det_eq_sinc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) :
    Matrix.det (fun i j => logPhaseKernel (x i - x j)) =
      Matrix.det (fun i j => (Real.sinc ((x i - x j) / 2) : ℂ)) := by
  let a : ι → ℂ := fun i => Complex.exp (-((x i : ℂ) / 2) * Complex.I)
  let b : ι → ℂ := fun i => Complex.exp ((x i : ℂ) / 2 * Complex.I)
  let S : Matrix ι ι ℂ := fun i j => (Real.sinc ((x i - x j) / 2) : ℂ)
  have hab (i : ι) : a i * b i = 1 := by
    dsimp only [a, b]
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  have hmatrix : (fun i j => logPhaseKernel (x i - x j)) =
      Matrix.of (fun i j => a i * (Matrix.of (fun k l => b l * S k l)) i j) := by
    funext i j
    exact logPhaseKernel_sub_gauge (x i) (x j)
  rw [hmatrix, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  simp only [hab, Finset.prod_const_one, one_mul]
  rfl

theorem logPhaseKernel_scaled_det_eq_sine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) :
    Matrix.det (fun i j => logPhaseKernel (2 * Real.pi * (x i - x j))) =
      Matrix.det (fun i j => (Real.sinc (Real.pi * (x i - x j)) : ℂ)) := by
  have hgap (a b : ℝ) : 2 * Real.pi * a - 2 * Real.pi * b =
      2 * Real.pi * (a - b) := by ring
  have hhalf (a b : ℝ) : (2 * Real.pi * (a - b)) / 2 =
      Real.pi * (a - b) := by ring
  simpa only [hgap, hhalf] using
    logPhaseKernel_det_eq_sinc (fun i => 2 * Real.pi * x i)

end RiemannResearch.RH.Pareto.SpectralObstruction

namespace RiemannResearch.RH.Pareto.ResidueMellin
open SpectralObstruction

theorem phaseStrippedCross_det_microscopic_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ → ℕ) (t : ℕ → ι → ℝ) (x : ι → ℝ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (hx : ∀ i k, Tendsto
      (fun j => (t j i - t j k) * Real.log ((N j : ℝ) + 1))
      atTop (𝓝 (2 * Real.pi * (x i - x k))))
    (hE : ∀ i k, Tendsto
      (fun j => microscopicCrossBudget (t j i) (t j k) /
        Real.log ((N j : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => Matrix.det
      (fun i k => phaseStrippedCross (t j i) (t j k) (N j))) atTop
      (𝓝 (Matrix.det (fun i k => (Real.sinc (Real.pi * (x i - x k)) : ℂ)))) := by
  have hentry : Tendsto
      (fun j i k => phaseStrippedCross (t j i) (t j k) (N j)) atTop
      (𝓝 (fun i k => logPhaseKernel (2 * Real.pi * (x i - x k)))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k =>
      phaseStrippedCross_microscopic_tendsto N (fun j => t j i) (fun j => t j k)
        (2 * Real.pi * (x i - x k)) hN (hx i k) (hE i k)
  have hd : Tendsto (fun j => Matrix.det
      (fun i k => phaseStrippedCross (t j i) (t j k) (N j))) atTop
      (𝓝 (Matrix.det (fun i k => logPhaseKernel (2 * Real.pi * (x i - x k))))) :=
    (continuous_id.matrix_det.tendsto _).comp hentry
  rwa [logPhaseKernel_scaled_det_eq_sine] at hd

theorem continuous_microscopicCrossBudget :
    Continuous (fun p : ℝ × ℝ => microscopicCrossBudget p.1 p.2) := by
  unfold microscopicCrossBudget MellinFrequency.criticalPoint
  fun_prop

theorem phaseStrippedCross_det_fixedCenter_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (t₀ : ℝ) (x : ι → ℝ) :
    Tendsto (fun j => Matrix.det (fun i k =>
      phaseStrippedCross
        (t₀ + 2 * Real.pi * x i / Real.log ((N j : ℝ) + 1))
        (t₀ + 2 * Real.pi * x k / Real.log ((N j : ℝ) + 1)) (N j))) atTop
      (𝓝 (Matrix.det (fun i k => (Real.sinc (Real.pi * (x i - x k)) : ℂ)))) := by
  have hNat : Tendsto (fun j => (N j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by
      change (N j : ℝ) ≤ (N j : ℝ) + 1
      linarith) (tendsto_natCast_atTop_atTop.comp hN)
  have hlog := Real.tendsto_log_atTop.comp hNat
  have hinv := tendsto_inv_atTop_zero.comp hlog
  let t : ℕ → ι → ℝ := fun j i =>
    t₀ + 2 * Real.pi * x i / Real.log ((N j : ℝ) + 1)
  have ht (i : ι) : Tendsto (fun j => t j i) atTop (𝓝 t₀) := by
    simpa only [t, div_eq_mul_inv, mul_zero, add_zero, Function.comp_apply] using
      ((hinv.const_mul (2 * Real.pi * x i)).const_add t₀)
  have hpos : ∀ᶠ j in atTop, 0 < N j := hN.eventually (eventually_gt_atTop 0)
  apply phaseStrippedCross_det_microscopic_tendsto N t x hpos
  · intro i k
    have he : ∀ᶠ j in atTop,
        (t j i - t j k) * Real.log ((N j : ℝ) + 1) =
          2 * Real.pi * (x i - x k) := by
      filter_upwards [hpos] with j hj
      have hp : 0 < Real.log ((N j : ℝ) + 1) := Real.log_pos (by
        have hn : 0 < (N j : ℝ) := by exact_mod_cast hj
        linarith)
      dsimp only [t]
      field_simp [hp.ne']
      ring
    exact (tendsto_congr' he).2 tendsto_const_nhds
  · intro i k
    have hb := (continuous_microscopicCrossBudget.tendsto (t₀, t₀)).comp
      ((ht i).prodMk_nhds (ht k))
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using hb.mul hinv

end RiemannResearch.RH.Pareto.ResidueMellin
