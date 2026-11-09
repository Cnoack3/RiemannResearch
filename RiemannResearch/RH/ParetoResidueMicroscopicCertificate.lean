import RiemannResearch.RH.ParetoResidueMovingCertificate
import RiemannResearch.RH.ParetoResidueMicroscopicGram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Microscopic grouped zero Gram and real certificate bounds

The complex two-ordinate Gram uses the difference-frequency profile.
The real certificate tests include both signs of every ordinate. Their
energy bound below uses both the difference- and sum-frequency terms.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin

open MellinFrequency (criticalPoint)
open SpectralObstruction (logPhaseKernel logPhaseKernel_pairDet_pos)

/-- Determinant of the two complex phase-normalized grouped observations. -/
def phaseStrippedPairDet (t u : ℝ) (N : ℕ) : ℝ :=
  (phaseStrippedCross t t N).re * (phaseStrippedCross u u N).re -
    ‖phaseStrippedCross t u N‖ ^ 2

private theorem star_phaseStrippedCross (t u : ℝ) (N : ℕ) :
    star (phaseStrippedCross t u N) = phaseStrippedCross u t N := by
  simp [phaseStrippedCross, classCross, classCrossSum, classCrossTerm, mul_comm]

theorem phaseStrippedPairDet_eq_gram (t u : ℝ) (N : ℕ) :
    let ts : Fin 2 → ℝ := fun i => if i = 0 then t else u
    phaseStrippedPairDet t u N =
      (Matrix.of (fun i j : Fin 2 => phaseStrippedCross (ts i) (ts j) N)).det.re := by
  dsimp only
  rw [Matrix.det_fin_two]
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [Matrix.of_apply, ite_true, if_neg hone]
  have hd (v : ℝ) : (phaseStrippedCross v v N).im = 0 := by
    have h := congrArg Complex.im (star_phaseStrippedCross v v N)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hc : phaseStrippedCross t u N * star (phaseStrippedCross t u N) =
      ((‖phaseStrippedCross t u N‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
      Complex.mul_conj (phaseStrippedCross t u N)
  rw [← star_phaseStrippedCross t u N, hc]
  simp only [phaseStrippedPairDet, Complex.sub_re, Complex.mul_re, hd, zero_mul, sub_zero,
    Complex.ofReal_re]

theorem phaseStrippedPairDet_microscopic_tendsto (N : ℕ → ℕ) (t u : ℕ → ℝ) (v : ℝ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (hv : Tendsto (fun j => (t j - u j) * Real.log ((N j : ℝ) + 1)) atTop (𝓝 v))
    (htt : Tendsto (fun j => microscopicCrossBudget (t j) (t j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0))
    (huu : Tendsto (fun j => microscopicCrossBudget (u j) (u j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0))
    (htu : Tendsto (fun j => microscopicCrossBudget (t j) (u j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => phaseStrippedPairDet (t j) (u j) (N j)) atTop
      (𝓝 (1 - ‖logPhaseKernel v‖ ^ 2)) := by
  have hd (a : ℕ → ℝ) (ha : Tendsto (fun j => microscopicCrossBudget (a j) (a j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0)) :
      Tendsto (fun j => (phaseStrippedCross (a j) (a j) (N j)).re) atTop (𝓝 1) := by
    have hzero : Tendsto (fun j => (a j - a j) * Real.log ((N j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [sub_self, zero_mul] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have h := phaseStrippedCross_microscopic_tendsto N a a 0 hN hzero ha
    simpa [Function.comp_def, logPhaseKernel] using (Complex.continuous_re.tendsto _).comp h
  have hc := (phaseStrippedCross_microscopic_tendsto N t u v hN hv htu).norm.pow 2
  simpa only [phaseStrippedPairDet, one_mul] using ((hd t htt).mul (hd u huu)).sub hc

theorem phaseStrippedPairDet_eventually_ge (N : ℕ → ℕ) (t u : ℕ → ℝ) {v : ℝ}
    (hv0 : v ≠ 0) (hN : ∀ᶠ j in atTop, 0 < N j)
    (hv : Tendsto (fun j => (t j - u j) * Real.log ((N j : ℝ) + 1)) atTop (𝓝 v))
    (htt : Tendsto (fun j => microscopicCrossBudget (t j) (t j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0))
    (huu : Tendsto (fun j => microscopicCrossBudget (u j) (u j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0))
    (htu : Tendsto (fun j => microscopicCrossBudget (t j) (u j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, (1 - ‖logPhaseKernel v‖ ^ 2) / 2 ≤
      phaseStrippedPairDet (t j) (u j) (N j) := by
  have h := phaseStrippedPairDet_microscopic_tendsto N t u v hN hv htt huu htu
  have hp := logPhaseKernel_pairDet_pos hv0
  have he := (tendsto_order.1 h).1 ((1 - ‖logPhaseKernel v‖ ^ 2) / 2) (by linarith)
  exact he.mono (fun _ hj => hj.le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual microscopic comparison row includes both signed frequencies
and the entrywise analytic errors. -/
def microscopicRealRowBudget (γ : ι → ℝ) (N : ℕ) (i : ι × Bool) : ℝ :=
  ∑ j : ι × Bool,
    (|crossPart i.2 j.2 (criticalKernelPair (γ i.1) (γ j.1) N) /
      (‖criticalPoint (γ i.1)‖ * ‖criticalPoint (γ j.1)‖) -
      (if i = j then 1 / 2 else 0)| +
    (microscopicCrossBudget (γ i.1) (γ j.1) + microscopicCrossBudget (γ i.1) (-γ j.1)) /
      (2 * Real.log ((N : ℝ) + 1)))

theorem relativeCriticalGram_row_le_microscopic (γ : ι → ℝ) (N : ℕ) (hN : 0 < N)
    (i : ι × Bool) :
    (∑ j, |relativeCriticalGram γ N i j - (if i = j then 1 / 2 else 0)|) ≤
      microscopicRealRowBudget γ N i := by
  unfold microscopicRealRowBudget
  apply Finset.sum_le_sum
  intro j _
  let a := relativeCriticalGram γ N i j
  let b := crossPart i.2 j.2 (criticalKernelPair (γ i.1) (γ j.1) N) /
    (‖criticalPoint (γ i.1)‖ * ‖criticalPoint (γ j.1)‖)
  let c : ℝ := if i = j then 1 / 2 else 0
  have h := relativeCriticalGram_sub_kernel_le γ N hN i j
  calc
    |a - c| = |(a - b) + (b - c)| := by rw [show a - b + (b - c) = a - c by ring]
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ = |b - c| + |a - b| := add_comm _ _
    _ ≤ _ := add_le_add le_rfl h

/-- A bound on the microscopic comparison controls the actual real grouped projection. -/
theorem critical_certificate_energy_bounds_of_microscopic (γ : ι → ℝ) (N : ℕ)
    (hN : 0 < N) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d < 1 / 2)
    (hrow : ∀ i, microscopicRealRowBudget γ N i ≤ d) :
    relativeCriticalSourceSq γ N / (1 / 2 + d) ≤
      Real.log ((N : ℝ) + 1) * certificateEnergy N (fun i => criticalPoint (γ i)) ∧
    Real.log ((N : ℝ) + 1) * certificateEnergy N (fun i => criticalPoint (γ i)) ≤
      relativeCriticalSourceSq γ N / (1 / 2 - d) :=
  critical_certificate_energy_bounds γ N hN hz d hd hd'
    (fun i => (relativeCriticalGram_row_le_microscopic γ N hN i).trans (hrow i))

/-- A uniform row margin and vanishing source divided by the log scale are
enough for vanishing grouped certificate energy along a moving family. -/
theorem critical_certificate_tendsto_of_microscopic
    (κ : ℕ → Type*) [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (N : ℕ → ℕ) (γ : ∀ j, κ j → ℝ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d < 1 / 2)
    (hrow : ∀ᶠ j in atTop, ∀ i, microscopicRealRowBudget (γ j) (N j) i ≤ d)
    (hsource : Tendsto (fun j => relativeCriticalSourceSq (γ j) (N j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => certificateEnergy (N j) (fun i => criticalPoint (γ j i)))
      atTop (𝓝 0) := by
  have hB : Tendsto (fun j => (relativeCriticalSourceSq (γ j) (N j) /
      Real.log ((N j : ℝ) + 1)) / (1 / 2 - d)) atTop (𝓝 0) := by
    simpa only [zero_div] using hsource.div_const (1 / 2 - d)
  refine squeeze_zero' (Eventually.of_forall (fun j => certificateEnergy_nonneg _ _)) ?_ hB
  filter_upwards [hN, hrow] with j hj hjrow
  have hlog : 0 < Real.log ((N j : ℝ) + 1) := by
    have hn : (0 : ℝ) < N j := by exact_mod_cast hj
    exact Real.log_pos (by linarith)
  have h := (critical_certificate_energy_bounds_of_microscopic
    (γ j) (N j) hj (hz j) d hd hd' hjrow).2
  calc
    _ ≤ (relativeCriticalSourceSq (γ j) (N j) / (1 / 2 - d)) /
        Real.log ((N j : ℝ) + 1) :=
      (le_div_iff₀ hlog).mpr (by rwa [mul_comm])
    _ = _ := by ring

end RiemannResearch.RH.Pareto.ResidueMellin
