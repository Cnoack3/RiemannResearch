import RiemannResearch.RH.MultiRangeCertificateConvergence
import Mathlib.Topology.Instances.Matrix
import RiemannResearch.RH.ConditionalResidueGram

/-! Fixed-family truncated Gram optimizers converge to the full optimizer.
Source: Section 7 of the multi-range research note. Nondegeneracy of the full
finite Gram matrix is explicit; for distinct anchored divisors it follows from
linear independence. No bound uniform in a growing divisor family is asserted.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conditionalMeanPrefixInner (F G : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, conditionalWeight k * cesaro F (k+1) * cesaro G (k+1)

def finiteMeanGram (U : ι → ℕ → ℝ) : Matrix ι ι ℝ :=
  fun i j => conditionalMeanInner (U i) (U j)

def prefixMeanGram (U : ι → ℕ → ℝ) (N : ℕ) : Matrix ι ι ℝ :=
  fun i j => conditionalMeanPrefixInner (U i) (U j) N

def finiteMeanOptimizer (F : ℕ → ℝ) (U : ι → ℕ → ℝ) (i : ι) : ℝ :=
  -(∑ j, (finiteMeanGram U)⁻¹ i j * conditionalMeanInner F (U j))

def prefixMeanOptimizer (F : ℕ → ℝ) (U : ι → ℕ → ℝ) (N : ℕ) (i : ι) : ℝ :=
  -(∑ j, (prefixMeanGram U N)⁻¹ i j * conditionalMeanPrefixInner F (U j) N)

theorem conditionalMeanPrefixInner_tendsto (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (hG : G ∈ legalSeedSpan (Set.Ici 1)) :
    Tendsto (conditionalMeanPrefixInner F G) atTop (𝓝 (conditionalMeanInner F G)) :=
  (conditionalMeanInner_summable F G hF hG).hasSum.tendsto_sum_nat

omit [Fintype ι] [DecidableEq ι] in
theorem prefixMeanGram_tendsto (U : ι → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1)) :
    Tendsto (prefixMeanGram U) atTop (𝓝 (finiteMeanGram U)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact conditionalMeanPrefixInner_tendsto (U i) (U j) (hU i) (hU j)

theorem prefixMeanOptimizer_tendsto (F : ℕ → ℝ) (U : ι → ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hdet : (finiteMeanGram U).det ≠ 0) :
    Tendsto (prefixMeanOptimizer F U) atTop (𝓝 (finiteMeanOptimizer F U)) := by
  have hc : ContinuousAt Inv.inv (finiteMeanGram U) :=
    continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet)
  have hi := hc.tendsto.comp (prefixMeanGram_tendsto U hU)
  apply tendsto_pi_nhds.2
  intro i
  apply Filter.Tendsto.neg
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi i)) j).mul
    (conditionalMeanPrefixInner_tendsto F (U j) hF (hU j))

/-- Each coordinate, and hence each fixed finite coefficient vector, is
uniformly bounded on a sufficiently long tail of truncations. -/
theorem prefixMeanOptimizer_eventually_bounded (F : ℕ → ℝ) (U : ι → ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hdet : (finiteMeanGram U).det ≠ 0) :
    ∀ᶠ N in atTop, ∀ i, |prefixMeanOptimizer F U N i| ≤ |finiteMeanOptimizer F U i| + 1 := by
  have ht := prefixMeanOptimizer_tendsto F U hF hU hdet
  have he (i : ι) : ∀ᶠ N in atTop,
      |prefixMeanOptimizer F U N i| ≤ |finiteMeanOptimizer F U i| + 1 := by
    have hi := (tendsto_pi_nhds.mp ht i).abs
    have hh := hi.eventually (gt_mem_nhds (by linarith :
      |finiteMeanOptimizer F U i| < |finiteMeanOptimizer F U i|+1))
    filter_upwards [hh] with N hN using hN.le
  simpa only [Filter.eventually_all] using he

/-- Fixed-family coefficient convergence gives an actual uniform mean bound
for all sufficiently large truncations. -/
theorem prefixMeanOptimizer_mean_eventually_bounded (F : ℕ → ℝ) (U : ι → ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hdet : (finiteMeanGram U).det ≠ 0)
    (B : ℝ) (C : ι → ℝ) (_hC : ∀ i, 0 ≤ C i)
    (hBF : ∀ t, |cesaro F t| ≤ B) (hCU : ∀ i t, |cesaro (U i) t| ≤ C i) :
    ∀ᶠ N in atTop, ∀ t,
      |cesaro (fun n => F n + ∑ i, prefixMeanOptimizer F U N i * U i n) t| ≤
        B + ∑ i, (|finiteMeanOptimizer F U i|+1)*C i := by
  filter_upwards [prefixMeanOptimizer_eventually_bounded F U hF hU hdet] with N hN
  intro t
  have he : cesaro (fun n => F n + ∑ i, prefixMeanOptimizer F U N i * U i n) t =
      cesaro F t + ∑ i, prefixMeanOptimizer F U N i * cesaro (U i) t := by
    have hh := cesaro_add_mul F (fun n => ∑ i, prefixMeanOptimizer F U N i * U i n) 1 t
    simpa only [one_mul, cesaro_finsetCombination] using hh
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add (hBF t)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul (hN i) (hCU i t) (abs_nonneg _) (by positivity)

end RiemannResearch.RH.Pareto
