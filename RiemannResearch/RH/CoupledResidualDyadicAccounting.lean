import RiemannResearch.RH.CoupledResidualCauchyHead
import RiemannResearch.RH.LogarithmicCorrectionTarget
import RiemannResearch.Analysis.CumulativeEnergySummability
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact dyadic source accounting and unconditional summability

Source: continuation of the user-provided
`Signed_Head_Cauchy_RH_Continuation_2026-11-14.md`.
All objects are the actual two-seed Pareto residuals, with the original floors
and complete energies. The signed identity retains the full squared mismatch
between the new innovation and the transported earlier innovation.

The raw sources and every unnormalized moving-cutoff certificate are summable.
This does not prove or refute nonsummability after division by residual energy
times transported trace. That normalized arithmetic input remains open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual

private theorem dyadic_double (J j : ℕ) : 2 * 2 ^ (J + j) = 2 ^ (J + (j + 1)) := by
  rw [show J + (j + 1) = (J + j) + 1 by omega, pow_succ]
  omega

/-- Exact floor-preserving telescoping of the earlier-scale energies. -/
theorem dyadic_priorGain_sum (J p N : ℕ) :
    (∑ j ∈ Finset.range N, priorGain (2 ^ (J + j)) p) =
      distance (2 ^ J / p) - distance (2 ^ (J + N) / p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, priorGain, dyadic_double]
    ring

/-- Exact current-scale energy balance, including the final residual. -/
theorem dyadic_gain_sum (J N : ℕ) :
    (∑ j ∈ Finset.range N, gain (2 ^ (J + j))) =
      distance (2 ^ J) - distance (2 ^ (J + N)) := by
  simpa only [priorGain, gain, Nat.div_one] using dyadic_priorGain_sum J 1 N

/-- Both transported column energies are nonnegative, including degenerate stages. -/
theorem trace_nonneg (M : ℕ) : 0 ≤ trace M := by
  dsimp only [trace]
  positivity [priorGain_nonneg M 2, priorGain_nonneg M 3]

/-- Exact sum of transported energies, with both endpoint terms retained. -/
theorem dyadic_trace_sum (J N : ℕ) :
    (∑ j ∈ Finset.range N, trace (2 ^ (J + j))) =
      2 * (distance (2 ^ J / 2) - distance (2 ^ (J + N) / 2)) +
      3 * (distance (2 ^ J / 3) - distance (2 ^ (J + N) / 3)) := by
  simp only [trace, Finset.sum_add_distrib, ← Finset.mul_sum, dyadic_priorGain_sum]

/-- Earlier-scale gains are summable without an RH hypothesis. -/
theorem summable_dyadic_priorGain (J p : ℕ) :
    Summable (fun j => priorGain (2 ^ (J + j)) p) := by
  apply RiemannResearch.Analysis.NonnegativeEnergy.summable_of_nonnegative_prefix_bound
    _ (fun j => priorGain_nonneg _ _) (distance (2 ^ J / p))
  intro N
  rw [dyadic_priorGain_sum]
  linarith only [distance_pos (2 ^ (J + N) / p)]

/-- The unnormalized current-scale gains are always summable. -/
theorem summable_dyadic_gain (J : ℕ) :
    Summable (fun j => gain (2 ^ (J + j))) := by
  simpa only [priorGain, gain, Nat.div_one] using summable_dyadic_priorGain J 1

/-- The total transported trace is summable along every dyadic chain. -/
theorem summable_dyadic_trace (J : ℕ) :
    Summable (fun j => trace (2 ^ (J + j))) :=
  ((summable_dyadic_priorGain J 2).mul_left 2).add
    ((summable_dyadic_priorGain J 3).mul_left 3)

/-- The signed source pairs two actual innovations; the later residual is orthogonal. -/
theorem source_eq_inner_innovation (M p : ℕ) (hp : 0 < p) :
    source M p hp = inner ℝ (innovation M 1) (transported M p hp) := by
  have ho := Submodule.starProjection_inner_eq_zero hilbertOne
    (transported M p hp) (transported_mem M p hp)
  change inner ℝ (error (2 * M)) (transported M p hp) = 0 at ho
  have he : error M = innovation M 1 + error (2 * M) := by
    simp only [error, innovation, Nat.div_one]
    abel
  rw [source, he, inner_add_left, ho, add_zero]

/-- Exact signed energy identity. The squared mismatch is not discarded. -/
theorem innovation_transport_norm_sub_sq (M p : ℕ) (hp : 0 < p) :
    ‖innovation M 1 - transported M p hp‖ ^ 2 =
      gain M + (p : ℝ) * priorGain M p - 2 * source M p hp := by
  rw [norm_sub_sq_real, innovation_norm_sq, transported_norm_sq,
    ← source_eq_inner_innovation]
  simp only [priorGain, Nat.div_one, gain]
  ring

/-- Exact finite signed-source balance, including every squared mismatch. -/
theorem dyadic_signed_source_sum (J p N : ℕ) (hp : 0 < p) :
    2 * (∑ j ∈ Finset.range N, source (2 ^ (J + j)) p hp) =
      (distance (2 ^ J) - distance (2 ^ (J + N))) +
      (p : ℝ) * (distance (2 ^ J / p) - distance (2 ^ (J + N) / p)) -
      ∑ j ∈ Finset.range N,
        ‖innovation (2 ^ (J + j)) 1 - transported (2 ^ (J + j)) p hp‖ ^ 2 := by
  have he : ∀ j, 2 * source (2 ^ (J + j)) p hp =
      gain (2 ^ (J + j)) + (p : ℝ) * priorGain (2 ^ (J + j)) p -
      ‖innovation (2 ^ (J + j)) 1 - transported (2 ^ (J + j)) p hp‖ ^ 2 := by
    intro j
    linarith only [innovation_transport_norm_sub_sq (2 ^ (J + j)) p hp]
  rw [Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    dyadic_gain_sum, dyadic_priorGain_sum]

/-- Absolute source control by the two complete innovation energies. -/
theorem source_abs_le_energy (M p : ℕ) (hp : 0 < p) :
    |source M p hp| ≤ ((p : ℝ) * priorGain M p + gain M) / 2 := by
  have h := interscale_source_sq M p hp
  have hp0 : 0 ≤ (p : ℝ) * priorGain M p :=
    mul_nonneg (Nat.cast_nonneg p) (priorGain_nonneg M p)
  have hg := gain_nonneg M
  have hab := sq_nonneg ((p : ℝ) * priorGain M p - gain M)
  have hs := abs_nonneg (source M p hp)
  have he := sq_abs (source M p hp)
  nlinarith

/-- For every fixed positive dilation, the actual signed sources are absolutely summable. -/
theorem summable_abs_dyadic_source (J p : ℕ) (hp : 0 < p) :
    Summable (fun j => |source (2 ^ (J + j)) p hp|) := by
  apply Summable.of_nonneg_of_le (fun j => abs_nonneg _)
    (fun j => source_abs_le_energy _ _ hp)
  exact (((summable_dyadic_priorGain J p).mul_left (p : ℝ)).add
    (summable_dyadic_gain J)).div_const 2

/-- A finite absolute-source bound retaining both final residual energies. -/
theorem dyadic_abs_source_sum_le (J p N : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range N, |source (2 ^ (J + j)) p hp|) ≤
      ((p : ℝ) * (distance (2 ^ J / p) - distance (2 ^ (J + N) / p)) +
        (distance (2 ^ J) - distance (2 ^ (J + N)))) / 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ((p : ℝ) * priorGain (2 ^ (J + j)) p + gain (2 ^ (J + j))) / 2 :=
      Finset.sum_le_sum (fun j _ => source_abs_le_energy _ _ hp)
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
        dyadic_priorGain_sum, dyadic_gain_sum]

/-- Undivided two-source bound, valid also when the trace vanishes. -/
theorem sourceSquare_le_trace_gain (M : ℕ) :
    sourceSquare M ≤ trace M * gain M := by
  have h2 := interscale_source_sq M 2 (by omega)
  have h3 := interscale_source_sq M 3 (by omega)
  norm_num only [Nat.cast_ofNat] at h2 h3
  dsimp only [sourceSquare, trace]
  nlinarith

/-- Trace normalization alone is still an absolute gain; no positive trace is required. -/
theorem sourceSquare_div_trace_le_gain (M : ℕ) :
    sourceSquare M / trace M ≤ gain M := by
  rcases eq_or_lt_of_le (trace_nonneg M) with ht | ht
  · rw [← ht, div_zero]
    exact gain_nonneg M
  · exact trace_gain M ht

/-- The trace-normalized complete source squares are unconditionally summable. -/
theorem summable_dyadic_sourceSquare_div_trace (J : ℕ) :
    Summable (fun j => sourceSquare (2 ^ (J + j)) / trace (2 ^ (J + j))) :=
  Summable.of_nonneg_of_le
    (fun j => div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (trace_nonneg _))
    (fun j => sourceSquare_div_trace_le_gain _) (summable_dyadic_gain J)

/-- The same absolute-gain summability holds for arbitrary finite-head cutoffs. -/
theorem summable_dyadic_cauchySquare_div_trace (J : ℕ) (K : ℕ → ℕ) :
    Summable (fun j => cauchySourceSquare (2 ^ (J + j)) (K j) / trace (2 ^ (J + j))) :=
  Summable.of_nonneg_of_le
    (fun j => div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (trace_nonneg _))
    (fun j => div_le_div_of_nonneg_right
      (cauchySourceSquare_le_sourceSquare _ _) (trace_nonneg _))
    (summable_dyadic_sourceSquare_div_trace J)

/-- The unnormalized complete two-source squares are always summable. -/
theorem summable_dyadic_sourceSquare (J : ℕ) :
    Summable (fun j => sourceSquare (2 ^ (J + j))) := by
  apply Summable.of_nonneg_of_le (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _)) _
    ((summable_dyadic_trace J).mul_left (distance 0))
  intro j
  have hg : gain (2 ^ (J + j)) ≤ distance 0 := by
    have hd := distance_antitone (Nat.zero_le (2 ^ (J + j)))
    dsimp only [gain]
    linarith only [hd, distance_pos (2 * 2 ^ (J + j))]
  calc
    sourceSquare (2 ^ (J + j)) ≤ trace (2 ^ (J + j)) * gain (2 ^ (J + j)) :=
      sourceSquare_le_trace_gain _
    _ ≤ trace (2 ^ (J + j)) * distance 0 :=
      mul_le_mul_of_nonneg_left hg (trace_nonneg _)
    _ = distance 0 * trace (2 ^ (J + j)) := mul_comm _ _

/-- Arbitrary moving cutoffs cannot make the raw Cauchy magnitudes nonsummable. -/
theorem summable_dyadic_cauchyMagnitude (J p : ℕ) (hp : 0 < p) (K : ℕ → ℕ) :
    Summable (fun j => cauchySourceMagnitude (2 ^ (J + j)) p hp (K j)) :=
  Summable.of_nonneg_of_le (fun j => cauchySourceMagnitude_nonneg _ _ _ _)
    (fun j => cauchySourceMagnitude_le_abs _ _ _ _) (summable_abs_dyadic_source J p hp)

/-- Arbitrary moving cutoffs cannot make the raw Cauchy squares nonsummable. -/
theorem summable_dyadic_cauchySquare (J : ℕ) (K : ℕ → ℕ) :
    Summable (fun j => cauchySourceSquare (2 ^ (J + j)) (K j)) :=
  Summable.of_nonneg_of_le (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun j => cauchySourceSquare_le_sourceSquare _ _) (summable_dyadic_sourceSquare J)

end RiemannResearch.RH.Pareto.CoupledResidual
