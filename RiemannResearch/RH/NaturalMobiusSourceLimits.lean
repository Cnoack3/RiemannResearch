import RiemannResearch.RH.NaturalMobiusPeriodicTests
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.NumberTheory.PrimeNumberTheorem.LogarithmicMobiusMean

/-!
# Actual fixed sources of the raw Möbius residual tend to zero

The constant source is exactly one plus the logarithm-weighted Möbius mean.
Its unconditional limit, together with centered periodic source decay, gives
the complete pairing limit for every fixed normalized residue generator.
Source: `ReciprocalCharge_DilationAndPeriodicSource_20260924.md`, Sections 7–8;
the logarithmic Möbius mean is the classical identity recorded in NIST DLMF
27.11.15. All statements use the actual Pareto inner product.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The genuine normalized residue has complete Pareto mean log(d)/d. -/
theorem normalizedResidueHilbert_inner_one (d : ℕ) (hd : 0 < d) :
    inner ℝ (normalizedResidueHilbert d hd) hilbertOne = Real.log d / (d : ℝ) := by
  rw [hilbert_inner_one, normalizedResidueHilbert_sequence]
  unfold paretoMean
  have he : (fun k => positiveWeight k * residueFraction d k) =
      (fun k => (positiveWeight k * residue d k) / (d : ℝ)) := by
    funext k
    unfold residueFraction residue
    ring
  rw [he, tsum_div_const]
  change paretoMean (residue d) / (d : ℝ) = _
  rw [paretoMean_residue d hd]

/-- Exact identification of the constant source before taking a limit. -/
theorem rawMobiusResidual_inner_one_eq_logarithmicMean (N : ℕ) :
    inner ℝ (hilbertOne - rawMobiusHilbert N) hilbertOne =
      1 + logarithmicMobiusMean N := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  unfold rawMobiusHilbert
  rw [inner_neg_left]
  simp_rw [sum_inner, real_inner_smul_left, normalizedResidueHilbert_inner_one]
  rw [Finset.sum_attach (Finset.Icc 1 N)
    (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) * (Real.log d / (d : ℝ)))]
  simp only [sub_neg_eq_add, logarithmicMobiusMean]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The actual constant source vanishes unconditionally. -/
theorem rawMobiusResidual_inner_one_tendsto_zero :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) hilbertOne)
      atTop (𝓝 0) := by
  simpa only [rawMobiusResidual_inner_one_eq_logarithmicMean, add_neg_cancel]
    using logarithmicMobiusMean_tendsto_neg_one.const_add 1

/-- The full fixed residue source vanishes, including its constant mode. -/
theorem rawMobiusResidual_residue_inner_tendsto_zero (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N =>
      inner ℝ (hilbertOne - rawMobiusHilbert N) (normalizedResidueHilbert m hm))
      atTop (𝓝 0) := by
  have hc := rawMobiusResidual_centered_residue_inner_tendsto m hm
  have hm0 := rawMobiusResidual_inner_one_tendsto_zero.const_mul
    (((m : ℝ) - 1) / (2 * (m : ℝ)))
  simpa only [sub_add_cancel, mul_zero, add_zero] using hc.add hm0

/-- Every fixed finite signed Möbius head is an unconditional vanishing test. -/
theorem rawMobiusResidual_inner_rawMobius_tendsto_zero (M : ℕ) :
    Tendsto (fun N =>
      inner ℝ (hilbertOne - rawMobiusHilbert N) (rawMobiusHilbert M))
      atTop (𝓝 0) := by
  have hsum (s : Finset {d // d ∈ Finset.Icc 1 M}) :
      Tendsto (fun N => ∑ d ∈ s,
        (ArithmeticFunction.moebius (d : ℕ) : ℝ) *
          inner ℝ (hilbertOne - rawMobiusHilbert N)
            (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1))
        atTop (𝓝 0) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert d s hds ih =>
      have hd := (rawMobiusResidual_residue_inner_tendsto_zero d
        (Finset.mem_Icc.mp d.property).1).const_mul
          (ArithmeticFunction.moebius (d : ℕ) : ℝ)
      simpa only [Finset.sum_insert hds, mul_zero, add_zero] using hd.add ih
  simpa only [rawMobiusHilbert, inner_neg_right, inner_sum, inner_smul_right,
    neg_zero] using (hsum (Finset.Icc 1 M).attach).neg

/-- The entire signed rectangle between a fixed head and its extending tail
has an explicit unconditional limit. For N ≥ M this is exactly the sum of
μ(d)μ(e)G(d,e) over d ≤ M < e ≤ N. -/
theorem rawMobius_tail_inner_head_tendsto (M : ℕ) :
    Tendsto (fun N =>
      inner ℝ (rawMobiusHilbert N - rawMobiusHilbert M) (rawMobiusHilbert M))
      atTop (𝓝 (-logarithmicMobiusMean M - ‖rawMobiusHilbert M‖^2)) := by
  have hz := rawMobiusResidual_inner_rawMobius_tendsto_zero M
  have hhead : inner ℝ hilbertOne (rawMobiusHilbert M) =
      -logarithmicMobiusMean M := by
    have h := rawMobiusResidual_inner_one_eq_logarithmicMean M
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq] at h
    rw [real_inner_comm]
    linarith
  have hid (N : ℕ) :
      inner ℝ (rawMobiusHilbert N - rawMobiusHilbert M) (rawMobiusHilbert M) =
        (-logarithmicMobiusMean M - ‖rawMobiusHilbert M‖^2) -
          inner ℝ (hilbertOne - rawMobiusHilbert N) (rawMobiusHilbert M) := by
    rw [inner_sub_left, inner_sub_left, real_inner_self_eq_norm_sq, hhead]
    ring
  simp_rw [hid]
  simpa only [sub_zero] using
    tendsto_const_nhds.sub hz


end RiemannResearch.RH.Pareto
