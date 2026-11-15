import RiemannResearch.RH.PrimorialCutoff
import RiemannResearch.RH.PrimorialDensityLowerBound
import RiemannResearch.RH.PrimorialSieveLift
import RiemannResearch.RH.QuantitativeSieve
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Source obstruction with a freely optimized correction coefficient

Source: the user's primorial-sieve compactness investigation, 14 November 2026.
This extends the prescribed-coefficient obstruction in PrimorialCutoff.
For every real a, positive K <= M, and conductor covering 2 through 3M,
the complete Q source energy is at least M * density(L)^2 / (36 * zeta(2)).
The proof first retains the exact signed difference at a multiple of K.
The correcting residue cancels from that difference, regardless of a.

The primorial consequence allows arbitrary stage-dependent real coefficients.
It excludes the eventually-small-cutoff class, not all coefficient schedules
with large cutoffs, and not signed combinations of several correcting residues.
It neither proves nor refutes the existence of bounded full-legal target lifts.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.PrimorialCoefficientObstruction
open ZetaTwoHilbert ZetaTwoProbability QPrimeSieve ArithmeticCumulative
open QuantitativeSieve QFullResidueProjection PrimorialSieveLift PrimorialCutoff

/-- Retain the Mobius sieve and allow any real coefficient on the correcting residue. -/
def coefficientLift (L K : ℕ) (a : ℝ) : QHilbert :=
  cutoffLift L K + (a - divisorDensity L * (K : ℝ)) • qResidue K

theorem coefficientLift_eq (L K : ℕ) (a : ℝ) :
    coefficientLift L K a =
      a • qResidue K - ∑ d ∈ L.divisors,
        (ArithmeticFunction.moebius d : ℝ) • qResidue d := by
  rw [coefficientLift, cutoffLift]
  module

theorem coefficientLift_mem (L K : ℕ) (a : ℝ) (hK : 0 < K) :
    coefficientLift L K a ∈ legalSpan :=
  legalSpan.add_mem (cutoffLift_mem L K hK)
    (legalSpan.smul_mem _ (residue_mem_legalSpan K hK))

theorem coefficientLift_sequence (L K n : ℕ) (a : ℝ)
    (hL : 0 < L) (hK : 0 < K) :
    qSequence (coefficientLift L K a) n =
      coprimeCount L n - divisorDensity L * (n : ℝ) + a * residueFraction K n := by
  change qSequenceLinear (_ + _) n = _
  rw [map_add, map_smul]
  change qSequence (cutoffLift L K) n +
    (a - divisorDensity L * (K : ℝ)) * qSequence (qResidue K) n = _
  rw [cutoffLift_sequence L K n hL hK, qSequence_qResidue,
    Pareto.residueFraction_eq_div_sub_floor K n hK]
  have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  field_simp
  ring

/-- A shift by a multiple of K cancels the correcting residue exactly. -/
theorem coefficientLift_head_difference (L K H n : ℕ) (a : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hd : K ∣ H)
    (hc : Covers L (n + H)) (hn : 0 < n) :
    qSequence (coefficientLift L K a) (n + H) -
      qSequence (coefficientLift L K a) n = -divisorDensity L * (H : ℝ) := by
  have hc' : Covers L n := fun j hj hjn => hc j hj (by omega)
  have hr : residueFraction K (n + H) = residueFraction K n := by
    simp only [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd,
      Nat.add_zero, Nat.mod_mod]
  rw [coefficientLift_sequence L K (n + H) a hL hK,
    coefficientLift_sequence L K n a hL hK, hr,
    coprimeCount_head L (n + H) (n + H) (by omega) le_rfl hc,
    coprimeCount_head L n n hn le_rfl hc']
  push_cast
  ring

/-- This complete-energy lower bound is independent of the correcting coefficient. -/
theorem coefficientLift_block_energy (L K H : ℕ) (a : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hH : 0 < H) (hd : K ∣ H)
    (hc : Covers L (3 * H)) :
    (H : ℝ) * divisorDensity L ^ 2 / (18 * zetaTwo) ≤
      ‖coefficientLift L K a‖ ^ 2 := by
  have hZ := zetaTwo_pos
  have hsum : (H : ℝ) * (divisorDensity L * (H : ℝ)) ^ 2 / 2 ≤
      ∑ n ∈ Finset.Ico H (3 * H), (qSequence (coefficientLift L K a) n)^2 := by
    rw [← Finset.sum_Ico_consecutive _ (show H ≤ 2 * H by omega)
      (show 2 * H ≤ 3 * H by omega),
      Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show 2 * H - H = H by omega, show 3 * H - 2 * H = H by omega,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range H, (divisorDensity L * (H : ℝ)) ^ 2 / 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hiH := Finset.mem_range.mp hi
        have hcov : Covers L (H + i + H) := fun j hj hjn => hc j hj (by omega)
        have he := coefficientLift_head_difference L K H (H + i) a
          hL hK hd hcov (by omega)
        rw [show H + i + H = 2 * H + i by omega] at he
        have hesq := congrArg (fun x : ℝ => x ^ 2) he
        nlinarith [sq_nonneg (qSequence (coefficientLift L K a) (H + i) +
          qSequence (coefficientLift L K a) (2 * H + i))]
  have hn := hsum.trans (interval_sq_le_norm (coefficientLift L K a) H (3 * H) hH)
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  push_cast at hn
  apply (div_le_iff₀ (by positivity : 0 < 18 * zetaTwo)).mpr
  nlinarith [sq_pos_of_pos hHR]

/-- Optimize the real coefficient arbitrarily: every K ≤ M still pays this energy. -/
theorem coefficientLift_small_energy (L K M : ℕ) (a : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hKM : K ≤ M) (hc : Covers L (3 * M)) :
    (M : ℝ) * divisorDensity L ^ 2 / (36 * zetaTwo) ≤
      ‖coefficientLift L K a‖ ^ 2 := by
  let H := K * (M / K)
  have hH : 0 < H := Nat.mul_pos hK (Nat.div_pos hKM hK)
  have hHM : H ≤ M := by dsimp [H]; exact Nat.mul_div_le M K
  have hKH : K ≤ H := by
    have : 1 ≤ M / K := Nat.div_pos hKM hK
    dsimp [H]
    nlinarith
  have hMH : M ≤ 2 * H := by
    have he := Nat.mod_add_div M K
    have hr := Nat.mod_lt M hK
    change M ≤ 2 * (K * (M / K))
    dsimp [H] at hKH
    omega
  have hcov : Covers L (3 * H) := fun j hj hjn => hc j hj (by omega)
  have hb := coefficientLift_block_energy L K H a hL hK hH
    (show K ∣ H from ⟨M / K, rfl⟩) hcov
  have hmR : (M : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hMH
  have he := mul_le_mul_of_nonneg_right hmR (sq_nonneg (divisorDensity L))
  apply le_trans _ hb
  apply (div_le_div_iff₀ (by positivity [zetaTwo_pos] : 0 < 36 * zetaTwo)
    (by positivity [zetaTwo_pos] : 0 < 18 * zetaTwo)).mpr
  nlinarith [mul_le_mul_of_nonneg_right he zetaTwo_pos.le]

/-- Even freely optimized real coefficients cannot repair small single cutoffs. -/
theorem coefficientLift_small_norm_sq_tendsto (K : ℕ → ℕ) (a : ℕ → ℝ)
    (hK : ∀ N, 0 < K N) (hsmall : ∀ᶠ N in atTop, K N ≤ N / 3) :
    Tendsto (fun N => ‖coefficientLift (primorial N) (K N) (a N)‖^2)
      atTop atTop := by
  have ht := third_density_cube_growth.const_mul_atTop
    (by positivity [zetaTwo_pos] : 0 < 1 / (36 * zetaTwo))
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [hsmall] with N hN
  have hc : Covers (primorial N) (3 * (N / 3)) :=
    fun j hj hjN => primorial_covers N j hj (hjN.trans (Nat.mul_div_le N 3))
  have hb := coefficientLift_small_energy (primorial N) (K N) (N / 3) (a N)
    (primorial_pos _) (hK N) hN hc
  rw [primorial_density_eq] at hb
  have hd := PrimorialDensity.density_le_one N
  have hp := (PrimorialDensity.density_pos N).le
  have hcube : PrimorialDensity.density N ^ 3 ≤ PrimorialDensity.density N ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (PrimorialDensity.density N)) (sub_nonneg.mpr hd)]
  have hm := mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg (N / 3))
  have hh := div_le_div_of_nonneg_right hm
    (by positivity [zetaTwo_pos] : 0 ≤ 36 * zetaTwo)
  have hb' := hh.trans hb
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb'

end RiemannResearch.RH.PrimorialCoefficientObstruction
