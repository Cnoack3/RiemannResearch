import RiemannResearch.Analysis.ActualPrimeTwoLandauBand
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.RamanujanOrdinateFMZ
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Uniform Ramanujan recovery from actual zeta ordinates

Choose frequencies in the prime-two band by folding the residue of the
harmonic into the interval `[log 2 / 2, log 2]`. One probe per divisor works
in a linear range of conductors. With a fixed list of dyadic multipliers
for each divisor, a common height threshold works for every conductor.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem folded_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- Fold the arithmetic residue into the left half of the prime-two band. -/
def foldedPrimeTwoFrequency (d n : ℕ) : ℝ :=
  Real.log 2 - (((n % d : ℕ) : ℝ) / (2 * (d : ℝ))) * Real.log 2

theorem foldedPrimeTwoFrequency_mem {d n : ℕ} (hd : 0 < d) :
    Real.log 2 / 2 ≤ foldedPrimeTwoFrequency d n ∧
      foldedPrimeTwoFrequency d n ≤ Real.log 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  have h₁ : ((n % d : ℕ) : ℝ) / (2 * (d : ℝ)) ≤ 1/2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  have h₂ : 0 ≤ ((n % d : ℕ) : ℝ) / (2 * (d : ℝ)) := by positivity
  unfold foldedPrimeTwoFrequency
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_right h₁ folded_log_two_pos.le]
  · linarith only [mul_nonneg h₂ folded_log_two_pos.le]

/-- Folding amounts to a change of indices in the original prime-root orbit. -/
theorem foldedPrimeTwoFrequency_eq_primeRootFrequency {d n : ℕ} (hd : 0 < d) :
    foldedPrimeTwoFrequency d n = primeRootFrequency 2 (2*d) (2*d - n % d) := by
  have hr := Nat.mod_lt n hd
  have hr' : n % d ≤ 2*d := by omega
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold foldedPrimeTwoFrequency primeRootFrequency
  push_cast [Nat.cast_sub hr']
  field_simp
  <;> ring

/-- A folded divisor probe from the actual zero ordinates at height `T`. -/
def foldedOrdinateDivisorProbe (T : ℝ) (d n : ℕ) : ℂ :=
  primeTwoOrdinateProbe T (foldedPrimeTwoFrequency d n)

private theorem foldedPrimeTwoFrequency_eq_of_dvd {d n : ℕ} (h : d ∣ n) :
    foldedPrimeTwoFrequency d n = Real.log 2 := by
  simp [foldedPrimeTwoFrequency, Nat.mod_eq_zero_of_dvd h]

private theorem fold_gap_of_not_dvd {d n : ℕ} (hd : 0 < d) (h : ¬ d ∣ n) :
    Real.log 2 / (2 * (d : ℝ)) ≤ Real.log 2 - foldedPrimeTwoFrequency d n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : (1 : ℝ) ≤ (n % d : ℕ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (fun hzero => h (Nat.dvd_of_mod_eq_zero hzero)))
  have hmul := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hr (by positivity : 0 ≤ 2*(d:ℝ))) folded_log_two_pos.le
  unfold foldedPrimeTwoFrequency
  simpa only [one_div, div_eq_mul_inv, one_mul, sub_sub_cancel, mul_comm (Real.log 2)] using hmul

private theorem fold_gap_of_large_residue {d n : ℕ} (hd : 0 < d) (h : d ≤ 2 * (n % d)) :
    Real.log 2 / 4 ≤ Real.log 2 - foldedPrimeTwoFrequency d n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : (d : ℝ) ≤ 2 * ((n % d : ℕ) : ℝ) := by exact_mod_cast h
  have hf : 1 / 4 ≤ ((n % d : ℕ) : ℝ) / (2 * (d : ℝ)) :=
    (le_div_iff₀ (by positivity)).2 (by linarith)
  unfold foldedPrimeTwoFrequency
  linarith only [mul_le_mul_of_nonneg_right hf folded_log_two_pos.le]

private theorem round_re_of_profile_one {v : ℂ} (h : ‖v - 1‖ < 1 / 2) : round v.re = 1 := by
  have hr := (Complex.abs_re_le_norm (v - 1)).trans_lt h
  simp only [Complex.sub_re, Complex.one_re, abs_lt] at hr
  exact round_eq_iff.mpr ⟨by norm_num; linarith [hr.1], by norm_num; linarith [hr.2]⟩

private theorem round_re_of_norm_small {v : ℂ} (h : ‖v‖ < 1 / 2) : round v.re = 0 := by
  have hr := abs_lt.mp ((Complex.abs_re_le_norm v).trans_lt h)
  exact round_eq_iff.mpr ⟨by norm_num; linarith [hr.1], by norm_num; linarith [hr.2]⟩

private theorem round_folded_probe_of_dvd {T : ℝ} (hT : 0 < T)
    (hclose : ∀ u : ℝ, Real.log 2 / 2 ≤ u → u ≤ Real.log 2 →
      ‖primeTwoOrdinateProbe T u - primeTwoOrdinateProfile T u‖ < 1 / 4)
    {d n : ℕ} (h : d ∣ n) : round (foldedOrdinateDivisorProbe T d n).re = 1 := by
  have hp := hclose (Real.log 2) (by linarith [folded_log_two_pos]) le_rfl
  rw [primeTwoOrdinateProfile_resonant hT] at hp
  rw [foldedOrdinateDivisorProbe, foldedPrimeTwoFrequency_eq_of_dvd h]
  exact round_re_of_profile_one (hp.trans (by norm_num))

private theorem round_folded_probe_of_gap {T : ℝ} (hT : 0 < T)
    (hclose : ∀ u : ℝ, Real.log 2 / 2 ≤ u → u ≤ Real.log 2 →
      ‖primeTwoOrdinateProbe T u - primeTwoOrdinateProfile T u‖ < 1 / 4)
    {d n : ℕ} (hd : 0 < d)
    (hgap : 8 ≤ (Real.log 2 - foldedPrimeTwoFrequency d n) * T) :
    round (foldedOrdinateDivisorProbe T d n).re = 0 := by
  let u := foldedPrimeTwoFrequency d n
  have hband := foldedPrimeTwoFrequency_mem (n := n) hd
  have hu : u < Real.log 2 := by
    by_contra! h
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hT.le
    linarith
  have hsmall : ‖primeTwoOrdinateProfile T u‖ ≤ 1 / 4 :=
    (norm_primeTwoOrdinateProfile_le hT hu).trans
      ((div_le_iff₀ (mul_pos (sub_pos.mpr hu) hT)).2 (by linarith))
  have hc := hclose u hband.1 hband.2
  change round (primeTwoOrdinateProbe T u).re = 0
  apply round_re_of_norm_small
  calc
    ‖primeTwoOrdinateProbe T u‖ = ‖(primeTwoOrdinateProbe T u - primeTwoOrdinateProfile T u) +
        primeTwoOrdinateProfile T u‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ < 1/2 := by linarith

/-- The original harmonic after folding needs one probe per divisor in a
linear range. The height threshold is uniform in both indices. -/
theorem eventually_round_foldedOrdinateDivisorProbe :
    ∀ᶠ T : ℝ in atTop, ∀ d n : ℕ, 0 < d → (d : ℝ) ≤ Real.log 2 * T / 16 →
      round (foldedOrdinateDivisorProbe T d n).re = if d ∣ n then 1 else 0 := by
  filter_upwards [eventually_primeTwoOrdinateProbe_profile_close (by norm_num : (0:ℝ) < 1/4),
    eventually_gt_atTop (0 : ℝ)] with T hclose hT
  intro d n hd hsize
  by_cases h : d ∣ n
  · simpa only [if_pos h] using round_folded_probe_of_dvd hT hclose h
  · rw [if_neg h]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    apply round_folded_probe_of_gap hT hclose hd
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (fold_gap_of_not_dvd hd h) hT.le)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith

/-- A nonzero residue doubles without wraparound up to its first entry into
the upper half of a period. -/
theorem exists_dyadic_mul_mod_ge_half {d n J : ℕ} (hd : 0 < d) (hn : ¬ d ∣ n)
    (hJ : d ≤ 2^(J+1)) : ∃ j ≤ J, d ≤ 2 * ((2^j * n) % d) := by
  classical
  let r := n % d
  have hr : 0 < r := Nat.pos_of_ne_zero (fun hz => hn (Nat.dvd_of_mod_eq_zero hz))
  have hrd : r < d := Nat.mod_lt n hd
  let P (j : ℕ) : Prop := d ≤ 2^(j+1) * r
  have hPJ : P J := hJ.trans (Nat.le_mul_of_pos_right _ hr)
  have hex : ∃ j, P j := ⟨J, hPJ⟩
  let j := Nat.find hex
  have hj : j ≤ J := Nat.find_min' hex hPJ
  have hjd : 2^j * r < d := by
    cases h : j with
    | zero => simpa only [h, pow_zero, one_mul] using hrd
    | succ k =>
      have hk : k < Nat.find hex := by change k < j; omega
      have hnot := Nat.find_min hex hk
      change ¬ d ≤ 2^(k+1)*r at hnot
      simpa only [h, Nat.succ_eq_add_one] using lt_of_not_ge hnot
  have hmod : (2^j * n) % d = 2^j * r := by
    change (2^j * n) % d = 2^j * (n % d)
    calc
      _ = (2^j * (n % d)) % d := by
        rw [Nat.mul_mod, Nat.mul_mod (2^j) (n % d), Nat.mod_mod]
      _ = _ := Nat.mod_eq_of_lt hjd
  have hspec : d ≤ 2^(j+1) * r := Nat.find_spec hex
  refine ⟨j, hj, ?_⟩
  simpa only [hmod, pow_succ, mul_assoc, mul_left_comm] using hspec

/-- Test the first `Nat.log 2 d + 1` dyadic multipliers, a list that depends
only on the divisor. The first false resonance is enough to reject. -/
def dyadicOrdinateDivisor (T : ℝ) (d n : ℕ) : ℤ := by
  classical
  exact if ∀ j ∈ Finset.range (Nat.log 2 d + 1),
      round (foldedOrdinateDivisorProbe T d (2^j * n)).re = 1 then 1 else 0

/-- One height threshold now works for every positive divisor and every
harmonic simultaneously. -/
theorem eventually_dyadicOrdinateDivisor_eq :
    ∀ᶠ T : ℝ in atTop, ∀ d n : ℕ, 0 < d →
      dyadicOrdinateDivisor T d n = if d ∣ n then 1 else 0 := by
  classical
  filter_upwards [eventually_primeTwoOrdinateProbe_profile_close (by norm_num : (0:ℝ) < 1/4),
    eventually_ge_atTop (32 / Real.log 2)] with T hclose hT
  have hTp : 0 < T := (div_pos (by norm_num) folded_log_two_pos).trans_le hT
  intro d n hd
  unfold dyadicOrdinateDivisor
  by_cases hn : d ∣ n
  · rw [if_pos hn, if_pos]
    intro j _
    exact round_folded_probe_of_dvd hTp hclose (dvd_mul_of_dvd_right hn _)
  · rw [if_neg hn, if_neg]
    intro hall
    have hbound : d ≤ 2^(Nat.log 2 d + 1) :=
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) d).le
    obtain ⟨j, hj, hr⟩ := exists_dyadic_mul_mod_ge_half hd hn hbound
    have h := hall j (Finset.mem_range.mpr (by omega))
    have hgap := fold_gap_of_large_residue hd hr
    have hscale : 8 ≤ Real.log 2 / 4 * T := by
      have ht := (div_le_iff₀ folded_log_two_pos).mp hT
      linarith only [ht]
    have hz := round_folded_probe_of_gap hTp hclose hd
      (hscale.trans (mul_le_mul_of_nonneg_right hgap hTp.le))
    exact zero_ne_one (hz.symm.trans h)

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.ActualZeroOrdinate

/-- Signed Möbius synthesis from integer-valued divisibility probes. -/
def ordinateRamanujanSumFromDivisor (probe : ℕ → ℕ → ℤ) (q n : ℕ) : ℤ :=
  ∑ d ∈ q.divisors, ArithmeticFunction.moebius (q/d) * (d : ℤ) * probe d n

private theorem ordinateRamanujanSumFromDivisor_eq {probe : ℕ → ℕ → ℤ} {q n : ℕ}
    (h : ∀ d ∈ q.divisors, probe d n = if d ∣ n then 1 else 0) :
    (ordinateRamanujanSumFromDivisor probe q n : ℝ) = ramanujanSum q n := by
  simp only [ordinateRamanujanSumFromDivisor, ramanujanSum, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro d hd
  rw [h d hd]
  by_cases hn : d ∣ n <;> simp [hn]

/-- Reconstruct an integrated packet from one period of the signed sum. -/
def ordinateRamanujanPacketFromDivisor (probe : ℕ → ℕ → ℤ) (q k : ℕ) : ℤ :=
  -(∑ n ∈ Finset.Ico 1 (k % q + 1), ordinateRamanujanSumFromDivisor probe q n)

private theorem ordinateRamanujanPacketFromDivisor_eq {probe : ℕ → ℕ → ℤ} {q : ℕ}
    (hq : 1 < q) (h : ∀ n, (ordinateRamanujanSumFromDivisor probe q n : ℝ) = ramanujanSum q n)
    (k : ℕ) : (ordinateRamanujanPacketFromDivisor probe q k : ℝ) = ramanujanPacket q k := by
  have hper : ramanujanPacket q k = ramanujanPacket q (k % q) := by
    simpa only [Nat.mod_add_div] using
      ramanujanPacket_period_of_dvd q (q*(k/q)) (dvd_mul_right q _) (k%q)
  rw [hper, ramanujanPacket_prefix q (k%q) hq]
  simp only [ordinateRamanujanPacketFromDivisor, Int.cast_neg, Int.cast_sum, h]

/-- Exact single-probe recovery of every harmonic in the explicit linear
range, at one and the same height. -/
theorem eventually_single_folded_ordinate_ramanujan :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ Real.log 2 * T / 16 → ∀ n : ℕ,
      (ordinateRamanujanSumFromDivisor
        (fun d m => round (foldedOrdinateDivisorProbe T d m).re) q n : ℝ) = ramanujanSum q n := by
  filter_upwards [eventually_round_foldedOrdinateDivisorProbe] with T hT
  intro q hq n
  apply ordinateRamanujanSumFromDivisor_eq
  intro d hd
  have hdiv := Nat.mem_divisors.mp hd
  have hdq : d ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hdiv.2) hdiv.1
  exact hT d n (Nat.pos_of_mem_divisors hd) ((by exact_mod_cast hdq : (d:ℝ) ≤ q).trans hq)

/-- At every sufficiently large height, the same actual zero cutoff recovers
all Ramanujan sums and all integrated packet rows, without a conductor bound. -/
theorem eventually_dyadic_ordinate_ramanujan_reconstruction :
    ∀ᶠ T : ℝ in atTop,
      (∀ q n : ℕ, (ordinateRamanujanSumFromDivisor (dyadicOrdinateDivisor T) q n : ℝ) =
        ramanujanSum q n) ∧
      (∀ q k : ℕ, 1 < q →
        (ordinateRamanujanPacketFromDivisor (dyadicOrdinateDivisor T) q k : ℝ) =
          ramanujanPacket q k) := by
  filter_upwards [eventually_dyadicOrdinateDivisor_eq] with T hT
  have hsum (q n : ℕ) : (ordinateRamanujanSumFromDivisor (dyadicOrdinateDivisor T) q n : ℝ) =
      ramanujanSum q n := ordinateRamanujanSumFromDivisor_eq
        (fun d hd => hT d n (Nat.pos_of_mem_divisors hd))
  exact ⟨hsum, fun q k hq => ordinateRamanujanPacketFromDivisor_eq hq (hsum q) k⟩

/--
info: 'RiemannResearch.RH.Pareto.eventually_single_folded_ordinate_ramanujan' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_single_folded_ordinate_ramanujan

/--
info: 'RiemannResearch.RH.Pareto.eventually_dyadic_ordinate_ramanujan_reconstruction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_dyadic_ordinate_ramanujan_reconstruction

end RiemannResearch.RH.Pareto
