/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.QResidueConditionalBounds
import RiemannResearch.RH.QPeriodicTailEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.CRTCarryArithmetic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.LogSquareTail
import RiemannResearch.Analysis.LogTailWeights
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q CRT conditioning of the reciprocal source

Source: the user's infinite-CRT squarefree response request, 26 October 2026.
Every fiber retains its complete infinite Q progression. The reciprocal bias
has an exact signed identity and a quantitative bound. The ambient conditioned
source has a uniform physical bound and a complete weighted-energy budget.
Membership in the legal squarefree span is not asserted. The actual legal
projection is assembled separately in QSquarefreeCRTResponse.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QReciprocalConditioning
open ZetaTwoProbability ZetaTwoHilbert QShiftedReciprocal
open QResidueConditional QPolylogTailEnergy ArithmeticCumulative
open RiemannResearch.Analysis RiemannResearch.Analysis.LogTailWeights

def reciprocal (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem reciprocal_nonneg (n : ℕ) : 0 ≤ reciprocal n := by
  unfold reciprocal
  positivity

theorem reciprocal_abs_le_one (n : ℕ) : |reciprocal n| ≤ 1 := by
  rw [abs_of_nonneg (reciprocal_nonneg n)]
  unfold reciprocal
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem reciprocal_antitone {m n : ℕ} (hmn : m ≤ n) :
    reciprocal n ≤ reciprocal m := by
  apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1)
  exact_mod_cast Nat.add_le_add_right hmn 1

def reciprocalMean (L a : ℕ) : ℝ := conditionalValue L a reciprocal

/-- Exact signed source factorization for every periodic residual. -/
theorem conditionalValue_reciprocal_mul (L a : ℕ) (r : ℕ → ℝ)
    (hr : ∀ n, r (n + L) = r n) :
    conditionalValue L a (fun n => r n / ((n : ℝ) + 1)) =
      r a * reciprocalMean L a := by
  simpa only [reciprocalMean, reciprocal, div_eq_mul_inv, one_mul] using
    conditionalValue_mul_of_periodic L a r reciprocal hr

private theorem fiberWeight_eq (L a : ℕ) :
    (∑' j : ℕ, positiveQWeight (a + L * j)) = residuePowerWeight 0 L a := by
  unfold residuePowerWeight
  apply tsum_congr
  intro j
  simp only [positiveQWeight, Nat.cast_add, Nat.cast_mul, Nat.zero_add, mul_comm]

private theorem fiberWeight_summable (L a : ℕ) (hL : 0 < L) (ha : 0 < a) :
    Summable (fun j : ℕ => positiveQWeight (a + L * j)) := by
  convert residuePowerWeight_summable 0
    (show (0 : ℝ) < L by exact_mod_cast hL)
    (show (0 : ℝ) < a by exact_mod_cast ha) using 1
  simp only [positiveQWeight, Nat.cast_add, Nat.cast_mul, Nat.zero_add, mul_comm]

/-- Exact complete-tail bias; its first summand vanishes, and every other term is kept. -/
theorem reciprocalMean_defect_exact (L a : ℕ) (hL : 0 < L) (ha : 0 < a) :
    reciprocal a - reciprocalMean L a =
      (∑' j : ℕ, positiveQWeight (a + L * j) *
        (reciprocal a - reciprocal (a + L * j))) / residuePowerWeight 0 L a := by
  have h := conditionalValue_smul_sub L a hL ha (reciprocal a)
    (fun _ => (1 : ℝ)) reciprocal (C := 1) (D := 1)
    (by intro n; norm_num) reciprocal_abs_le_one
  rw [conditionalValue_of_periodic L a hL ha (fun _ => (1 : ℝ))
    (by intro n; rfl)] at h
  simpa only [reciprocalMean, conditionalValue, fiberSum, mul_one] using h.symm

/-- The exact complete tail controls the reciprocal bias before division. -/
theorem reciprocalMean_defect_weighted (L a : ℕ) (hL : 0 < L) (ha : 0 < a) :
    0 ≤ reciprocal a - reciprocalMean L a ∧
      residuePowerWeight 0 L a * (reciprocal a - reciprocalMean L a) ≤
        reciprocal a * residuePowerWeight 0 L ((a : ℝ) + L) := by
  have hwpos : 0 < residuePowerWeight 0 L a :=
    residuePowerWeight_pos 0 (by exact_mod_cast hL) (by exact_mod_cast ha)
  have hs := fiber_terms_summable L a hL ha reciprocal reciprocal_abs_le_one
  have hweight := fiberWeight_summable L a hL ha
  have hupper : fiberSum L a reciprocal ≤
      residuePowerWeight 0 L a * reciprocal a := by
    calc
      fiberSum L a reciprocal ≤
          ∑' j : ℕ, positiveQWeight (a + L * j) * reciprocal a := by
        apply Summable.tsum_le_tsum _ hs (hweight.mul_right _)
        intro j
        exact mul_le_mul_of_nonneg_left
          (reciprocal_antitone (Nat.le_add_right a (L * j)))
          (positiveQWeight_nonneg _)
      _ = _ := by rw [tsum_mul_right, fiberWeight_eq]
  have hlower : positiveQWeight a * reciprocal a ≤ fiberSum L a reciprocal := by
    simpa only [fiberSum, Nat.mul_zero, Nat.add_zero] using hs.le_tsum 0
      (fun j _ => mul_nonneg (positiveQWeight_nonneg _) (reciprocal_nonneg _))
  have hmean : residuePowerWeight 0 L a * reciprocalMean L a =
      fiberSum L a reciprocal := by
    unfold reciprocalMean conditionalValue
    field_simp [ne_of_gt hwpos]
  have hshift := residuePowerWeight_shift 0
    (show (0 : ℝ) < L by exact_mod_cast hL)
    (show (0 : ℝ) < a by exact_mod_cast ha)
  change residuePowerWeight 0 L a = positiveQWeight a +
    residuePowerWeight 0 L ((a : ℝ) + L) at hshift
  constructor
  · exact nonneg_of_mul_nonneg_right
      (show 0 ≤ residuePowerWeight 0 L a *
        (reciprocal a - reciprocalMean L a) by nlinarith) hwpos
  · rw [mul_sub, hmean, hshift]
    nlinarith

/-- Quantitative scalar bias, with the complete progression tail retained. -/
theorem reciprocalMean_defect_bound (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L) :
    0 ≤ reciprocal a - reciprocalMean L a ∧
      reciprocal a - reciprocalMean L a ≤
        zetaTwo * (a : ℝ) ^ 2 / ((L : ℝ) ^ 2 * ((a : ℝ) + 1)) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  obtain ⟨hzero, hweighted⟩ := reciprocalMean_defect_weighted L a hL ha
  refine ⟨hzero, ?_⟩
  have htail := (residueSquareWeight_tail_bounds L hL haR
    (show (a : ℝ) ≤ L by exact_mod_cast haL)).2
  have hfirst := residueSquareWeight_lower hLR haR
  have hbound : (1 / (zetaTwo * (a : ℝ) ^ 2)) *
      (reciprocal a - reciprocalMean L a) ≤ reciprocal a * (1 / (L : ℝ) ^ 2) :=
    (mul_le_mul_of_nonneg_right hfirst hzero).trans
      (hweighted.trans (mul_le_mul_of_nonneg_left htail (reciprocal_nonneg a)))
  have hZ : 0 < zetaTwo * (a : ℝ) ^ 2 := by
    have := zetaTwo_pos
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hbound hZ.le
  have he : (zetaTwo * (a : ℝ) ^ 2) *
      ((1 / (zetaTwo * (a : ℝ) ^ 2)) *
        (reciprocal a - reciprocalMean L a)) =
      reciprocal a - reciprocalMean L a := by
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt haR]
  rw [he] at hscaled
  calc
    _ ≤ zetaTwo * (a : ℝ) ^ 2 * (reciprocal a * (1 / (L : ℝ) ^ 2)) := hscaled
    _ = _ := by
      simp only [reciprocal, div_eq_mul_inv, mul_inv_rev, one_mul]

/-- The actual Q-fiber conditional mean of Bf at each positive physical site.
Residue zero is represented by L, and the auxiliary site zero is set to zero. -/
def conditionalReciprocalSequence (L : ℕ) (f : QHilbert) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    conditionalValue L ((n - 1) % L + 1) (qSequence (B f))

theorem conditionalReciprocalSequence_bound
    (L : ℕ) (hL : 0 < L) (f : QHilbert) (n : ℕ) :
    |conditionalReciprocalSequence L f n| ≤ Real.sqrt zetaTwo * ‖f‖ := by
  by_cases hn : n = 0
  · simp only [conditionalReciprocalSequence, if_pos hn, abs_zero]
    positivity
  · simp only [conditionalReciprocalSequence, if_neg hn]
    exact conditionalValue_abs_le L ((n - 1) % L + 1) hL (Nat.succ_pos _)
      (qSequence (B f)) (Real.sqrt zetaTwo * ‖f‖) (by positivity)
      (B_physical_bound f)

/-- An ambient CRT cylinder. Membership in the legal squarefree span is not asserted. -/
def conditionalReciprocal (L : ℕ) (hL : 0 < L) (f : QHilbert) : QHilbert :=
  encodeQ (conditionalReciprocalSequence L f)
    (boundedQ_square_summable _ (Real.sqrt zetaTwo * ‖f‖) (by positivity)
      (conditionalReciprocalSequence_bound L hL f))

@[simp] theorem qSequence_conditionalReciprocal
    (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    qSequence (conditionalReciprocal L hL f) = conditionalReciprocalSequence L f :=
  qSequence_encodeQ _ _ (by simp [conditionalReciprocalSequence])

theorem conditionalReciprocal_bound
    (L : ℕ) (hL : 0 < L) (f : QHilbert) (n : ℕ) :
    |qSequence (conditionalReciprocal L hL f) n| ≤ Real.sqrt zetaTwo * ‖f‖ := by
  rw [qSequence_conditionalReciprocal]
  exact conditionalReciprocalSequence_bound L hL f n

/-- The same complete weighted energy is finite for every modulus. -/
theorem conditionalReciprocal_energy_summable
    (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    Summable (polylogWeightedEnergyTerm 2 (conditionalReciprocal L hL f)) := by
  apply polylogWeightedEnergyTerm_summable (conditionalReciprocal L hL f)
    0 (Real.sqrt zetaTwo * ‖f‖) (by positivity)
  intro n
  simpa only [pow_zero, mul_one] using conditionalReciprocal_bound L hL f n

/-- A uniform explicit complete-energy budget for the conditioned reciprocal source. -/
theorem conditionalReciprocal_energy_le
    (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    (∑' n, polylogWeightedEnergyTerm 2 (conditionalReciprocal L hL f) n) ≤
      ‖f‖ ^ 2 * (∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
  have hCeq : (Real.sqrt zetaTwo * ‖f‖) ^ 2 / zetaTwo = ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt zetaTwo_pos.le]
    field_simp [zetaTwo_pos.ne']
  have hmajor (n : ℕ) :
      polylogWeightedEnergyTerm 2 (conditionalReciprocal L hL f) n ≤
        ‖f‖ ^ 2 * (1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
    have hh := polylogWeightedEnergyTerm_le_log_square
      (conditionalReciprocal L hL f) 0 n (Real.sqrt zetaTwo * ‖f‖)
      (by simpa only [pow_zero, mul_one] using conditionalReciprocal_bound L hL f n)
    simpa only [Nat.mul_zero, Nat.zero_add, hCeq] using hh
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
    simpa only [Real.rpow_two] using summable_shifted_log_square
  have hh := (conditionalReciprocal_energy_summable L hL f).tsum_le_tsum
    hmajor (hsum.mul_left (‖f‖ ^ 2))
  simpa only [tsum_mul_left] using hh

theorem conditionalReciprocalSequence_fiber
    (L a : ℕ) (ha : 0 < a) (haL : a ≤ L)
    (f : QHilbert) (j : ℕ) :
    conditionalReciprocalSequence L f (a + L * j) =
      conditionalValue L a (qSequence (B f)) := by
  have hn : a + L * j ≠ 0 := by omega
  have hsub : a + L * j - 1 = (a - 1) + L * j := by omega
  have haLt : a - 1 < L := by omega
  have hrep : (a + L * j - 1) % L + 1 = a := by
    rw [hsub]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
      add_zero, Nat.mod_eq_of_lt haLt]
    omega
  simp only [conditionalReciprocalSequence, if_neg hn, hrep]

/-- Complete mass and first moment agree on each individual Q residue fiber. -/
theorem conditionalReciprocal_fiberSum
    (L a : ℕ) (hL : 0 < L) (ha : 0 < a) (haL : a ≤ L)
    (f : QHilbert) :
    fiberSum L a (conditionalReciprocalSequence L f) =
      fiberSum L a (qSequence (B f)) := by
  have hmass : (∑' j : ℕ, positiveQWeight (a + L * j)) =
      residuePowerWeight 0 L a := by
    simpa only [fiberSum, mul_one] using
      fiberSum_of_periodic L a (fun _ => (1 : ℝ)) (fun _ => rfl)
  unfold fiberSum
  simp_rw [conditionalReciprocalSequence_fiber L a ha haL f]
  rw [tsum_mul_right, hmass, conditionalValue]
  have hw : residuePowerWeight 0 L a ≠ 0 :=
    ne_of_gt (residuePowerWeight_pos 0 (by exact_mod_cast hL) (by exact_mod_cast ha))
  change residuePowerWeight 0 L a *
      (fiberSum L a (qSequence (B f)) / residuePowerWeight 0 L a) =
    fiberSum L a (qSequence (B f))
  field_simp [hw]

/-- Exact finite-fiber pairing identity against any bounded positive-periodic test. -/
theorem conditionalReciprocal_inversePowerMean_mul
    (L : ℕ) (hL : 0 < L) (f : QHilbert)
    (g : ℕ → ℝ) {D : ℝ} (hg : ∀ n, |g n| ≤ D)
    (hperiod : ∀ n, 0 < n → g (n + L) = g n) :
    inversePowerMean 0 (fun n => conditionalReciprocalSequence L f n * g n) =
      inversePowerMean 0 (fun n => qSequence (B f) n * g n) := by
  rw [inversePowerMean_eq_sum_fiber L hL _
    (Pareto.bounded_product (conditionalReciprocalSequence_bound L hL f) hg)]
  rw [inversePowerMean_eq_sum_fiber L hL _
    (Pareto.bounded_product (B_physical_bound f) hg)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [fiberSum_mul_pos_periodic L (a.val + 1) (Nat.succ_pos _) _ g hperiod,
    fiberSum_mul_pos_periodic L (a.val + 1) (Nat.succ_pos _) _ g hperiod,
    conditionalReciprocal_fiberSum L (a.val + 1) hL (Nat.succ_pos _)
      (Nat.succ_le_iff.mpr a.isLt) f]

/-- Q-inner products are preserved against every bounded positive-periodic vector. -/
theorem conditionalReciprocal_inner_periodic
    (L : ℕ) (hL : 0 < L) (f g : QHilbert)
    {D : ℝ} (hg : ∀ n, |qSequence g n| ≤ D)
    (hperiod : ∀ n, 0 < n → qSequence g (n + L) = qSequence g n) :
    inner ℝ (conditionalReciprocal L hL f) g = inner ℝ (B f) g := by
  rw [qInner_eq_inversePowerMean, qInner_eq_inversePowerMean,
    qSequence_conditionalReciprocal]
  exact conditionalReciprocal_inversePowerMean_mul L hL f (qSequence g) hg hperiod

/-- In particular every conductor dividing the CRT period keeps its exact moment. -/
theorem conditionalReciprocal_inner_residue
    (L d : ℕ) (hL : 0 < L) (hdL : d ∣ L) (f : QHilbert) :
    inner ℝ (qResidue d) (conditionalReciprocal L hL f) =
      inner ℝ (qResidue d) (B f) := by
  rw [real_inner_comm (conditionalReciprocal L hL f) (qResidue d),
    real_inner_comm (B f) (qResidue d)]
  apply conditionalReciprocal_inner_periodic L hL f (qResidue d)
  · intro n
    rw [qSequence_qResidue]
    exact CRTCarryArithmetic.residueFraction_abs_le_one d n
  · intro n hn
    simp only [qSequence_qResidue]
    exact residueFraction_period_of_dvd d L hdL n

/-- Uniform physical error for bounded reciprocal inputs on the first CRT period. -/
theorem conditionalReciprocal_sequence_error_bound
    (L n : ℕ) (hL : 0 < L) (hn : 0 < n) (hnL : n ≤ L) (f : QHilbert) :
    |qSequence (conditionalReciprocal L hL f) n - qSequence (B f) n| ≤
      2 * (Real.sqrt zetaTwo * ‖f‖) * zetaTwo * (n : ℝ) ^ 2 / (L : ℝ) ^ 2 := by
  rw [qSequence_conditionalReciprocal]
  have he := conditionalReciprocalSequence_fiber L n hn hnL f 0
  simp only [Nat.mul_zero, Nat.add_zero] at he
  rw [he]
  exact conditionalValue_deviation_bound L n hL hn (qSequence (B f))
    (Real.sqrt zetaTwo * ‖f‖) (by positivity) (B_physical_bound f)

/-- The infinite-modulus passage is valid in the complete weighted energy,
even for an arbitrary norm-bounded family of inputs. This theorem precedes
the legal projection and does not assume its weighted boundedness. -/
theorem conditionalReciprocal_weighted_error_tendsto_zero
    (f : ℕ → QHilbert) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ j, ‖f j‖ ≤ C)
    (L : ℕ → ℕ) (hLp : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => ∑' n : ℕ, polylogWeightedEnergyTerm 2
      (conditionalReciprocal (L j) (hLp j) (f j) - B (f j)) n) atTop (𝓝 0) := by
  let e : ℕ → QHilbert := fun j => conditionalReciprocal (L j) (hLp j) (f j) - B (f j)
  let D : ℝ := Real.sqrt zetaTwo * (2 * C)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hseq (j n : ℕ) : qSequence (e j) n =
      qSequence (conditionalReciprocal (L j) (hLp j) (f j)) n - qSequence (B (f j)) n := by
    change qSequenceLinear (conditionalReciprocal (L j) (hLp j) (f j) - B (f j)) n = _
    rw [map_sub]
    rfl
  have hb (j n : ℕ) : |qSequence (e j) n| ≤ D := by
    rw [hseq]
    have hc := conditionalReciprocal_bound (L j) (hLp j) (f j) n
    have hs := B_physical_bound (f j) n
    have hm := mul_le_mul_of_nonneg_left (hf j) (Real.sqrt_nonneg zetaTwo)
    have ht : |qSequence (conditionalReciprocal (L j) (hLp j) (f j)) n -
        qSequence (B (f j)) n| ≤
        |qSequence (conditionalReciprocal (L j) (hLp j) (f j)) n| +
          |qSequence (B (f j)) n| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (qSequence (conditionalReciprocal (L j) (hLp j) (f j)) n) 0
          (qSequence (B (f j)) n)
    dsimp [D]
    linarith
  have hcast : Tendsto (fun j => (L j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hL
  have hden : Tendsto (fun j => (L j : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hcast
  have habslim (n : ℕ) : Tendsto (fun j => |qSequence (e j) n|) atTop (𝓝 0) := by
    by_cases hn : n = 0
    · subst n
      simpa only [qSequence_zero, abs_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hquot : Tendsto (fun j =>
        (2 * (Real.sqrt zetaTwo * C) * zetaTwo * (n : ℝ) ^ 2) / (L j : ℝ) ^ 2)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
    apply squeeze_zero' (Eventually.of_forall (fun j => abs_nonneg _)) _ hquot
    filter_upwards [hL.eventually (eventually_ge_atTop n)] with j hj
    rw [hseq]
    have hh := conditionalReciprocal_sequence_error_bound (L j) n (hLp j)
      (Nat.pos_of_ne_zero hn) hj (f j)
    have hm := mul_le_mul_of_nonneg_left (hf j) (Real.sqrt_nonneg zetaTwo)
    have hnum : 2 * (Real.sqrt zetaTwo * ‖f j‖) * zetaTwo * (n : ℝ) ^ 2 ≤
        2 * (Real.sqrt zetaTwo * C) * zetaTwo * (n : ℝ) ^ 2 := by
      have hz := zetaTwo_pos
      nlinarith [mul_le_mul_of_nonneg_right hm
        (show 0 ≤ 2 * zetaTwo * (n : ℝ) ^ 2 by positivity)]
    exact hh.trans (div_le_div_of_nonneg_right hnum (sq_nonneg _))
  have hlim (n : ℕ) : Tendsto
      (fun j => polylogWeightedEnergyTerm 2 (e j) n) atTop (𝓝 0) := by
    have hh := ((habslim n).pow 2).const_mul
      (polylogTailProfile 2 n * positiveQWeight n)
    simpa only [polylogWeightedEnergyTerm, sq_abs, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using hh
  have hDeq : D ^ 2 / zetaTwo = (2 * C) ^ 2 := by
    dsimp [D]
    rw [mul_pow, Real.sq_sqrt zetaTwo_pos.le]
    field_simp [zetaTwo_pos.ne']
  let major : ℕ → ℝ := fun n =>
    (2 * C) ^ 2 * (1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2))
  have hmajor_sum : Summable major := by
    have hs : Summable (fun n : ℕ =>
        1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
      simpa only [Real.rpow_two] using summable_shifted_log_square
    exact hs.mul_left _
  have hmajor (j n : ℕ) : ‖polylogWeightedEnergyTerm 2 (e j) n‖ ≤ major n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (polylogWeightedEnergyTerm_nonneg 2 (e j) n)]
    have hh := polylogWeightedEnergyTerm_le_log_square (e j) 0 n D
      (by simpa only [pow_zero, mul_one] using hb j n)
    simpa only [Nat.mul_zero, Nat.zero_add, hDeq, major] using hh
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun j n => polylogWeightedEnergyTerm 2 (e j) n)
    (g := fun _ : ℕ => (0 : ℝ)) hmajor_sum hlim
    (Eventually.of_forall hmajor)
  simpa only [tsum_zero, e] using ht

end RiemannResearch.RH.QReciprocalConditioning
