/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.RvM.MainTerm
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Complete
import RiemannResearch.Analysis.HighMomentTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import RiemannResearch.RH.WeilExplicitFormula.RvM.GammaSide
import RiemannResearch.RH.WeilExplicitFormula.RvM.LocalCount
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Actual zero-count discrepancy and high-moment interface

We use the exact gamma density, not an asymptotic main term:
`smoothCount t = integral_0^t mu` and
`discrepancy t = Ncount 0 t - smoothCount t`.
The count includes the upper endpoint and excludes the lower endpoint, with
actual analytic multiplicities. At good heights above 1, discrepancy increments
are exactly the imaginary zeta logarithmic-derivative half-contour divided by pi.

The discrepancy is an equivalent increment interface for the continued zeta
argument. No principal-argument identification is made. A separate conventional
argument lift and its absolute additive normalization are not constructed here.
The exact contour theorem is proved using the existing folded argument principle,
the completed-zeta splitting, and the exact gamma-side integral identity.

Every finite norm power of a shifted discrepancy, its increments, and its
remainder against a continuous approximant is interval-integrable. The bad
heights are countable. Endpoint changes and constant normalizations therefore do
not change increment moments. Transfer bounds leave all quantitative polynomial
and remainder budgets explicit.

Provenance: Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed.,
Sections 9.3--9.4, for the counting/argument identity; the existing
`Zeta23.RvM` modules supply its formal proof.
Simonic, Trudgian and Turnage-Butterbaugh,
https://arxiv.org/abs/2010.10675, Sections 1, 3--4, for the argument convention
and high-moment application. The measure-theoretic assembly below is elementary.
No novelty or proof of the Selberg approximation, Tsang asymptotic, or RH is claimed.
-/

open MeasureTheory Set Zeta23 RiemannResearch.HighMomentTransfer
open scoped Interval
namespace RiemannResearch.Analysis.ActualZeroDiscrepancy
/-- Exact smooth gamma contribution, with base point zero. -/
noncomputable def smoothCount (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, mu u
/-- Upper-inclusive actual zero count minus the exact smooth gamma contribution. -/
noncomputable def discrepancy (t : ℝ) : ℝ := (Ncount 0 t : ℝ) - smoothCount t

/-- The smooth main term is continuous on the entire real line. -/
theorem smoothCount_continuous : Continuous smoothCount :=
  intervalIntegral.continuous_primitive
    (fun a b => (RvM.mu_continuous gammaFacts).intervalIntegrable a b) 0

/-- Exact smooth increment, with no Stirling error discarded. -/
theorem smoothCount_sub (a b : ℝ) :
    smoothCount b - smoothCount a = ∫ u in a..b, mu u := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    ((RvM.mu_continuous gammaFacts).intervalIntegrable (μ := volume) 0 a)
    ((RvM.mu_continuous gammaFacts).intervalIntegrable a b)
  dsimp [smoothCount]
  linarith

/-- Monotonicity retains every zero's actual analytic multiplicity. -/
theorem count_monotone : Monotone (fun t : ℝ => (Ncount 0 t : ℝ)) := by
  intro a b hab
  change (Ncount 0 a : ℝ) ≤ (Ncount 0 b : ℝ)
  exact_mod_cast Ncount_mono (a := 0) (b := a) (c := 0) (d := b) le_rfl hab

/-- Measurability follows from a monotone count and a continuous main term. -/
theorem discrepancy_measurable : Measurable discrepancy :=
  count_monotone.measurable.sub smoothCount_continuous.measurable

/-- The discrepancy is integrable on every finite interval, despite its jumps. -/
theorem discrepancy_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable discrepancy volume a b :=
  count_monotone.intervalIntegrable.sub (smoothCount_continuous.intervalIntegrable a b)

/-- Exact centered window identity, valid also when an endpoint is a zero height. -/
theorem discrepancy_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    discrepancy b - discrepancy a = (Ncount a b : ℝ) - ∫ u in a..b, mu u := by
  have he : (Ncount 0 b : ℝ) = (Ncount 0 a : ℝ) + (Ncount a b : ℝ) := by
    exact_mod_cast Ncount_add ha hab
  dsimp [discrepancy]
  rw [show (Ncount 0 b : ℝ) - smoothCount b - ((Ncount 0 a : ℝ) - smoothCount a) =
    ((Ncount 0 b : ℝ) - (Ncount 0 a : ℝ)) - (smoothCount b - smoothCount a) by ring,
    smoothCount_sub, he]
  ring

/-- Nonnegative-shift form of the exact centered window identity. -/
theorem discrepancy_increment {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    discrepancy (t + h) - discrepancy t = (Ncount t (t + h) : ℝ) - ∫ u in t..t+h, mu u :=
  discrepancy_sub ht (by linarith)

/-- The exact bridge to continued zeta-argument variation at good heights. -/
theorem discrepancy_sub_eq_zeta_halfContour {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hga : RvM.GoodHeight a) (hgb : RvM.GoodHeight b) :
    discrepancy b - discrepancy a =
      (1 / Real.pi) * (RvM.halfContour (logDeriv riemannZeta) a b).im := by
  rw [discrepancy_sub (by linarith) hab.le, RvM.N_eq_halfContour_completedZeta ha hab hga hgb,
    RvM.halfContour_completedZeta_split ha hab hga hgb, Complex.add_im, mul_add,
    RvM.gamma_side (by linarith : 0 < a) (by linarith : 0 < b)]
  ring


/-- All finite powers of the nonnegative shifted count are locally integrable. -/
theorem count_shift_pow_intervalIntegrable (h a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => ‖(Ncount 0 (t + h) : ℝ)‖ ^ n) volume a b := by
  have hm : Monotone (fun t : ℝ => (Ncount 0 (t + h) : ℝ) ^ n) := by
    intro s t hst
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (count_monotone (by linarith)) n
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using
    (hm.intervalIntegrable (a := a) (b := b) (μ := volume))

theorem discrepancy_sub_continuous_shift_pow_intervalIntegrable
    (f : ℝ → ℝ) (hf : Continuous f) (h a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => ‖discrepancy (t + h) - f (t + h)‖ ^ n) volume a b := by
  have hc : Continuous (fun t => smoothCount (t + h) + f (t + h)) :=
    (smoothCount_continuous.add hf).comp (continuous_id.add continuous_const)
  have hi := norm_sub_pow_intervalIntegrable
    (count_monotone.measurable.comp (measurable_id.add measurable_const))
    hc.measurable a b n (count_shift_pow_intervalIntegrable h a b n)
    ((hc.norm.pow n).intervalIntegrable a b)
  convert hi using 1
  funext t
  congr 2
  simp only [discrepancy, Function.comp_apply, Pi.add_apply, id_eq]
  ring

/-- All finite powers of a shifted discrepancy are locally integrable. -/
theorem discrepancy_shift_pow_intervalIntegrable (h a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => ‖discrepancy (t + h)‖ ^ n) volume a b := by
  simpa only [sub_zero] using
    discrepancy_sub_continuous_shift_pow_intervalIntegrable (fun _ => 0)
      continuous_const h a b n

/-- The regularity premise required by HighMomentTransfer, discharged unconditionally. -/
theorem discrepancy_increment_pow_intervalIntegrable (h a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => ‖discrepancy (t + h) - discrepancy t‖ ^ n) volume a b := by
  exact norm_sub_pow_intervalIntegrable
    (discrepancy_measurable.comp (measurable_id.add measurable_const))
    discrepancy_measurable a b n (discrepancy_shift_pow_intervalIntegrable h a b n)
    (by simpa only [add_zero] using discrepancy_shift_pow_intervalIntegrable 0 a b n)

/-- Local finiteness of actual zeros makes the exceptional ordinates countable. -/
theorem badHeights_countable : Set.Countable {t : ℝ | ¬ RvM.GoodHeight t} := by
  have hc : Set.Countable (⋃ n : ℕ, Complex.im '' zerosIn (-(n:ℝ)) n) :=
    Set.countable_iUnion fun n => ((zerosIn_finite (-(n:ℝ)) n).countable.image _)
  apply hc.mono
  intro t ht
  simp only [RvM.GoodHeight, not_forall, not_not] at ht
  obtain ⟨ρ, hρ, he⟩ := ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  apply Set.mem_iUnion.mpr
  refine ⟨n, ρ, ?_, he⟩
  exact ⟨hρ, by rw [he]; linarith [neg_abs_le t], by rw [he]; linarith [le_abs_self t]⟩

/-- Almost every real height is free of nontrivial zeta zeros. -/
theorem ae_goodHeight : ∀ᵐ t : ℝ, RvM.GoodHeight t := by
  exact ae_iff.mpr (badHeights_countable.measure_zero volume)

/-- The same exceptional-set statement after any fixed real translation. -/
theorem ae_goodHeight_shift (h : ℝ) : ∀ᵐ t : ℝ, RvM.GoodHeight (t + h) := by
  apply ae_iff.mpr
  have hc : Set.Countable {t : ℝ | ¬ RvM.GoodHeight (t + h)} :=
    (badHeights_countable.image (fun t => t-h)).mono (by
      intro t ht
      exact ⟨t+h, ht, by ring⟩)
  exact hc.measure_zero volume

open RiemannResearch.HighMomentTransfer

/-- Endpoint modifications and a fixed additive normalization preserve moments. -/
theorem evenMoment_eq_of_eqOn_goodHeights (S : ℝ → ℝ) (c : ℝ)
    (hS : ∀ t, RvM.GoodHeight t → S t = discrepancy t + c)
    (h a b : ℝ) (k : ℕ) :
    evenMoment (fun t => S (t + h) - S t) k a b =
    evenMoment (fun t => discrepancy (t + h) - discrepancy t) k a b := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_goodHeight, ae_goodHeight_shift h] with t ht hth
  intro _
  rw [hS t ht, hS (t + h) hth]
  congr 2
  ring

theorem increment_evenMoment_le_continuous_approximation
    (f : ℝ → ℝ) (hf : Continuous f) (h a b : ℝ) (hab : a ≤ b)
    (k : ℕ) (hk : 1 ≤ k) :
    evenMoment (fun t => discrepancy (t + h) - discrepancy t) k a b ≤
      (3 : ℝ) ^ (2 * k - 1) *
        (evenMoment (fun t => f (t + h) - f t) k a b +
          evenMoment (fun t => discrepancy (t + h) - f (t + h)) k a b +
          evenMoment (fun t => discrepancy t - f t) k a b) := by
  apply increment_evenMoment_le discrepancy (fun t => f (t + h) - f t)
    (fun t => discrepancy t - f t) h a b hab k hk
  · exact discrepancy_increment_pow_intervalIntegrable h a b (2 * k)
  · exact (((hf.comp (continuous_id.add continuous_const)).sub hf).norm.pow _).intervalIntegrable
      a b
  · exact discrepancy_sub_continuous_shift_pow_intervalIntegrable f hf h a b (2 * k)
  · simpa only [add_zero] using
      discrepancy_sub_continuous_shift_pow_intervalIntegrable f hf 0 a b (2 * k)
  · intro t _
    ring


/-- Estimate only after the exact contour identity: retain both horizontal endpoints. -/
theorem discrepancy_sub_abs_le_contour {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hga : RvM.GoodHeight a) (hgb : RvM.GoodHeight b) :
    |discrepancy b - discrepancy a| ≤
      (1 / Real.pi) *
        (|(∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta (σ + a * Complex.I)).im| +
          Real.pi +
          |(∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta (σ + b * Complex.I)).im|) := by
  rw [discrepancy_sub_eq_zeta_halfContour ha hab hga hgb, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hv : |((∫ t in a..b, logDeriv riemannZeta (2 + t * Complex.I)) *
      Complex.I).im| ≤ Real.pi := by
    rw [← intervalIntegral.integral_mul_const]
    exact RvM.vertical_two a b
  simp only [RvM.halfContour, Complex.sub_im, Complex.add_im]
  have htri (x y z : ℝ) : |x + y - z| ≤ |x| + |y| + |z| := by
    have h1 : |x + y - z| ≤ |x + y| + |z| := abs_sub (x + y) z
    have h2 : |x + y| ≤ |x| + |y| := abs_add_le x y
    linarith only [h1, h2]
  exact (htri _ _ _).trans (by linarith only [hv])

/-- Existing Backlund bounds provide logarithmic control of good-endpoint increments. -/
theorem discrepancy_sub_log_bound :
    ∃ C T₀ : ℝ, ∀ a b : ℝ, 1 ≤ a → a < b → T₀ ≤ a → T₀ ≤ b →
      RvM.GoodHeight a → RvM.GoodHeight b →
      |discrepancy b - discrepancy a| ≤
        (1 / Real.pi) * (C * Real.log a + Real.pi + C * Real.log b) := by
  obtain ⟨C, T₀, hbound⟩ := RvM.backlund_horizontal
  refine ⟨C, T₀, ?_⟩
  intro a b ha hab hTa hTb hga hgb
  exact (discrepancy_sub_abs_le_contour ha hab hga hgb).trans
    (mul_le_mul_of_nonneg_left
      (by linarith only [hbound a hTa hga, hbound b hTb hgb]) (by positivity))

/-- Backlund's good-height bound extends to the right-continuous discrepancy
at every nonnegative height. The transfer across a unit interval uses its
actual zero count and the exact smooth gamma integral. -/
theorem exists_abs_discrepancy_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |discrepancy t| ≤ C * (1 + Real.log (t + 4)) := by
  obtain ⟨c, t₀, hbk⟩ := discrepancy_sub_log_bound
  obtain ⟨A, hA, hgoodA⟩ := RvM.exists_goodHeight (max 1 t₀)
  have hA1 := (le_max_left (1 : ℝ) t₀).trans hA.1
  have hAt := (le_max_right (1 : ℝ) t₀).trans hA.1
  obtain ⟨v, _, hv⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) A).Nonempty from ⟨0, le_rfl, by linarith⟩)
    smoothCount_continuous.abs.continuousOn
  obtain ⟨m, hm, hmu⟩ := RvM.mu_le_log gammaFacts
  obtain ⟨n, hn, hcount⟩ := RvM.zeta_local_zero_count
  let C : ℝ := (Ncount 0 A : ℝ) + |smoothCount v| + |discrepancy A| +
    Real.pi + 2 * |c| + m + n + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith only [Nat.cast_nonneg (α := ℝ) (Ncount 0 A), abs_nonneg (smoothCount v),
      abs_nonneg (discrepancy A), Real.pi_pos, abs_nonneg c, hm, hn]
  refine ⟨C, hC, ?_⟩
  intro t ht
  let L := Real.log (t + 4)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  by_cases htA : t ≤ A
  · have hs : |smoothCount t| ≤ |smoothCount v| := isMaxOn_iff.mp hv t ⟨ht, htA⟩
    have hN : (Ncount 0 t : ℝ) ≤ (Ncount 0 A : ℝ) := count_monotone htA
    have hd : |discrepancy t| ≤ (Ncount 0 A : ℝ) + |smoothCount v| := by
      unfold discrepancy
      have H := abs_sub (Ncount 0 t : ℝ) (smoothCount t)
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Ncount 0 t))] at H
      linarith only [H, hs, hN]
    have hk : (Ncount 0 A : ℝ) + |smoothCount v| ≤ C := by
      dsimp [C]
      linarith only [abs_nonneg (discrepancy A), Real.pi_pos, abs_nonneg c, hm, hn]
    exact (hd.trans hk).trans (by change C ≤ C * (1 + L); nlinarith only [mul_nonneg hC.le hL])
  · have hAt' := lt_of_not_ge htA
    obtain ⟨u, hu, hgu⟩ := RvM.exists_goodHeight t
    have hAu := hAt'.trans_le hu.1
    have hUb := hbk A u hA1 hAu hAt (hAt.trans hAu.le) hgoodA hgu
    have hlg (x : ℝ) (hx : 1 ≤ x) (hxt : x ≤ t + 4) : c * Real.log x ≤ |c| * L :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg hx)).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hxt) (abs_nonneg _))
    have hAlog := hlg A hA1 (by linarith)
    have hulog := hlg u (hA1.trans hAu.le) (by linarith [hu.2])
    have hBr : |discrepancy u - discrepancy A| ≤ Real.pi + 2 * |c| * L := by
      refine hUb.trans ((mul_le_mul_of_nonneg_left
        (show c * Real.log A + Real.pi + c * Real.log u ≤ Real.pi + 2 * |c| * L
          by linarith only [hAlog, hulog]) (by positivity)).trans ?_)
      have hπ : (1 : ℝ) / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hπ
        (show 0 ≤ Real.pi + 2 * |c| * L by positivity)
    have hloc : (Ncount t u : ℝ) ≤ n * L := by
      have hN : (Ncount t u : ℝ) ≤ (Ncount t (t + 1) : ℝ) := by
        exact_mod_cast Ncount_mono (a := t) (b := u) (c := t) (d := t+1) le_rfl hu.2
      have hn' := hcount t
      rw [abs_of_nonneg ht] at hn'
      exact hN.trans (hn'.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith) (by linarith)) (by linarith)))
    have hμpoint (x : ℝ) (hx : x ∈ uIoc t u) : ‖mu x‖ ≤ m * L := by
      rw [uIoc_of_le hu.1] at hx
      rw [Real.norm_eq_abs]
      exact (hmu x (by linarith [hx.1])).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith [hx.1]) (by linarith [hx.2, hu.2])) hm.le)
    have hμbound := intervalIntegral.norm_integral_le_of_norm_le_const hμpoint
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu.1)] at hμbound
    have hμabs : |∫ x in t..u, mu x| ≤ m * L := by
      exact hμbound.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (show u-t ≤ 1 by linarith [hu.2]) (mul_nonneg hm.le hL))
    have hdtu : |discrepancy u - discrepancy t| ≤ (n+m) * L := by
      rw [discrepancy_sub ht hu.1]
      have H := abs_sub (Ncount t u : ℝ) (∫ x in t..u, mu x)
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Ncount t u))] at H
      linarith only [H, hloc, hμabs]
    have hthree : |discrepancy t| ≤ |discrepancy A| +
        |discrepancy u - discrepancy A| + |discrepancy u - discrepancy t| := by
      calc
        _ = |(discrepancy A + (discrepancy u - discrepancy A)) -
            (discrepancy u - discrepancy t)| := by ring_nf
        _ ≤ |discrepancy A + (discrepancy u - discrepancy A)| +
              |discrepancy u - discrepancy t| := abs_sub _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    have hinter : |discrepancy A| + Real.pi ≤ C := by
      dsimp [C]
      linarith only [Nat.cast_nonneg (α := ℝ) (Ncount 0 A), abs_nonneg (smoothCount v),
        abs_nonneg c, hm, hn]
    have hslope : 2 * |c| + n + m ≤ C := by
      dsimp [C]
      linarith only [Nat.cast_nonneg (α := ℝ) (Ncount 0 A), abs_nonneg (smoothCount v),
        abs_nonneg (discrepancy A), Real.pi_pos]
    change |discrepancy t| ≤ C * (1 + L)
    linarith only [hthree, hBr, hdtu, hinter, mul_le_mul_of_nonneg_right hslope hL]

theorem increment_evenMoment_le_of_continuous_budgets
    (f : ℝ → ℝ) (hf : Continuous f) (h a b T U V : ℝ) (hab : a ≤ b)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (k : ℕ) (hk : 1 ≤ k)
    (hpoly : evenMoment (fun t => f (t + h) - f t) k a b ≤ T * U ^ k)
    (hshift : evenMoment (fun t => discrepancy (t + h) - f (t + h)) k a b ≤ T * V ^ k)
    (hrem : evenMoment (fun t => discrepancy t - f t) k a b ≤ T * V ^ k) :
    evenMoment (fun t => discrepancy (t + h) - discrepancy t) k a b ≤
      T * (9 * (U + V)) ^ k := by
  apply increment_evenMoment_le_of_budgets discrepancy (fun t => f (t + h) - f t)
    (fun t => discrepancy t - f t) h a b T U V hab hT hU hV k hk
  · exact discrepancy_increment_pow_intervalIntegrable h a b (2 * k)
  · exact (((hf.comp (continuous_id.add continuous_const)).sub hf).norm.pow _).intervalIntegrable
      a b
  · exact discrepancy_sub_continuous_shift_pow_intervalIntegrable f hf h a b (2 * k)
  · simpa only [add_zero] using
      discrepancy_sub_continuous_shift_pow_intervalIntegrable f hf 0 a b (2 * k)
  · intro t _
    ring
  · exact hpoly
  · exact hshift
  · exact hrem


/-- Direct moment identity for the actual centered window count. -/
theorem centered_window_evenMoment_eq (h a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hh : 0 ≤ h) (k : ℕ) :
    evenMoment (fun t => (Ncount t (t + h) : ℝ) - ∫ u in t..t + h, mu u) k a b =
      evenMoment (fun t => discrepancy (t + h) - discrepancy t) k a b := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  dsimp only
  rw [discrepancy_increment (ha.trans ht.1) hh]

/-- On positive intervals, changing values at zero heights and adding a fixed
normalization constant leaves every increment moment unchanged. -/
theorem evenMoment_eq_of_eqOn_positive_goodHeights (S : ℝ → ℝ) (c : ℝ)
    (hS : ∀ t, 1 ≤ t → RvM.GoodHeight t → S t = discrepancy t + c)
    (h a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hh : 0 ≤ h) (k : ℕ) :
    evenMoment (fun t => S (t + h) - S t) k a b =
      evenMoment (fun t => discrepancy (t + h) - discrepancy t) k a b := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_goodHeight, ae_goodHeight_shift h] with t ht hth
  intro htab
  rw [Set.uIoc_of_le hab] at htab
  have ht1 : 1 ≤ t := ha.trans htab.1.le
  rw [hS t ht1 ht, hS (t + h) (by linarith) hth]
  congr 2
  ring

end RiemannResearch.Analysis.ActualZeroDiscrepancy
