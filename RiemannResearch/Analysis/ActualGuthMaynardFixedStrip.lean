/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodDensity
import RiemannResearch.Analysis.ActualSelbergDensityAssembly

/-!
# Guth–Maynard and Ingham on fixed vertical strips

Guth and Maynard, *New large value estimates for Dirichlet polynomials*,
Ann. of Math. 203 (2026), Theorem 1.2, https://doi.org/10.4007/annals.2026.203.2.6,
bound the inclusive count up to absolute height by a power with exponent
`15 (1 - σ) / (3 + 5 σ) + o(1)`. Its positive-ordinate consequence is an
explicit external hypothesis here. Constants and height thresholds may depend
on the fixed abscissa and on the positive power allowance.

The repository supplies the Ingham bound with logarithmic exponent `2 + q`.
The combined minimum retains that entire term. For fixed abscissae from
one half to 19/25 the better of the two height exponents agrees with the
first two entries of Tao–Trudgian–Yang, ANTEDB, Table 11.1. At and beyond
19/25 further fixed-strip estimates are available.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Height exponent in Theorem 1.2 of Guth–Maynard. -/
def guthMaynardExponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

/-- Positive-ordinate version of the published theorem. Every abscissa
and allowance are fixed before the constant and the height threshold. -/
def GuthMaynardDensityHypothesis : Prop :=
  ∀ σ ∈ Icc (1 / 2 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ T : ℝ in atTop, rightInclusiveCount T σ ≤ C * T ^ (guthMaynardExponent σ + ε)

/-- Exact signed gain in the height exponent. -/
theorem ingham_sub_guthMaynard {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    3 * (1 - σ) / (2 - σ) - guthMaynardExponent σ =
      3 * (1 - σ) * (10 * σ - 7) / ((2 - σ) * (3 + 5 * σ)) := by
  have h₁ : 2 - σ ≠ 0 := ne_of_gt (by linarith only [hσ.2])
  have h₂ : 3 + 5 * σ ≠ 0 := ne_of_gt (by linarith only [hσ.1])
  have h₂' : 3 + σ * 5 ≠ 0 := by simpa only [mul_comm] using h₂
  unfold guthMaynardExponent
  field_simp [h₁, h₂, h₂']
  ring

/-- At fixed abscissae strictly below one the exact crossover in the two
height exponents is 7/10. Each positive epsilon still costs that amount on
the Guth–Maynard side. -/
theorem guthMaynard_le_ingham_iff {σ : ℝ} (hσ : 1 / 2 ≤ σ) (h₁ : σ < 1) :
    guthMaynardExponent σ ≤ 3 * (1 - σ) / (2 - σ) ↔ 7 / 10 ≤ σ := by
  rw [← sub_nonneg, ingham_sub_guthMaynard ⟨hσ, h₁.le⟩]
  have hd : 0 < (2 - σ) * (3 + 5 * σ) := mul_pos (by linarith) (by linarith)
  have hn : 0 < 3 * (1 - σ) := by linarith
  rw [le_div_iff₀ hd, zero_mul, mul_nonneg_iff_of_pos_left hn]
  constructor <;> intro h <;> linarith

/-- At 3/4 the decrease of 2/45 leaves room for every power allowance
strictly below 2/45. -/
theorem guthMaynard_gain_three_quarters :
    guthMaynardExponent (3 / 4) = 5 / 9 ∧
      3 * (1 - (3 / 4 : ℝ)) / (2 - 3 / 4) - guthMaynardExponent (3 / 4) = 2 / 45 := by
  norm_num [guthMaynardExponent]

/-- The pointwise minimum of both complete majorants for an actual count.
The Ingham constant is uniform and the Guth–Maynard constant is local to
the chosen abscissa and allowance. -/
theorem exists_ingham_guthMaynard_count (hG : GuthMaynardDensityHypothesis) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ ∈ Icc (1 / 2 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
        let q := 3 * (1 - σ) / (2 - σ)
        rightInclusiveCount T σ ≤ min
          (B * min (T * Real.log T) (T ^ q * (Real.log T) ^ (2 + q)))
          (C * T ^ (guthMaynardExponent σ + ε)) := by
  obtain ⟨B, hB, hi⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨B, hB, ?_⟩
  intro σ hσ ε hε
  obtain ⟨C, hC, hg⟩ := hG σ hσ ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hg] with T hT hG'
  exact le_min (hi T hT σ hσ) hG'

/-- Reflection and the proved total-count lower bound turn the published
one-sided count into a bound for the fraction of actual copies on either
side of a fixed strip. The normalization retains the extra logarithm. -/
theorem normalized_strictTail_of_guthMaynard (hG : GuthMaynardDensityHypothesis)
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) (1 / 2)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      strictTail T δ / (Ncount 0 T : ℝ) ≤
        C * T ^ (guthMaynardExponent (1 / 2 + δ) + ε - 1) / Real.log T := by
  have hσ : 1 / 2 + δ ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith only [hδ.1], by linarith only [hδ.2]⟩
  obtain ⟨C, hC, hg⟩ := hG _ hσ ε hε
  let c : ℝ := 1 / (16 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2 * C / c, by positivity, ?_⟩
  filter_upwards [eventually_count_ge_log, eventually_ge_atTop (2 : ℝ), hg] with T hN hT hG'
  have hT₀ : 0 < T := by linarith
  have hL := Real.log_pos (show 1 < T by linarith)
  change c * T * Real.log T ≤ (Ncount 0 T : ℝ) at hN
  have hNpos : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  let q := guthMaynardExponent (1 / 2 + δ) + ε
  have ht : strictTail T δ ≤ 2 * (C * T ^ q) := by
    rw [strictTail_eq_twice_right T δ hδ.1]
    exact mul_le_mul_of_nonneg_left ((rightStrictTail_le_inclusive T δ).trans hG') (by norm_num)
  apply (div_le_iff₀ hNpos).mpr
  calc
    _ ≤ 2 * (C * T ^ q) := ht
    _ = (2 * C / c * T ^ (q - 1) / Real.log T) * (c * T * Real.log T) := by
      rw [Real.rpow_sub hT₀, Real.rpow_one]
      field_simp [ne_of_gt hc, ne_of_gt hT₀, ne_of_gt hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

/-- The two-sided exceptional fraction at displacement 1/4 is bounded by
a constant times `T^(−4/9+ε)/log T`. -/
theorem normalized_strictTail_quarter_of_guthMaynard (hG : GuthMaynardDensityHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      strictTail T (1 / 4) / (Ncount 0 T : ℝ) ≤ C * T ^ (-4 / 9 + ε) / Real.log T := by
  have he : guthMaynardExponent (1 / 2 + 1 / 4) + ε - 1 = -4 / 9 + ε := by
    norm_num [guthMaynardExponent]
    ring
  simpa only [he] using normalized_strictTail_of_guthMaynard hG
    (δ := 1 / 4) (by constructor <;> norm_num) hε

/-- The slope of the fixed-strip exponent is bounded in magnitude by four
on the closed half strip. The difference identity keeps the exact denominator. -/
theorem guthMaynardExponent_difference {x y : ℝ} (hx : 1 / 2 ≤ x) (hy : x ≤ y) :
    guthMaynardExponent x - guthMaynardExponent y =
      120 * (y - x) / ((3 + 5 * x) * (3 + 5 * y)) := by
  have h₁ : 3 + 5 * x ≠ 0 := ne_of_gt (by linarith)
  have h₂ : 3 + 5 * y ≠ 0 := ne_of_gt (by linarith)
  have h₁' : 3 + x * 5 ≠ 0 := by simpa only [mul_comm] using h₁
  have h₂' : 3 + y * 5 ≠ 0 := by simpa only [mul_comm] using h₂
  unfold guthMaynardExponent
  field_simp [h₁, h₂, h₁', h₂']
  ring

private theorem guthMaynardExponent_diff_le {x y : ℝ} (hx : 1 / 2 ≤ x) (hy : x ≤ y) :
    guthMaynardExponent x - guthMaynardExponent y ≤ 4 * (y - x) := by
  rw [guthMaynardExponent_difference hx hy]
  have hx' : 11 / 2 ≤ 3 + 5 * x := by linarith
  have hy' : 11 / 2 ≤ 3 + 5 * y := by linarith
  have hd : (11 / 2 : ℝ) * (11 / 2) ≤ (3 + 5 * x) * (3 + 5 * y) :=
    mul_le_mul hx' hy' (by norm_num) (by linarith)
  apply (div_le_iff₀ (show 0 < (3 + 5 * x) * (3 + 5 * y) by linarith only [hd])).mpr
  calc
    120 * (y - x) ≤ (4 * (y - x)) * ((11 / 2) * (11 / 2)) := by linarith only [hy]
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by linarith only [hy])

/-- Despite the order of quantifiers in the literature input, every fixed
positive power allowance gives one constant and one height threshold for
the entire closed half strip. A finite mesh uses half the allowance in
its pointwise estimates and half between adjacent abscissae. -/
theorem uniform_guthMaynard_count (hG : GuthMaynardDensityHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      rightInclusiveCount T σ ≤ C * T ^ (guthMaynardExponent σ + ε) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (8 / ε)
  have hn₀ : 0 < (n : ℝ) := lt_trans (by positivity : 0 < 8 / ε) hn
  have hmesh : 4 / (n : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hn₀).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith only [h]
  let grid (i : Fin (n + 1)) : ℝ := min 1 (1 / 2 + (i.val : ℝ) / n)
  have hgrid (i : Fin (n + 1)) : grid i ∈ Icc (1 / 2 : ℝ) 1 := by
    refine ⟨le_min (by norm_num) ?_, min_le_left _ _⟩
    have hi : 0 ≤ (i.val : ℝ) / n := by positivity
    linarith
  choose D hD hb using fun i : Fin (n + 1) => hG (grid i) (hgrid i) (ε / 2) (by linarith)
  let C := 1 + ∑ i : Fin (n + 1), D i
  have hsum : 0 ≤ ∑ i : Fin (n + 1), D i := Finset.sum_nonneg (fun i _ => (hD i).le)
  refine ⟨C, by dsimp [C]; linarith only [hsum], ?_⟩
  have hs : ∀ᶠ T : ℝ in atTop, ∀ i : Fin (n + 1),
      rightInclusiveCount T (grid i) ≤ D i * T ^ (guthMaynardExponent (grid i) + ε / 2) :=
    Filter.eventually_all.mpr hb
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
  intro σ hσ
  let z := (σ - 1 / 2) * (n : ℝ)
  have hz : 0 ≤ z := mul_nonneg (sub_nonneg.mpr hσ.1) hn₀.le
  have hzn : z ≤ (n : ℝ) := by
    dsimp [z]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hσ.2) hn₀.le, hn₀.le]
  have hk := Nat.floor_le hz
  have hk' := Nat.lt_floor_add_one z
  have hkn : ⌊z⌋₊ ≤ n := by exact_mod_cast hk.trans hzn
  let i : Fin (n + 1) := ⟨⌊z⌋₊, Nat.lt_succ_of_le hkn⟩
  have hx : 1 / 2 + (i.val : ℝ) / n ≤ σ := by
    have hz' : (i.val : ℝ) / n ≤ σ - 1 / 2 := (div_le_iff₀ hn₀).mpr hk
    linarith
  have heq : grid i = 1 / 2 + (i.val : ℝ) / n := min_eq_right (hx.trans hσ.2)
  have hsg : σ - grid i < 1 / n := by
    rw [heq]
    have hz' : σ - 1 / 2 < ((i.val : ℝ) + 1) / n := (lt_div_iff₀ hn₀).mpr hk'
    rw [add_div] at hz'
    linarith
  have hgs : grid i ≤ σ := heq.trans_le hx
  have hp : guthMaynardExponent (grid i) + ε / 2 ≤ guthMaynardExponent σ + ε := by
    have hd := guthMaynardExponent_diff_le (hgrid i).1 hgs
    have hm : 4 * (σ - grid i) < 4 / n := by
      calc
        _ < 4 * (1 / (n : ℝ)) := mul_lt_mul_of_pos_left hsg (by norm_num)
        _ = _ := by ring
    linarith only [hd, hm, hmesh]
  have hDC : D i ≤ C := by
    have hle : D i ≤ ∑ j : Fin (n + 1), D j :=
      Finset.single_le_sum (fun j _ => (hD j).le) (Finset.mem_univ i)
    dsimp [C]; linarith only [hle]
  exact (rightInclusiveCount_antitone T hgs).trans ((hT i).trans
    (mul_le_mul hDC (Real.rpow_le_rpow_of_exponent_le hT₁ hp)
      (Real.rpow_nonneg (by linarith) _) (le_trans (hD i).le hDC)))

/-- The Guth–Maynard exponent plus the displacement weight has its maximum
on the right quarter-strip at its left edge whenever `b ≤ 20/9`. The
straight-line upper bound for the rational exponent is the secant through
the two endpoints. -/
theorem guthMaynard_weighted_quarter_exponent {b σ : ℝ}
    (hb : b ≤ 20 / 9) (hσ : σ ∈ Icc (3 / 4 : ℝ) 1) :
    guthMaynardExponent σ + b * (σ - 1 / 2) ≤ 5 / 9 + b / 4 := by
  have hd : 0 < 3 + 5 * σ := by linarith only [hσ.1]
  have hq : guthMaynardExponent σ ≤ (20 / 9) * (1 - σ) := by
    unfold guthMaynardExponent
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hσ.2) (sub_nonneg.mpr hσ.1)]
  nlinarith only [hq, mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hσ.1)]

/-- Every abscissa on the right quarter-strip, including a height-dependent
one, has the same weighted count budget. For `b < 16/9` an allowance
`0 < ε < 4/9 - b/4` makes the exponent strictly smaller than one. -/
theorem weighted_quarter_count_of_guthMaynard (hG : GuthMaynardDensityHypothesis)
    {b ε : ℝ} (hb : b ≤ 20 / 9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (3 / 4 : ℝ) 1,
      rightInclusiveCount T σ * T ^ (b * (σ - 1 / 2)) ≤
        C * T ^ (5 / 9 + b / 4 + ε) := by
  obtain ⟨C, hC, hc⟩ := uniform_guthMaynard_count hG hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
  intro σ hσ
  have hhalf : σ ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith only [hσ.1], hσ.2⟩
  have hT₀ : 0 < T := by linarith
  calc
    _ ≤ (C * T ^ (guthMaynardExponent σ + ε)) * T ^ (b * (σ - 1 / 2)) :=
      mul_le_mul_of_nonneg_right (hT σ hhalf) (Real.rpow_nonneg hT₀.le _)
    _ = C * T ^ ((guthMaynardExponent σ + ε) + b * (σ - 1 / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hT₀]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT₁
      (by linarith only [guthMaynard_weighted_quarter_exponent hb hσ])) hC.le

/-- The finite layer cake converts a bound on weighted counts throughout
the quarter-strip into a bound on the sum over all exceptional copies.
The boundary count at 1/4 and the interval length 1/4 both contribute. -/
private theorem badExp_quarter_le_of_weighted_tail {T ℓ K : ℝ} (hℓ : 0 ≤ ℓ)
    (htail : ∀ t ∈ Icc (1 / 4 : ℝ) (1 / 2), strictTail T t * Real.exp (ℓ * t) ≤ K) :
    badWeightedSum T (1 / 4) (fun t => Real.exp (ℓ * t)) ≤ K * (1 + ℓ / 4) := by
  have hI : IntervalIntegrable (fun t => strictTail T t * (ℓ * Real.exp (ℓ * t)))
      volume (1 / 4) (1 / 2) :=
    FiniteStrictTail.intervalIntegrable_tail_mul _ _ _ (by fun_prop) _ _
  have hi : (∫ t in (1 / 4 : ℝ)..(1 / 2), strictTail T t * (ℓ * Real.exp (ℓ * t))) ≤
      ∫ _ in (1 / 4 : ℝ)..(1 / 2), ℓ * K := by
    apply intervalIntegral.integral_mono_on (by norm_num) hI intervalIntegrable_const
    intro t ht
    calc
      _ = ℓ * (strictTail T t * Real.exp (ℓ * t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (htail t ht) hℓ
  have hleft := htail (1 / 4) ⟨le_rfl, by norm_num⟩
  rw [badExp_layerCake T (1 / 4) ℓ (by norm_num)]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  nlinarith only [hleft, hi]

/-- The exponentially weighted mass of strictly exceptional copies on both
sides has a power saving for every fixed weight 0 ≤ b < 16/9, after choosing
epsilon smaller than 4/9 - b/4. This use of Guth–Maynard retains the
original analytic multiplicities and the finite lower boundary. -/
theorem badExp_quarter_of_guthMaynard (hG : GuthMaynardDensityHypothesis)
    {b ε : ℝ} (hb₀ : 0 ≤ b) (hb : b ≤ 20 / 9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T (1 / 4) (fun t => Real.exp (b * Real.log T * t)) ≤
        C * T ^ (5 / 9 + b / 4 + ε) * (1 + b * Real.log T / 4) := by
  obtain ⟨C, hC, hg⟩ := weighted_quarter_count_of_guthMaynard hG hb hε
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hg, eventually_ge_atTop (2 : ℝ)] with T hT hT₂
  have hT₀ : 0 < T := by linarith
  apply badExp_quarter_le_of_weighted_tail (mul_nonneg hb₀ (Real.log_nonneg (by linarith)))
  intro t ht
  have hσ : 1 / 2 + t ∈ Icc (3 / 4 : ℝ) 1 := ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have hz := hT _ hσ
  rw [show 1 / 2 + t - 1 / 2 = t by ring, Real.rpow_def_of_pos hT₀ (b * t)] at hz
  have hh := mul_le_mul_of_nonneg_right
    (strictTail_le_twice_inclusive T t (by linarith only [ht.1]))
    (Real.exp_pos (b * Real.log T * t)).le
  calc
    _ ≤ _ := hh
    _ = 2 * (rightInclusiveCount T (1 / 2 + t) * Real.exp (Real.log T * (b * t))) := by
      rw [show b * Real.log T * t = Real.log T * (b * t) by ring]; ring
    _ ≤ _ := by linarith only [hz]

/-- Normalization by the original count absorbs the layer-cake logarithm.
Thus the full weighted exceptional fraction saves the power `4/9 - b/4 - ε`
whenever it is positive. -/
theorem normalized_badExp_quarter_of_guthMaynard (hG : GuthMaynardDensityHypothesis)
    {b ε : ℝ} (hb₀ : 0 ≤ b) (hb : b ≤ 20 / 9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T (1 / 4) (fun t => Real.exp (b * Real.log T * t)) /
        (Ncount 0 T : ℝ) ≤ C * T ^ (-4 / 9 + b / 4 + ε) := by
  obtain ⟨B, hB, hf⟩ := badExp_quarter_of_guthMaynard hG hb₀ hb hε
  let c : ℝ := 1 / (16 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨B * (1 + b / 4) / c, by positivity, ?_⟩
  filter_upwards [hf, eventually_count_ge_log, eventually_ge_atTop (Real.exp 1)] with T hT hN hE
  have hT₀ := (Real.exp_pos _).trans_le hE
  have hL : 1 ≤ Real.log T := by simpa using Real.log_le_log (Real.exp_pos _) hE
  change c * T * Real.log T ≤ (Ncount 0 T : ℝ) at hN
  have hLp : 0 < Real.log T := by linarith
  have hNp : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hpow : T ^ (5 / 9 + b / 4 + ε) = T ^ (-4 / 9 + b / 4 + ε) * T := by
    rw [show (5 / 9 + b / 4 + ε) = (-4 / 9 + b / 4 + ε) + 1 by ring, Real.rpow_add hT₀,
      Real.rpow_one]
  apply (div_le_iff₀ hNp).mpr
  calc
    _ ≤ _ := hT
    _ ≤ B * T ^ (5 / 9 + b / 4 + ε) * ((1 + b / 4) * Real.log T) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hL]) (by positivity)
    _ = (B * (1 + b / 4) / c * T ^ (-4 / 9 + b / 4 + ε)) * (c * T * Real.log T) := by
      rw [hpow]; field_simp [hc.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

end RiemannResearch.Analysis.ActualZeroOrdinate
