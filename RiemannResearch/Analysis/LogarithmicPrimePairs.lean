import RiemannResearch.RH.PrimePairSingularSeriesMean
import RiemannResearch.Analysis.OddGapPrimeCorrelation
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual prime pairs at logarithmic additive shifts

The sharp sum uses the real parameter X, the half-open macroscopic interval
(AX,BX], positive integer shifts up to floor(d log X), and all prime powers.
It is equivalent to cancellation of the signed, even-shift Hardy–Littlewood
error. A uniform relative even-shift estimate suffices for that cancellation.

Gallagher, *On the distribution of primes in short intervals* (1976),
https://doi.org/10.1112/S0025579300016442, gives the conditional Poisson
context. Matomäki–Radziwiłł–Tao, *Correlations of the von Mangoldt and higher
divisor functions I*, Theorem 1.3, https://arxiv.org/abs/1707.01315,
proves an averaged result in a power-size shift range. The logarithmic
even-shift input below is an explicit mathematical hypothesis.
-/

noncomputable section
open Filter Finset
open scoped Topology BigOperators ArithmeticFunction

namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.Analysis.ShortIntervalBoundary
open RiemannResearch.Analysis.OddGapPrimeCorrelation

/-- Positive integral shifts allowed by the real cutoff. -/
def shiftWidth (d X : ℝ) : ℕ := ⌊d * Real.log X⌋₊

/-- A single positive-shift correlation, with no upper cutoff on the second factor. -/
def pairBlock (A B X : ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ Ioc ⌊A * X⌋₊ ⌊B * X⌋₊, Λ n * Λ (n + h)

/-- The sharp von Mangoldt statistic. The diagonal h = 0 is excluded. -/
def sharpPairAverage (A B d X : ℝ) : ℝ :=
  (∑ n ∈ Ioc ⌊A * X⌋₊ ⌊B * X⌋₊,
    ∑ h ∈ Ioc 0 (shiftWidth d X), Λ n * Λ (n + h)) / (X * Real.log X)

def evenResidual (A B d X : ℝ) : ℝ :=
  ∑ h ∈ Ioc 0 (shiftWidth d X), if h % 2 = 0 then
    pairBlock A B X h - (B - A) * X * singularSeries h else 0

def oddMass (A B d X : ℝ) : ℝ :=
  ∑ h ∈ Ioc 0 (shiftWidth d X), if h % 2 = 0 then 0 else pairBlock A B X h

/-- Exact finite decomposition, including both signed even error and odd prime powers. -/
theorem pair_total_exact (A B d X : ℝ) :
    (∑ n ∈ Ioc ⌊A * X⌋₊ ⌊B * X⌋₊,
      ∑ h ∈ Ioc 0 (shiftWidth d X), Λ n * Λ (n + h)) =
      (B - A) * X * (∑ h ∈ Ioc 0 (shiftWidth d X), singularSeries h) +
        evenResidual A B d X + oddMass A B d X := by
  rw [sum_comm]
  unfold evenResidual oddMass
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro h _
  change pairBlock A B X h = _
  by_cases he : h % 2 = 0
  · rw [if_pos he, if_pos he]
    ring
  · have ho : h % 2 = 1 := by omega
    simp [he, singularSeries_eq_zero_of_odd_gap h ho]

private theorem width_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (shiftWidth d) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [(Real.tendsto_log_atTop.const_mul_atTop hd).eventually_ge_atTop (n : ℝ)]
    with X hX
  exact Nat.le_floor hX

theorem tendsto_width_div_log {d : ℝ} (hd : 0 < d) :
    Tendsto (fun X => (shiftWidth d X : ℝ) / Real.log X) atTop (𝓝 d) := by
  have hl := (tendsto_const_nhds (x := d)).sub
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
      Tendsto (fun X : ℝ => 1 / Real.log X) atTop (𝓝 0))
  rw [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hx := Real.log_pos hX
    apply (le_div_iff₀ hx).mpr
    rw [sub_mul, div_mul_cancel₀ _ hx.ne']
    have h := Nat.lt_floor_add_one (d * Real.log X)
    change d * Real.log X - 1 ≤ (↑⌊d * Real.log X⌋₊ : ℝ)
    linarith
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hx := Real.log_pos hX
    exact (div_le_iff₀ hx).mpr (Nat.floor_le (mul_nonneg hd.le hx.le))

/-- Unconditional main term on the precise logarithmic scale. -/
theorem tendsto_log_singularSeries {d : ℝ} (hd : 0 < d) :
    Tendsto (fun X => (∑ h ∈ Ioc 0 (shiftWidth d X), singularSeries h) / Real.log X)
      atTop (𝓝 d) := by
  have ht := (tendsto_singularSeries_mean.comp (width_atTop hd)).mul (tendsto_width_div_log hd)
  rw [one_mul] at ht
  apply ht.congr'
  filter_upwards [(width_atTop hd).eventually_ge_atTop 1] with X hX
  have h : (shiftWidth d X : ℝ) ≠ 0 := by exact_mod_cast (show shiftWidth d X ≠ 0 by omega)
  dsimp [Function.comp_def]
  field_simp

theorem pairBlock_nonneg (A B X : ℝ) (h : ℕ) : 0 ≤ pairBlock A B X h :=
  sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

private theorem block_le_raw (A B X : ℝ) (h : ℕ) :
    pairBlock A B X h ≤ rawGapCorrelation ⌊B * X⌋₊ h := by
  let b := ⌊B * X⌋₊
  let f := fun n : ℕ => Λ n * Λ (n + h)
  change (∑ n ∈ Ioc ⌊A * X⌋₊ b, f n) ≤ ∑ n ∈ range b, f (n + 2)
  calc
    _ ≤ ∑ n ∈ range (2 + b), f n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have := (mem_Ioc.mp hn).2
        exact mem_range.mpr (by omega)
      · intro n _ _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by
      rw [sum_range_add]
      have hz : (∑ n ∈ range 2, f n) = 0 := by simp [sum_range_succ, f]
      rw [hz, zero_add]
      apply sum_congr rfl
      intro j _
      rw [Nat.add_comm 2 j]

/-- The whole odd contribution vanishes even though powers of two carry nonzero mass. -/
theorem tendsto_oddMass_div (A : ℝ) {B d : ℝ} (hB : 0 < B) (hd : 0 < d) :
    Tendsto (fun X => oddMass A B d X / (X * Real.log X)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℝ => (Real.log X)^2 / X) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_pow_atTop (1 : ℝ) 2 (by norm_num))
  have hlim := hlog.const_mul (8 * d)
  rw [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hsum : 0 ≤ oddMass A B d X := by
      apply sum_nonneg
      intro h _
      split_ifs
      · exact le_rfl
      · exact pairBlock_nonneg A B X h
    exact div_nonneg hsum (mul_nonneg (by linarith) (Real.log_pos hX).le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (B + d + 2)] with X hX hbig
    have hx : 0 < X := by linarith
    have hl := Real.log_pos hX
    have hwidth : (shiftWidth d X : ℝ) ≤ d * Real.log X :=
      Nat.floor_le (mul_nonneg hd.le hl.le)
    have hc (h : ℕ) (hh : h ≤ shiftWidth d X) (ho : h % 2 = 1) :
        pairBlock A B X h ≤ 8 * (Real.log X)^2 := by
      let L := ⌊B * X⌋₊ + h + 2
      have hL : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by dsimp [L]; omega)
      have hcast : (h : ℝ) ≤ shiftWidth d X := by exact_mod_cast hh
      have hfloor : (↑⌊B * X⌋₊ : ℝ) ≤ B * X := Nat.floor_le (mul_nonneg hB.le hx.le)
      have hlx : Real.log X ≤ X := by linarith [Real.log_le_sub_one_of_pos hx]
      have hLs : (L : ℝ) ≤ X^2 := by
        dsimp [L]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hbig hx.le, mul_le_mul_of_nonneg_left hlx hd.le]
      have hLl : Real.log (L : ℝ) ≤ 2 * Real.log X := by
        simpa only [Real.log_pow, Nat.cast_ofNat] using
          Real.log_le_log (by linarith : (0 : ℝ) < L) hLs
      have hLn := Real.log_nonneg hL
      have hs := sq_le_sq' (by linarith : -(2 * Real.log X) ≤ Real.log (L : ℝ)) hLl
      have ho' := (block_le_raw A B X h).trans (odd_raw_le_log_sq ⌊B * X⌋₊ h ho)
      change pairBlock A B X h ≤ 2 * (Real.log (L : ℝ))^2 at ho'
      nlinarith
    have hs : oddMass A B d X ≤ (shiftWidth d X : ℝ) * (8 * (Real.log X)^2) := by
      unfold oddMass
      calc
        _ ≤ ∑ _h ∈ Ioc 0 (shiftWidth d X), 8 * (Real.log X)^2 := by
          apply sum_le_sum
          intro h hh
          split_ifs with he
          · positivity
          · exact hc h (mem_Ioc.mp hh).2 (by omega)
        _ = _ := by simp
    calc
      _ ≤ (d * Real.log X * (8 * (Real.log X)^2)) / (X * Real.log X) :=
        div_le_div_of_nonneg_right (hs.trans (mul_le_mul_of_nonneg_right hwidth (by positivity)))
          (mul_nonneg hx.le hl.le)
      _ = _ := by field_simp

private theorem normalized_exact (A B d X : ℝ) (hX : 1 < X) :
    sharpPairAverage A B d X =
      (B - A) * ((∑ h ∈ Ioc 0 (shiftWidth d X), singularSeries h) / Real.log X) +
      evenResidual A B d X / (X * Real.log X) + oddMass A B d X / (X * Real.log X) := by
  have hx : X ≠ 0 := by linarith
  have hl := (Real.log_pos hX).ne'
  rw [sharpPairAverage, pair_total_exact]
  field_simp

/-- Exactly the signed even-shift residual is left at the stated normalization. -/
theorem sharpPairAverage_iff_evenResidual {A B d : ℝ} (hA : 0 < A) (hAB : A < B) (hd : 0 < d) :
    Tendsto (sharpPairAverage A B d) atTop (𝓝 ((B - A) * d)) ↔
    Tendsto (fun X => evenResidual A B d X / (X * Real.log X)) atTop (𝓝 0) := by
  have hm := (tendsto_log_singularSeries hd).const_mul (B - A)
  have ho := tendsto_oddMass_div A (hA.trans hAB) hd
  constructor
  · intro ht
    have hr := (ht.sub hm).sub ho
    rw [sub_self, sub_zero] at hr
    apply hr.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [normalized_exact A B d X hX]
    ring
  · intro hr
    have ht := (hm.add hr).add ho
    rw [add_zero, add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (normalized_exact A B d X hX).symm

/-- A relative uniform Hardy–Littlewood error on even shifts suffices.
The error function and its moving range appear in the hypotheses. -/
theorem sharpPairAverage_of_uniform_even {A B d : ℝ} (hA : 0 < A) (hAB : A < B)
    (hd : 0 < d) (err : ℝ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hHL : ∀ᶠ X : ℝ in atTop, ∀ h ∈ Ioc 0 (shiftWidth d X), h % 2 = 0 →
      |pairBlock A B X h - (B - A) * X * singularSeries h| ≤
        |err X| * X * singularSeries h) :
    Tendsto (sharpPairAverage A B d) atTop (𝓝 ((B - A) * d)) := by
  apply (sharpPairAverage_iff_evenResidual hA hAB hd).2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hl := herr.abs.mul (tendsto_log_singularSeries hd)
  simp only [abs_zero, zero_mul] at hl
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hl
  filter_upwards [hHL, eventually_gt_atTop (1 : ℝ)] with X he hX
  have hx : 0 < X := by linarith
  have hlog := Real.log_pos hX
  have hsum : |evenResidual A B d X| ≤
      |err X| * X * ∑ h ∈ Ioc 0 (shiftWidth d X), singularSeries h := by
    unfold evenResidual
    rw [mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro h hh
    by_cases ho : h % 2 = 0
    · simpa only [if_pos ho] using he h hh ho
    · rw [if_neg ho, abs_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hx.le) (singularSeries_nonneg h)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hx hlog)]
  calc
    _ ≤ (|err X| * X * ∑ h ∈ Ioc 0 (shiftWidth d X), singularSeries h) /
        (X * Real.log X) := div_le_div_of_nonneg_right hsum (mul_pos hx hlog).le
    _ = _ := by field_simp

end RiemannResearch.Analysis.LogarithmicPrimePairs
