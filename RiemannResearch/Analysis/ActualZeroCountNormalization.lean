/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ActualZeroCountUpper
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact leading normalization of the actual zero count

The existing actual Riemann--von Mangoldt provider gives the sharp dyadic
main term. Finite dyadic accumulation of an arbitrary coarse upper bound
gives every upper coefficient greater than `1 / (2*pi)`. Combined with the
existing sharp lower coefficients, this proves
`Ncount 0 T / (T * log T / (2*pi)) → 1` without RH or a density hypothesis.
All nontrivial zeros retain their analytic multiplicity.

Source for the classical normalization statement: Carneiro--Milinovich--Ramos,
*Fourier optimization and Montgomery's pair correlation conjecture*,
arXiv:2310.01913v2, Section 1.1, https://arxiv.org/abs/2310.01913.
The proof here uses the repository's checked dyadic Riemann--von Mangoldt
theorem and elementary geometric accumulation, not the pair correlation
conjecture. This normalization aligns the `N(T)` denominator used there with
the `T log T / (2*pi)` denominator of `MontgomeryFormFactor.formFactor`.
-/

open Filter Zeta23
open scoped Topology

namespace Zeta23.Assembly

/-- Every coefficient above the dyadic Riemann--von Mangoldt leading
coefficient is an eventual upper bound. -/
theorem eventually_N_le_log_of_lt (Z : ZeroConfig) (hR : RiemannVonMangoldt Z)
    {q : ℝ} (hq : 1 / (2 * Real.pi) < q) :
    ∀ᶠ T : ℝ in atTop,
      (Z.N T (2 * T) : ℝ) ≤ q * T * Real.log T := by
  let b : ℝ := 1 / (2 * Real.pi)
  let u : ℝ := -Real.log (2 * Real.pi) + 2 * Real.log 2 - 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hk : 0 < q - b := by dsimp [b]; linarith
  obtain ⟨C, T₀, hmain⟩ := hR.main
  filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * b * |u| / (q - b)),
    eventually_ge_atTop (2 * |C| / (q - b))]
    with T hT₀ hT hT1 hLu hTC
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hell : ell1 T = Real.log T + u := by
    rw [ell1_eq]
    have he := log_eq_l_add hT
    dsimp [u, c₀]
    linarith
  have hformula : T / (2 * Real.pi) * ell1 T =
      b * T * (Real.log T + u) := by rw [hell]; dsimp [b]; ring
  have hupp := (abs_le.mp (hmain T hT₀)).2
  rw [hformula] at hupp
  have hu := mul_le_mul_of_nonneg_left (le_abs_self u) (mul_nonneg hb.le hT.le)
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hu₀ : b * |u| ≤ ((q - b) / 2) * Real.log T := by
    have h := (div_le_iff₀ hk).mp hLu
    nlinarith
  have hC₀ : |C| ≤ ((q - b) / 2) * T := by
    have h := (div_le_iff₀ hk).mp hTC
    nlinarith
  have huT := mul_le_mul_of_nonneg_left hu₀ hT.le
  have hCT := mul_le_mul_of_nonneg_right hC₀ hlog
  nlinarith

end Zeta23.Assembly

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Finite dyadic accumulation contracts an arbitrary upper coefficient
towards any coefficient above the sharp one. -/
theorem eventually_count_le_log_geometric {q A : ℝ}
    (hq : 1 / (2 * Real.pi) < q) (hAq : q ≤ A)
    (hA : ∀ᶠ T : ℝ in atTop, (Ncount 0 T : ℝ) ≤ A * T * Real.log T) (n : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      (Ncount 0 T : ℝ) ≤ (q + (A - q) * (1 / 2 : ℝ) ^ n) * T * Real.log T := by
  have hq₀ : 0 < q := lt_trans (by positivity) hq
  have hd := Assembly.eventually_N_le_log_of_lt zetaZeroConfig
    (RvM.riemannVonMangoldt gammaFacts) hq
  have hh : ∀ᶠ T : ℝ in atTop,
      (Ncount (T / 2) T : ℝ) ≤ q * (T / 2) * Real.log (T / 2) := by
    have hc := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually hd
    filter_upwards [hc] with T hT
    simpa only [id_eq, zetaZeroConfig_N, show 2 * (T / 2) = T by ring] using hT
  induction n with
  | zero => simpa using hA
  | succ n ih =>
    have hi := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually ih
    filter_upwards [hi, hh, eventually_gt_atTop (0 : ℝ)] with T hI hD hT
    have hadd : (Ncount 0 T : ℝ) =
        (Ncount 0 (T / 2) : ℝ) + (Ncount (T / 2) T : ℝ) := by
      exact_mod_cast Ncount_add (a := 0) (b := T / 2) (c := T)
        (by linarith) (by linarith)
    have hlog : Real.log (T / 2) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by linarith)
    have hcoeff : 0 ≤ q + (A - q) * (1 / 2 : ℝ) ^ (n + 1) := by positivity
    calc
      _ ≤ (q + (A - q) * (1 / 2 : ℝ) ^ n) * (T / 2) * Real.log (T / 2) +
          q * (T / 2) * Real.log (T / 2) := by rw [hadd]; exact add_le_add hI hD
      _ = (q + (A - q) * (1 / 2 : ℝ) ^ (n + 1)) * T * Real.log (T / 2) := by
        rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (mul_nonneg hcoeff hT.le)

/-- Every coefficient strictly above the sharp leading coefficient bounds
the actual zero count eventually. -/
theorem eventually_count_le_log_of_lt {c : ℝ} (hc : 1 / (2 * Real.pi) < c) :
    ∀ᶠ T : ℝ in atTop, (Ncount 0 T : ℝ) ≤ c * T * Real.log T := by
  let b : ℝ := 1 / (2 * Real.pi)
  let q : ℝ := (b + c) / 2
  have hbq : b < q := by dsimp [q, b]; linarith
  have hqc : q < c := by dsimp [q, b]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_count_le_height_log
  let A : ℝ := max C q
  have hA : ∀ᶠ T : ℝ in atTop, (Ncount 0 T : ℝ) ≤ A * T * Real.log T := by
    filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
    have hT₀ : 0 ≤ T := by linarith
    have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C q) hT₀) hlog)
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ha : Tendsto (fun n : ℕ => q + (A - q) * (1 / 2 : ℝ) ^ n) atTop (𝓝 q) := by
    simpa using tendsto_const_nhds.add (hp.const_mul (A - q))
  obtain ⟨n, hn⟩ := (ha.eventually (gt_mem_nhds hqc)).exists
  filter_upwards [eventually_count_le_log_geometric hbq (le_max_right C q) hA n,
    eventually_gt_atTop (1 : ℝ)] with T hN hT
  have hT₀ : 0 ≤ T := by linarith
  exact hN.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hn.le hT₀) (Real.log_nonneg hT.le))

/-- The actual multiplicity-weighted zero count has its exact leading
normalization, unconditionally. -/
theorem tendsto_count_div_mainTerm :
    Tendsto (fun T : ℝ => (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let q : ℝ := (a + 1) / 2
    have haq : a < q := by dsimp [q]; linarith
    have hq : q < 1 := by dsimp [q]; linarith
    have hc : q / (2 * Real.pi) < 1 / (2 * Real.pi) :=
      div_lt_div_of_pos_right hq (by positivity)
    filter_upwards [eventually_count_ge_log_of_lt hc, eventually_gt_atTop (1 : ℝ)]
      with T hN hT
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hD : 0 < T * Real.log T / (2 * Real.pi) := by positivity
    apply (lt_div_iff₀ hD).2
    calc
      _ < q * (T * Real.log T / (2 * Real.pi)) := mul_lt_mul_of_pos_right haq hD
      _ = q / (2 * Real.pi) * T * Real.log T := by ring
      _ ≤ _ := hN
  · intro b hb
    let q : ℝ := (1 + b) / 2
    have hqb : q < b := by dsimp [q]; linarith
    have hq : 1 < q := by dsimp [q]; linarith
    have hc : 1 / (2 * Real.pi) < q / (2 * Real.pi) :=
      div_lt_div_of_pos_right hq (by positivity)
    filter_upwards [eventually_count_le_log_of_lt hc, eventually_gt_atTop (1 : ℝ)]
      with T hN hT
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hD : 0 < T * Real.log T / (2 * Real.pi) := by positivity
    apply (div_lt_iff₀ hD).2
    calc
      _ ≤ q / (2 * Real.pi) * T * Real.log T := hN
      _ = q * (T * Real.log T / (2 * Real.pi)) := by ring
      _ < _ := mul_lt_mul_of_pos_right hqb hD

end RiemannResearch.Analysis.ActualZeroOrdinate
