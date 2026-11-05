import RiemannResearch.RH.QPrimeSubtreeBudget
import RiemannResearch.RH.QHeadSlopeLimit
import RiemannResearch.RH.MobiusPrimitiveCharge
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.NumberTheory.FiniteFloorTail
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-!
# Sharp and exponentially damped physical readouts of the prime tree

Source: Prime Trees, Carries and Zeta Zeros (5 November 2026), §7.3. The
fixed-site Abel deduction uses Abel's limit theorem. Signed primitive
bounds below use the project's implementation of Balazard, Proposition 7.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer ZetaTwoProbability

/-- The m-th physical readout term, with conductor m ≥ 1 in the sums below. -/
def remainderTerm (f : QHilbert) (n m : ℕ) : ℝ :=
  ((n % m : ℕ) : ℝ) * (charge f m / (m : ℝ))

private theorem shifted_range_eq_Icc (a : ℕ → ℝ) (H : ℕ) :
    (∑ k ∈ Finset.range H, a (k+1)) = ∑ m ∈ Finset.Icc 1 H, a m := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem physical_remainder_prefix_tendsto (f : QHilbert) (n : ℕ) :
    Tendsto (fun H => ∑ k ∈ Finset.range H, remainderTerm f n (k+1))
      atTop (𝓝 (-qSequence f n)) := by
  apply (signed_subtree_tendsto f n).congr
  intro H
  exact (signed_subtree_identity (charge f) H n).trans
    (shifted_range_eq_Icc (remainderTerm f n) H).symm

/-- Abel's theorem at each physical site, with the actual positive conductors
as power-series exponents. No absolute convergence of the undamped series
is assumed. -/
theorem physical_remainder_abel_tendsto (f : QHilbert) (n : ℕ) :
    Tendsto (fun x : ℝ => ∑' k : ℕ, remainderTerm f n (k+1) * x ^ (k+1))
      (𝓝[<] 1) (𝓝 (-qSequence f n)) := by
  have h := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (physical_remainder_prefix_tendsto f n)
  have hx : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    nhdsWithin_le_nhds
  simpa only [pow_succ, ← mul_assoc, tsum_mul_right, mul_one] using h.mul hx

/-- The discrete integral of the actual exponentially damped weights, in
the parameter used in the paper. The positive real limit is one-sided. -/
theorem physical_remainder_exponential_tendsto (f : QHilbert) (n : ℕ) :
    Tendsto (fun t : ℝ => ∑' k : ℕ,
      remainderTerm f n (k+1) * Real.exp (-(t * ((k+1 : ℕ) : ℝ))))
      (𝓝[>] 0) (𝓝 (-qSequence f n)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change Real.exp (-t) < 1
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have h := (physical_remainder_abel_tendsto f n).comp he
  apply h.congr
  intro t
  apply tsum_congr
  intro k
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem cutoff_prefix (a : ℕ → ℝ) (H N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, if m ≤ H then a m else 0) =
      ∑ m ∈ Finset.Icc 1 (min H N), a m := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
  tauto

/-- Reading the truncated floor sum by occurrence indices retains both
the conductor cutoff and the complete signed prefix under each quotient. -/
theorem clipped_floor_sum (b : ℕ → ℝ) (H n : ℕ) :
    (∑ m ∈ Finset.Icc 1 H, b m * ((n / m : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 (min H (n / j)), b m := by
  classical
  let a (m : ℕ) := b m * ((n / m : ℕ) : ℝ)
  let c (m : ℕ) := if m ≤ H then b m else 0
  calc
    _ = ∑ m ∈ Finset.Icc 1 (min n H), a m := by
      rw [← cutoff_prefix]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m ≤ n
      · simp [a, hm]
      · simp [a, hm, Nat.div_eq_of_lt (lt_of_not_ge hm)]
    _ = ∑ m ∈ Finset.Icc 1 n, c m * ((n / m : ℕ) : ℝ) := by
      simp only [c, ite_mul, zero_mul, a, cutoff_prefix, min_comm]
    _ = _ := by
      simpa only [zero_add, Nat.div_one, c, cutoff_prefix] using
        RiemannResearch.NumberTheory.finite_floor_tail_swap c 0 n

private theorem primitive_prefix_bound (f : QHilbert) (N : ℕ) :
    |∑ m ∈ Finset.Icc 1 N, charge f m| ≤ 14 * ‖toPareto f‖ * N := by
  by_cases hN : N = 0
  · simp [hN]
  have hR : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h := (norm_inner_le_norm (𝕜 := ℝ) (primitiveChargeRiesz N) (toPareto f)).trans
    (mul_le_mul_of_nonneg_right (primitiveChargeRiesz_norm_le N) (norm_nonneg _))
  rw [Real.norm_eq_abs, primitiveChargeRiesz_inner, abs_div, abs_of_pos hR] at h
  simpa only [charge, mobiusDifferenceCLM_apply, toPareto_sequence] using (div_le_iff₀ hR).mp h

private theorem reciprocal_prefix_bound (f : QHilbert) (N : ℕ) :
    |∑ m ∈ Finset.Icc 1 N, charge f m / (m : ℝ)| ≤ 7 * ‖toPareto f‖ := by
  have h := (norm_inner_le_norm (𝕜 := ℝ) (reciprocalChargeRiesz N) (toPareto f)).trans
    (mul_le_mul_of_nonneg_right (reciprocalChargeRiesz_norm_le N) (norm_nonneg _))
  simpa only [Real.norm_eq_abs, reciprocalChargeRiesz_inner, charge,
    mobiusDifferenceCLM_apply, toPareto_sequence] using h

private theorem reciprocal_Icc_eq_harmonic (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ)⁻¹) = (harmonic n : ℝ) := by
  rw [← shifted_range_eq_Icc]
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem floor_prefix_bound (f : QHilbert) (H n : ℕ) :
    |∑ m ∈ Finset.Icc 1 H, charge f m * ((n / m : ℕ) : ℝ)| ≤
      (14 * ‖toPareto f‖ * n) * (harmonic n : ℝ) := by
  rw [clipped_floor_sum]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 n, |∑ m ∈ Finset.Icc 1 (min H (n/j)), charge f m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 n, (14 * ‖toPareto f‖ * n) * (j : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      have hmin : ((min H (n / j) : ℕ) : ℝ) ≤ ((n / j : ℕ) : ℝ) := by
        exact_mod_cast min_le_right H (n/j)
      have hq : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / (j : ℝ) := Nat.cast_div_le
      exact (primitive_prefix_bound f _).trans (by
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hmin.trans hq) (show 0 ≤ 14 * ‖toPareto f‖ by positivity))
    _ = _ := by rw [← Finset.mul_sum, reciprocal_Icc_eq_harmonic]

theorem physical_remainder_prefix_exact (f : QHilbert) (H n : ℕ) :
    (∑ m ∈ Finset.Icc 1 H, remainderTerm f n m) =
      (n : ℝ) * (∑ m ∈ Finset.Icc 1 H, charge f m / (m : ℝ)) -
      (∑ m ∈ Finset.Icc 1 H, charge f m * ((n / m : ℕ) : ℝ)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hp : 0 < m := (Finset.mem_Icc.mp hm).1
  have hr : (m : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n m
  unfold remainderTerm
  field_simp [hr]
  linear_combination (charge f m) * he

/-- The signed prefix estimate is logarithmic after division by the site.
It holds for every cutoff, including cutoffs below the observation site. -/
theorem physical_remainder_harmonic_bound (f : QHilbert) (H n : ℕ) :
    |∑ k ∈ Finset.range H, remainderTerm f n (k+1)| ≤
      (‖toPareto f‖ * n) * (7 + 14 * (harmonic n : ℝ)) := by
  rw [shifted_range_eq_Icc, physical_remainder_prefix_exact]
  calc
    _ ≤ |(n : ℝ) * (∑ m ∈ Finset.Icc 1 H, charge f m / (m : ℝ))| +
        |∑ m ∈ Finset.Icc 1 H, charge f m * ((n / m : ℕ) : ℝ)| := abs_sub _ _
    _ ≤ (n : ℝ) * (7 * ‖toPareto f‖) + (14 * ‖toPareto f‖ * n) * (harmonic n : ℝ) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      exact add_le_add (mul_le_mul_of_nonneg_left (reciprocal_prefix_bound f H)
        (Nat.cast_nonneg n)) (floor_prefix_bound f H n)
    _ = _ := by ring

/-- Abel damping of an ordered sum stays inside any absolute bound on all
ordinary partial sums. The exponent matches conductors starting at one. -/
private theorem abel_abs_le_of_prefix (u : ℕ → ℝ) (M x : ℝ)
    (hM : ∀ H, |∑ k ∈ Finset.range H, u k| ≤ M) (hx : 0 ≤ x) (hx' : x < 1) :
    |∑' k : ℕ, u k * x ^ (k+1)| ≤ M := by
  let S (H : ℕ) := ∑ k ∈ Finset.range H, u k
  have hu (k : ℕ) : u k = S (k+1) - S k := by simp [S, Finset.sum_range_succ]
  have hgeo := summable_geometric_of_lt_one hx hx'
  have hMgeo := hgeo.mul_left M
  have hbound (k : ℕ) : ‖S k * x ^ k‖ ≤ M * x^k := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx k)]
    exact mul_le_mul_of_nonneg_right (hM k) (pow_nonneg hx k)
  have hs : Summable (fun k : ℕ => S k * x ^ k) := hMgeo.of_norm_bounded hbound
  have hs1 : Summable (fun k : ℕ => S (k+1) * x ^ (k+1)) := (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable (fun k : ℕ => S k * x ^ (k+1)) := by
    simpa only [pow_succ, ← mul_assoc] using hs.mul_right x
  have ht : (∑' k : ℕ, S (k+1) * x ^ (k+1)) = ∑' k : ℕ, S k * x ^ k := by
    have h := hs.tsum_eq_zero_add
    simpa [S] using h.symm
  have he : (∑' k : ℕ, u k * x ^ (k+1)) = (1-x) * (∑' k : ℕ, S k * x ^ k) := by
    calc
      _ = ∑' k : ℕ, (S (k+1) * x ^ (k+1) - S k * x ^ (k+1)) := by
        apply tsum_congr
        intro k
        rw [hu k, sub_mul]
      _ = _ := by
        rw [hs1.tsum_sub hs2, ht]
        simp_rw [pow_succ, ← mul_assoc, tsum_mul_right]
        ring
  have hT : |∑' k : ℕ, S k * x ^ k| ≤ M / (1-x) := by
    calc
      _ = ‖∑' k : ℕ, S k * x ^ k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : ℕ, ‖S k * x ^ k‖ := norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' k : ℕ, M * x ^ k := hs.norm.tsum_le_tsum hbound hMgeo
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hx hx']; ring
  rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx'.le)]
  calc
    _ ≤ (1-x) * (M / (1-x)) := mul_le_mul_of_nonneg_left hT (sub_nonneg.mpr hx'.le)
    _ = M := by field_simp [ne_of_gt (sub_pos.mpr hx')]

/-- A common Q-square envelope after division by n^a, for every a>1/2. -/
private theorem harmonic_weight_summable (C a : ℝ) (hC : 0 ≤ C) (ha : 1 / 2 < a) :
    Summable (fun n : ℕ => positiveQWeight n *
      ((C * (n : ℝ) * (7+14*(harmonic n : ℝ))) / (n : ℝ)^a)^2) := by
  let δ := (a - 1/2) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have he : 2 * δ - 2 * a < -1 := by dsimp [δ]; linarith
  let L := (C * (21 + 14 / δ))^2 / zetaTwo
  have hs := (Real.summable_nat_rpow.mpr he).mul_left L
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hpow : 1 ≤ (n : ℝ)^δ := Real.one_le_rpow hn1 hδ.le
  have hHnon : 0 ≤ (harmonic n : ℝ) := by
    rw [← reciprocal_Icc_eq_harmonic]
    exact Finset.sum_nonneg fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j)
  have hf : 7 + 14 * (harmonic n : ℝ) ≤ (21 + 14/δ) * (n : ℝ)^δ := by
    have hl := Real.log_le_rpow_div hn0.le hδ
    have hh := harmonic_le_one_add_log n
    calc
      _ ≤ 21 + 14 * ((n : ℝ)^δ / δ) := by linarith
      _ ≤ 21 * (n : ℝ)^δ + 14 * ((n : ℝ)^δ / δ) := by linarith
      _ = _ := by ring
  have hden := Real.rpow_pos_of_pos hn0 a
  have hval := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf (mul_nonneg hC hn0.le)) hden.le
  have hnon : 0 ≤ (C * (n : ℝ) * (7+14*(harmonic n : ℝ))) / (n : ℝ)^a := by positivity
  have hp : (n : ℝ)^(2*δ-2*a) = ((n : ℝ)^δ)^2 / ((n : ℝ)^a)^2 := by
    rw [Real.rpow_sub hn0, show 2*δ = δ*2 by ring, show 2*a = a*2 by ring,
      Real.rpow_mul hn0.le, Real.rpow_mul hn0.le, Real.rpow_two, Real.rpow_two]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ positiveQWeight n *
        ((C * (n : ℝ) * ((21+14/δ) * (n : ℝ)^δ)) / (n : ℝ)^a)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hval 2) (positiveQWeight_nonneg _)
    _ = _ := by
      rw [hp]
      dsimp [positiveQWeight, L]
      field_simp [zetaTwo_pos.ne', hn0.ne', hden.ne']

private theorem normalized_error_tendsto {ι : Type*} {l : Filter ι}
    (F : ι → ℕ → ℝ) (g : ℕ → ℝ) (C a : ℝ) (hC : 0 ≤ C) (ha : 1 / 2 < a)
    (hF : ∀ᶠ i in l, ∀ n : ℕ, |F i n| ≤ (C * n) * (7 + 14 * (harmonic n : ℝ)))
    (hg : ∀ n : ℕ, |g n| ≤ (C * n) * (7 + 14 * (harmonic n : ℝ)))
    (ht : ∀ n, Tendsto (fun i => F i n) l (𝓝 (g n))) :
    Tendsto (fun i => ∑' n : ℕ, positiveQWeight n * ((F i n - g n) / (n : ℝ)^a)^2)
      l (𝓝 0) := by
  have hs := harmonic_weight_summable (2*C) a (by positivity) ha
  have hl := tendsto_tsum_of_dominated_convergence hs (g := fun _ : ℕ => (0 : ℝ))
    (f := fun i n => positiveQWeight n * ((F i n - g n) / (n : ℝ)^a)^2)
    (fun n => by
      simpa only [sub_self, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero] using
        ((((ht n).sub_const (g n)).div_const ((n : ℝ)^a)).pow 2).const_mul (positiveQWeight n))
    (by
      filter_upwards [hF] with i hi
      intro n
      have he : |F i n - g n| ≤ ((2*C) * n) * (7+14*(harmonic n : ℝ)) := by
        calc
          _ ≤ |F i n| + |g n| := abs_sub _ _
          _ ≤ _ := by linarith only [hi n, hg n]
      have hd := Real.rpow_nonneg (Nat.cast_nonneg n) a
      have hle := div_le_div_of_nonneg_right he hd
      have hsq := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hd) hle 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg _)
      simpa only [div_pow, sq_abs] using hsq)
  simpa only [tsum_zero] using hl

/-- Both cutoffs converge strongly in the original Q measure after the
weaker site normalization n^a, a>1/2. The expressions are the full weighted
squared errors; the second uses the Abel parameter x approaching one below. -/
theorem normalized_remainder_energy_tendsto (f : QHilbert) (a : ℝ) (ha : 1 / 2 < a) :
    Tendsto (fun H => ∑' n : ℕ, positiveQWeight n *
      (((∑ k ∈ Finset.range H, remainderTerm f n (k+1)) + qSequence f n) / (n : ℝ)^a)^2)
        atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => ∑' n : ℕ, positiveQWeight n *
      (((∑' k : ℕ, remainderTerm f n (k+1) * x^(k+1)) + qSequence f n) / (n : ℝ)^a)^2)
        (𝓝[<] 1) (𝓝 0) := by
  have hg (n : ℕ) : |-qSequence f n| ≤ (‖toPareto f‖ * n) * (7+14*(harmonic n : ℝ)) :=
    le_of_tendsto (physical_remainder_prefix_tendsto f n).abs
      (Eventually.of_forall fun H => physical_remainder_harmonic_bound f H n)
  constructor
  · simpa only [sub_neg_eq_add] using normalized_error_tendsto
      (fun H n => ∑ k ∈ Finset.range H, remainderTerm f n (k+1)) (fun n => -qSequence f n)
      ‖toPareto f‖ a (norm_nonneg _) ha
      (Eventually.of_forall fun H n => physical_remainder_harmonic_bound f H n)
      hg (physical_remainder_prefix_tendsto f)
  · have hdom : ∀ᶠ x : ℝ in 𝓝[<] 1, ∀ n : ℕ,
        |∑' k : ℕ, remainderTerm f n (k+1) * x^(k+1)| ≤
          (‖toPareto f‖ * n) * (7+14*(harmonic n : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx1 hx0
      intro n
      exact abel_abs_le_of_prefix _ _ _ (fun H => physical_remainder_harmonic_bound f H n)
        (le_of_lt hx0) hx1
    simpa only [sub_neg_eq_add] using normalized_error_tendsto
      (fun x n => ∑' k : ℕ, remainderTerm f n (k+1) * x^(k+1)) (fun n => -qSequence f n)
      ‖toPareto f‖ a (norm_nonneg _) ha hdom hg (physical_remainder_abel_tendsto f)

/-- Hilbert realization of a weighted physical sequence when its weighted
energy is finite. The positive exponent automatically anchors the zero site. -/
def normalizedPhysicalReadout (g : ℕ → ℝ) (a : ℝ) : QHilbert := by
  classical
  exact if h : Summable (fun n : ℕ => positiveQWeight n * (g n / (n : ℝ)^a)^2)
    then encodeQ (fun n : ℕ => g n / (n : ℝ)^a) h else 0

theorem normalizedPhysicalReadout_sequence {g : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hs : Summable (fun n : ℕ => positiveQWeight n * (g n / (n : ℝ)^a)^2)) (n : ℕ) :
    qSequence (normalizedPhysicalReadout g a) n = g n / (n : ℝ)^a := by
  classical
  rw [normalizedPhysicalReadout, dif_pos hs,
    qSequence_encodeQ _ _ (by simp [Real.zero_rpow ha.ne'])]

private theorem summable_of_harmonic_envelope (g : ℕ → ℝ) (a C : ℝ)
    (ha : 1 / 2 < a) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, |g n| ≤ (C*n) * (7 + 14*(harmonic n : ℝ))) :
    Summable (fun n : ℕ => positiveQWeight n * (g n / (n : ℝ)^a)^2) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)) _
    (harmonic_weight_summable C a hC ha)
  intro n
  apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
  have hd := Real.rpow_nonneg (Nat.cast_nonneg n) a
  have h := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hd)
    (div_le_div_of_nonneg_right (hb n) hd) 2
  simpa only [div_pow, sq_abs] using h

private theorem normalized_Hilbert_tendsto_of_energy {ι : Type*} {l : Filter ι}
    (F : ι → ℕ → ℝ) (g : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hF : ∀ᶠ i in l, Summable (fun n : ℕ => positiveQWeight n * (F i n / (n : ℝ)^a)^2))
    (hg : Summable (fun n : ℕ => positiveQWeight n * (g n / (n : ℝ)^a)^2))
    (he : Tendsto (fun i => ∑' n : ℕ, positiveQWeight n * ((F i n - g n) / (n : ℝ)^a)^2)
      l (𝓝 0)) :
    Tendsto (fun i => normalizedPhysicalReadout (F i) a) l (𝓝 (normalizedPhysicalReadout g a)) := by
  have ht : Tendsto (fun i => ‖normalizedPhysicalReadout (F i) a -
      normalizedPhysicalReadout g a‖^2) l (𝓝 0) := by
    apply he.congr'
    filter_upwards [hF] with i hi
    rw [qNorm_weighted_sq]
    apply tsum_congr
    intro n
    have hsub : qSequence
        (normalizedPhysicalReadout (F i) a - normalizedPhysicalReadout g a) n =
        qSequence (normalizedPhysicalReadout (F i) a) n -
        qSequence (normalizedPhysicalReadout g a) n :=
      congrFun (qSequenceLinear.map_sub _ _) n
    rw [hsub, normalizedPhysicalReadout_sequence ha hi n, normalizedPhysicalReadout_sequence ha hg n,
      sub_div]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

/-- Equation (33) in the Q Hilbert space itself, with a smaller site exponent.
All the positive-conductor approximants and the limit have finite Q energy. -/
theorem normalized_remainder_Hilbert_tendsto (f : QHilbert) (a : ℝ) (ha : 1 / 2 < a) :
    Tendsto (fun H => normalizedPhysicalReadout
      (fun n => ∑ k ∈ Finset.range H, remainderTerm f n (k+1)) a)
      atTop (𝓝 (normalizedPhysicalReadout (fun n => -qSequence f n) a)) ∧
    Tendsto (fun x : ℝ => normalizedPhysicalReadout
      (fun n => ∑' k : ℕ, remainderTerm f n (k+1) * x^(k+1)) a)
      (𝓝[<] 1) (𝓝 (normalizedPhysicalReadout (fun n => -qSequence f n) a)) := by
  have h0 : 0 < a := by linarith
  have hg (n : ℕ) : |-qSequence f n| ≤ (‖toPareto f‖ * n) * (7+14*(harmonic n : ℝ)) :=
    le_of_tendsto (physical_remainder_prefix_tendsto f n).abs
      (Eventually.of_forall fun H => physical_remainder_harmonic_bound f H n)
  have hgs := summable_of_harmonic_envelope _ a _ ha (norm_nonneg _) hg
  obtain ⟨hp, hA⟩ := normalized_remainder_energy_tendsto f a ha
  constructor
  · refine normalized_Hilbert_tendsto_of_energy _ _ a h0 ?_ hgs ?_
    · apply Eventually.of_forall
      intro H
      exact summable_of_harmonic_envelope _ a _ ha (norm_nonneg _)
        (physical_remainder_harmonic_bound f H)
    · simpa only [sub_neg_eq_add] using hp
  · refine normalized_Hilbert_tendsto_of_energy _ _ a h0 ?_ hgs ?_
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx1 hx0
      exact summable_of_harmonic_envelope _ a _ ha (norm_nonneg _)
        (fun n => abel_abs_le_of_prefix _ _ _ (fun H => physical_remainder_harmonic_bound f H n)
          (le_of_lt hx0) hx1)
    · simpa only [sub_neg_eq_add] using hA

end RiemannResearch.RH.QPrimeSubtreeBudget
