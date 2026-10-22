import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform reciprocal compatibility in the absolute convergence half-plane

The estimates below hold for every complex argument with real part at least
`σ > 1`. In particular they hold for every real ordinate shift, with no averaging,
zero-distribution hypothesis, or Riemann hypothesis. The cutoff `N` includes the
terms `1 ≤ n < N`; use `N = Y + 1` for the usual cutoff `n ≤ Y`.

The tail is a genuine summable p-series tail. Its summability and convergence to
zero are proved, rather than supplied as hypotheses. The full Möbius reciprocal
identity is imported from Mathlib's unconditional L-series theory.

Mathlib source (supports the imported analytic/arithmetic identity):
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/NumberTheory/LSeries/Dirichlet.lean
-/

noncomputable section

open Filter Finset
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannResearch.Analysis.AbsoluteReciprocalCompatibility

/-- An L-series truncation, including Mathlib's zero term (which is zero). -/
def partialSum (f : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, LSeries.term f s n

/-- The absolute-value p-series majorant, independent of imaginary part. -/
def weight (σ : ℝ) (n : ℕ) : ℝ := ‖LSeries.term 1 (σ : ℂ) n‖

def mass (σ : ℝ) : ℝ := ∑' n, weight σ n

def tail (σ : ℝ) (N : ℕ) : ℝ :=
  ∑' n : { n // n ∉ range N }, weight σ n

lemma weight_eq (σ : ℝ) (n : ℕ) :
    weight σ n = if n = 0 then 0 else 1 / (n : ℝ) ^ σ := by
  simp [weight, LSeries.norm_term_eq]

lemma summable_weight {σ : ℝ} (hσ : 1 < σ) : Summable (weight σ) := by
  exact (LSeriesSummable_one_iff.mpr (by simpa using hσ)).norm

lemma mass_nonneg (σ : ℝ) : 0 ≤ mass σ :=
  tsum_nonneg fun _ => norm_nonneg _

lemma tail_nonneg (σ : ℝ) (N : ℕ) : 0 ≤ tail σ N :=
  tsum_nonneg fun _ => norm_nonneg _

lemma term_norm_le_weight {σ : ℝ} {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hs : σ ≤ s.re) (n : ℕ) :
    ‖LSeries.term f s n‖ ≤ weight σ n := by
  apply (LSeries.norm_term_le (g := 1) s (by simpa using hf n)).trans
  exact LSeries.norm_term_le_of_re_le_re 1 (by simpa using hs) n

lemma partial_norm_le_mass {σ : ℝ} (hσ : 1 < σ) {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hs : σ ≤ s.re) (N : ℕ) :
    ‖partialSum f s N‖ ≤ mass σ := by
  calc
    ‖partialSum f s N‖ ≤ ∑ n ∈ range N, ‖LSeries.term f s n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, weight σ n :=
      sum_le_sum fun n _ => term_norm_le_weight hf hs n
    _ ≤ mass σ := (summable_weight hσ).sum_le_tsum _ (fun _ _ => norm_nonneg _)

lemma LSeries_norm_le_mass {σ : ℝ} (hσ : 1 < σ) {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖LSeries f s‖ ≤ mass σ :=
  tsum_of_norm_bounded (summable_weight hσ).hasSum (term_norm_le_weight hf hs)

lemma partial_error_le_tail {σ : ℝ} (hσ : 1 < σ) {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hs : σ ≤ s.re) (N : ℕ) :
    ‖partialSum f s N - LSeries f s‖ ≤ tail σ N := by
  have hnorm : Summable fun n => ‖LSeries.term f s n‖ :=
    (summable_weight hσ).of_nonneg_of_le (fun _ => norm_nonneg _)
      (term_norm_le_weight hf hs)
  rw [norm_sub_rev, LSeries, ← hnorm.of_norm.sum_add_tsum_subtype_compl (range N)]
  simp only [partialSum, add_sub_cancel_left]
  exact tsum_of_norm_bounded ((summable_weight hσ).subtype _).hasSum
    (fun n => term_norm_le_weight hf hs n)

lemma tail_tendsto_zero (σ : ℝ) : Tendsto (tail σ) atTop (𝓝 0) :=
  (tendsto_tsum_compl_atTop_zero (weight σ)).comp tendsto_finset_range

lemma weight_eq_rpow {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    weight σ n = (n : ℝ) ^ (-σ) := by
  rw [weight_eq]
  by_cases hn : n = 0
  · have hexp : -σ ≠ 0 := neg_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hσ))
    simp [hn, Real.zero_rpow hexp]
  · rw [if_neg hn, Real.rpow_neg (Nat.cast_nonneg n), one_div]

lemma tail_eq_mass_sub_sum {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    tail σ N = mass σ - ∑ n ∈ range N, weight σ n := by
  have h := (summable_weight hσ).sum_add_tsum_subtype_compl (range N)
  change (∑ n ∈ range N, weight σ n) + tail σ N = mass σ at h
  linarith

/-- Integral-test rate for the genuine p-series tail. -/
theorem tail_le_power {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 2 ≤ N) :
    tail σ N ≤ ((N : ℝ) - 1) ^ (1 - σ) / (σ - 1) := by
  have hc : 0 < (N : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hexp : -σ < -1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici ((N : ℝ) - 1)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hc.trans_le hx) hxy (by linarith)
  have hbound := AntitoneOn.abs_tsum_sub_sum_range_le_integral
    (le_trans (by norm_num : 1 ≤ 2) hN) hanti
    (integrableOn_Ioi_rpow_of_lt hexp hc)
    (fun x hx => Real.rpow_nonneg (hc.le.trans hx.le) _)
  have htail : tail σ N =
      (∑' n : ℕ, (n : ℝ) ^ (-σ)) - ∑ n ∈ range N, (n : ℝ) ^ (-σ) := by
    rw [tail_eq_mass_sub_sum hσ]
    simp only [mass, weight_eq_rpow hσ]
  rw [← htail, abs_of_nonneg (tail_nonneg _ _)] at hbound
  apply hbound.trans_eq
  rw [integral_Ioi_rpow_of_lt hexp hc]
  rw [show -σ + 1 = 1 - σ by ring, show 1 - σ = -(σ - 1) by ring,
    neg_div_neg_eq]

lemma mass_le {σ : ℝ} (hσ : 1 < σ) : mass σ ≤ 1 + 1 / (σ - 1) := by
  have htail := tail_le_power hσ (N := 2) (le_refl 2)
  norm_num at htail
  have hsum : (∑ n ∈ range 2, weight σ n) = 1 := by
    simp [sum_range_succ, weight_eq]
  have hsplit := (summable_weight hσ).sum_add_tsum_subtype_compl (range 2)
  change (∑ n ∈ range 2, weight σ n) + tail σ 2 = mass σ at hsplit
  rw [hsum] at hsplit
  simp only [one_div] at hsplit ⊢
  linarith

lemma moebius_norm_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  norm_cast
  exact ArithmeticFunction.abs_moebius_le_one

def zetaPartial (s : ℂ) (N : ℕ) : ℂ := partialSum 1 s N

def moebiusPartial (s : ℂ) (N : ℕ) : ℂ :=
  partialSum (fun n => (ArithmeticFunction.moebius n : ℂ)) s N

/-- The same deterministic error bound holds at every ordinate, since only `re s`
enters the majorant. This does not extend the reciprocal identity into the critical strip. -/
theorem reciprocal_product_error {σ : ℝ} (hσ : 1 < σ) {s : ℂ}
    (hs : σ ≤ s.re) (N : ℕ) :
    ‖zetaPartial s N * moebiusPartial s N - 1‖ ≤ 2 * mass σ * tail σ N := by
  let z := LSeries 1 s
  let m := LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s
  have hzm : z * m = 1 :=
    LSeries_one_mul_Lseries_moebius (lt_of_lt_of_le hσ hs)
  have hz : ‖z‖ ≤ mass σ := LSeries_norm_le_mass hσ (by simp) hs
  have hmN : ‖moebiusPartial s N‖ ≤ mass σ :=
    partial_norm_le_mass hσ moebius_norm_le_one hs N
  have hzerr : ‖zetaPartial s N - z‖ ≤ tail σ N :=
    partial_error_le_tail hσ (by simp) hs N
  have hmerr : ‖moebiusPartial s N - m‖ ≤ tail σ N :=
    partial_error_le_tail hσ moebius_norm_le_one hs N
  have hdecomp : zetaPartial s N * moebiusPartial s N - 1 =
      (zetaPartial s N - z) * moebiusPartial s N + z * (moebiusPartial s N - m) := by
    rw [← hzm]
    ring
  calc
    ‖zetaPartial s N * moebiusPartial s N - 1‖
        ≤ ‖zetaPartial s N - z‖ * ‖moebiusPartial s N‖ +
          ‖z‖ * ‖moebiusPartial s N - m‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ ≤ tail σ N * mass σ + mass σ * tail σ N :=
      add_le_add (mul_le_mul hzerr hmN (norm_nonneg _) (tail_nonneg _ _))
        (mul_le_mul hz hmerr (norm_nonneg _) (mass_nonneg _))
    _ = 2 * mass σ * tail σ N := by ring

/-- Explicit deterministic convergence rate, uniform in both real and imaginary
parts on `re s ≥ σ`. -/
theorem reciprocal_product_error_le_power {σ : ℝ} (hσ : 1 < σ) {s : ℂ}
    (hs : σ ≤ s.re) {N : ℕ} (hN : 2 ≤ N) :
    ‖zetaPartial s N * moebiusPartial s N - 1‖
      ≤ 2 * mass σ * (((N : ℝ) - 1) ^ (1 - σ) / (σ - 1)) :=
  (reciprocal_product_error hσ hs N).trans <|
    mul_le_mul_of_nonneg_left (tail_le_power hσ hN)
      (mul_nonneg (by norm_num) (mass_nonneg σ))

/-- The rate with a completely explicit constant depending only on `σ`. -/
theorem reciprocal_product_error_explicit {σ : ℝ} (hσ : 1 < σ) {s : ℂ}
    (hs : σ ≤ s.re) {N : ℕ} (hN : 2 ≤ N) :
    ‖zetaPartial s N * moebiusPartial s N - 1‖ ≤
      2 * (1 + 1 / (σ - 1)) * (((N : ℝ) - 1) ^ (1 - σ) / (σ - 1)) := by
  apply (reciprocal_product_error_le_power hσ hs hN).trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mass_le hσ) (by norm_num))
  exact (tail_nonneg σ N).trans (tail_le_power hσ hN)

/-- Uniform convergence on an unbounded half-plane, hence at every ordinate shift. -/
theorem reciprocal_product_tendstoUniformlyOn {σ : ℝ} (hσ : 1 < σ) :
    TendstoUniformlyOn (fun N s => zetaPartial s N * moebiusPartial s N)
      (fun _ => (1 : ℂ)) atTop { s : ℂ | σ ≤ s.re } := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hbudget : Tendsto (fun N => 2 * mass σ * tail σ N) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => 2 * mass σ) atTop (𝓝 (2 * mass σ))).mul
        (tail_tendsto_zero σ))
  filter_upwards [hbudget.eventually (gt_mem_nhds hε)] with N hN s hs
  rw [dist_eq_norm, norm_sub_rev]
  exact (reciprocal_product_error hσ hs N).trans_lt hN

/-- Both finite polynomials eventually have no zeros anywhere in the half-plane
`re s ≥ σ`, with one cutoff working for every imaginary part. -/
theorem eventually_nonzero_on_halfPlane {σ : ℝ} (hσ : 1 < σ) :
    ∀ᶠ N in atTop, ∀ s : ℂ, σ ≤ s.re →
      zetaPartial s N ≠ 0 ∧ moebiusPartial s N ≠ 0 := by
  have hbudget : Tendsto (fun N => 2 * mass σ * tail σ N) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => 2 * mass σ) atTop (𝓝 (2 * mass σ))).mul
        (tail_tendsto_zero σ))
  filter_upwards [hbudget.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN s hs
  have herror : ‖zetaPartial s N * moebiusPartial s N - 1‖ < 1 :=
    (reciprocal_product_error hσ hs N).trans_lt hN
  constructor
  · intro hzero
    simp [hzero] at herror
  · intro hzero
    simp [hzero] at herror

theorem zetaPartial_tendstoUniformlyOn {σ : ℝ} (hσ : 1 < σ) :
    TendstoUniformlyOn (fun N s => zetaPartial s N) riemannZeta atTop
      { s : ℂ | σ ≤ s.re } := by
  change TendstoUniformlyOn
    (fun N s => ∑ n ∈ range N, LSeries.term 1 s n)
    riemannZeta atTop { s : ℂ | σ ≤ s.re }
  have h := tendstoUniformlyOn_tsum_nat (summable_weight hσ)
    (s := { s : ℂ | σ ≤ s.re })
    (fun n s hs => term_norm_le_weight (f := 1) (by simp) hs n)
  apply h.congr_right
  intro s hs
  exact LSeries_one_eq_riemannZeta (lt_of_lt_of_le hσ hs)

lemma LSeries_moebius_eq_reciprocal {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 / riemannZeta s := by
  have hz : riemannZeta s ≠ 0 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_ne_zero_of_one_lt_re hs
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm, LSeries_one_eq_riemannZeta hs] using
    LSeries_one_mul_Lseries_moebius hs

theorem moebiusPartial_tendstoUniformlyOn {σ : ℝ} (hσ : 1 < σ) :
    TendstoUniformlyOn (fun N s => moebiusPartial s N)
      (fun s => 1 / riemannZeta s) atTop { s : ℂ | σ ≤ s.re } := by
  change TendstoUniformlyOn
    (fun N s => ∑ n ∈ range N,
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n)
    (fun s => 1 / riemannZeta s) atTop { s : ℂ | σ ≤ s.re }
  have h := tendstoUniformlyOn_tsum_nat (summable_weight hσ)
    (s := { s : ℂ | σ ≤ s.re })
    (fun n s hs => term_norm_le_weight moebius_norm_le_one hs n)
  apply h.congr_right
  intro s hs
  exact LSeries_moebius_eq_reciprocal (lt_of_lt_of_le hσ hs)

/-- Specialization of the same error bound to arbitrary real ordinate shifts. -/
theorem reciprocal_product_error_at_ordinate {σ : ℝ} (hσ : 1 < σ) {s : ℂ}
    (hs : σ ≤ s.re) (t : ℝ) (N : ℕ) :
    ‖zetaPartial (s - t * Complex.I) N * moebiusPartial (s - t * Complex.I) N - 1‖
      ≤ 2 * mass σ * tail σ N := by
  apply reciprocal_product_error hσ
  simpa using hs

end RiemannResearch.Analysis.AbsoluteReciprocalCompatibility
