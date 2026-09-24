import RiemannResearch.NumberTheory.QuotientWindowEnergySplit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

/-!
# Limits of the diagonal and isolated quotient-window energies

The exact arithmetic separation is provided by QuotientWindowEnergySplit.
Dominated convergence is applied only after this separation. In particular, this
module makes no claim that the original moving-window energy tends to zero.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.QuotientWindow

/-- The low quotient-window square bound used as a summable majorant. -/
theorem low_window_sum_sq_le (η : ℕ → ℝ)
    (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ))
    {N d : ℕ} (hd : 0 < d) (hN : d * (d + 1) ≤ N) :
    (∑ n ∈ window N d, η n) ^ 2 ≤ 4 / (d : ℝ) ^ 2 := by
  have hs : |∑ n ∈ window N d, η n| ≤ 2 / (d : ℝ) := by
    calc
      _ ≤ ∑ n ∈ window N d, |η n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ window N d, 1 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hη n (mem_window_bounds hd hn).1
      _ ≤ _ := harmonic_window_le hd hN
  have hh := (sq_le_sq₀ (abs_nonneg (∑ n ∈ window N d, η n))
    (by positivity : (0 : ℝ) ≤ 2 / (d : ℝ))).mpr hs
  simpa only [sq_abs, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh

/-- Fixed-window cancellation eliminates precisely the low-window energy. -/
theorem low_window_square_energy_tendsto_zero (η : ℕ → ℝ)
    (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ))
    (hlim : ∀ d, 0 < d →
      Tendsto (fun N => ∑ n ∈ window N d, η n) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ d ∈ (Finset.Icc 1 N).filter
      (fun d => d * (d + 1) ≤ N), (∑ n ∈ window N d, η n) ^ 2)
      atTop (𝓝 0) := by
  let s (N : ℕ) := (Finset.Icc 1 N).filter (fun d => d * (d + 1) ≤ N)
  let f (N d : ℕ) : ℝ := if d ∈ s N then (∑ n ∈ window N d, η n) ^ 2 else 0
  have hsum0 : Summable (fun d : ℕ => ((d : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hsum : Summable (fun d : ℕ => 4 / (d : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv] using hsum0.mul_left (4 : ℝ)
  have hpoint (d : ℕ) : Tendsto (fun N => f N d) atTop (𝓝 (0 : ℝ)) := by
    by_cases hd : 0 < d
    · have he : ∀ᶠ N : ℕ in atTop, f N d = (∑ n ∈ window N d, η n) ^ 2 := by
        filter_upwards [eventually_ge_atTop (d * (d + 1))] with N hN
        have hdN : d ≤ N := by nlinarith
        have hmem : d ∈ s N :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd, hdN⟩, hN⟩
        simp only [f, if_pos hmem]
      have hp : Tendsto (fun N => (∑ n ∈ window N d, η n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
        simpa using (hlim d hd).pow 2
      exact hp.congr' (by filter_upwards [he] with N hN; exact hN.symm)
    · have hd0 : d = 0 := by omega
      simpa [f, s, hd0] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ d, ‖f N d‖ ≤ 4 / (d : ℝ) ^ 2 := by
    apply Eventually.of_forall
    intro N d
    by_cases hd : d ∈ s N
    · have hds := Finset.mem_filter.mp hd
      have hd0 : 0 < d := (Finset.mem_Icc.mp hds.1).1
      simpa only [f, if_pos hd, Real.norm_eq_abs, abs_sq] using
        low_window_sum_sq_le η hη hd0 hds.2
    · simp only [f, if_neg hd, norm_zero]
      positivity
  have hconv := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have heq (N : ℕ) : (∑' d, f N d) =
      ∑ d ∈ s N, (∑ n ∈ window N d, η n) ^ 2 := by
    rw [tsum_eq_sum (s := s N) (by intro d hd; simp [f, hd])]
    apply Finset.sum_congr rfl
    intro d hd
    simp [f, hd]
  simpa only [heq, tsum_zero, s] using hconv

/-- Every fixed nonzero charge ultimately enters the isolated-window sum. -/
theorem isolated_square_energy_tendsto (η : ℕ → ℝ) (hzero : η 0 = 0)
    (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ)) :
    Tendsto (fun N => ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n => N < (N / n) * (N / n + 1)), η n ^ 2)
      atTop (𝓝 (∑' n, η n ^ 2)) := by
  let s (N : ℕ) := (Finset.Icc 1 N).filter
    (fun n => N < (N / n) * (N / n + 1))
  let f (N n : ℕ) : ℝ := if n ∈ s N then η n ^ 2 else 0
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simpa only [one_div] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
  have hpoint (n : ℕ) : Tendsto (fun N => f N n) atTop (𝓝 (η n ^ 2)) := by
    by_cases hn : 0 < n
    · apply tendsto_const_nhds.congr'
      filter_upwards [quotient_diagonal_eventually hn] with N hN
      change n ∈ s N at hN
      simp only [f, if_pos hN]
    · have hn0 : n = 0 := by omega
      simpa [f, s, hn0, hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ n, ‖f N n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    apply Eventually.of_forall
    intro N n
    by_cases hn : n ∈ s N
    · have hn0 : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hq := (sq_le_sq₀ (abs_nonneg (η n))
        (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))).mpr (hη n hn0)
      simpa only [f, if_pos hn, Real.norm_eq_abs, abs_sq,
        sq_abs, div_pow, one_pow] using hq
    · simp only [f, if_neg hn, norm_zero]
      positivity
  have hconv := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have heq (N : ℕ) : (∑' n, f N n) = ∑ n ∈ s N, η n ^ 2 := by
    rw [tsum_eq_sum (s := s N) (by intro n hn; simp [f, hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, hn]
  simpa only [heq, s] using hconv

/-- General window-energy limit: the persistent mass is the isolated charge energy. -/
theorem window_square_energy_tendsto (η : ℕ → ℝ) (hzero : η 0 = 0)
    (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ))
    (hlim : ∀ d, 0 < d →
      Tendsto (fun N => ∑ n ∈ window N d, η n) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ d ∈ Finset.Icc 1 N,
      (∑ n ∈ window N d, η n) ^ 2) atTop (𝓝 (∑' n, η n ^ 2)) := by
  have h := (low_window_square_energy_tendsto_zero η hη hlim).add
    (isolated_square_energy_tendsto η hzero hη)
  simpa only [zero_add, ← sum_window_sq_eq_low_add_isolated] using h

end RiemannResearch.NumberTheory.QuotientWindow
