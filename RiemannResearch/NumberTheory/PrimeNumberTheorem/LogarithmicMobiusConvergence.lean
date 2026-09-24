import RiemannResearch.NumberTheory.LogarithmicKernelConvolution
import RiemannResearch.RH.MobiusQuotientEnergy
import RiemannResearch.NumberTheory.QuotientWindowEnergySplit

/-!
# Möbius floor convolutions with a cubic logarithmic remainder

The analytic remainder bound is explicit. Its unconditional provider is an
Abel-summed consequence of the repository's established MediumPNT theorem,
assembled in `LogarithmicMobiusMean`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.NumberTheory.QuotientWindow
open RiemannResearch.RH.Pareto

private theorem sum_positive_eq_shifted_range (f : ℕ → ℝ) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, f d) = ∑ k ∈ Finset.range M, f (k + 1) := by
  have he : (Finset.range M).image (fun k => k + 1) = Finset.Icc 1 M := by
    ext n
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · intro hn
      exact ⟨n - 1, by omega, by omega⟩
  rw [← he, Finset.sum_image]
  intro a ha b hb hab
  dsimp only at hab
  omega

private theorem quotient_tail_windows (N K : ℕ) (hK : 0 < K) :
    (Finset.Icc 1 (K - 1)).biUnion (window N) = Finset.Ioc (N / K) N := by
  ext d
  constructor
  · intro hd
    obtain ⟨q, hq, hdq⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hqpos, hqK⟩ := Finset.mem_Icc.mp hq
    have hq1 : 0 < q + 1 := by omega
    have hq1K : q + 1 ≤ K := by omega
    have hlow : N / K ≤ N / (q + 1) := by
      apply (Nat.le_div_iff_mul_le hq1).mpr
      exact (Nat.mul_le_mul_left (N / K) hq1K).trans (Nat.div_mul_le_self N K)
    have hw := Finset.mem_Ioc.mp hdq
    have hdN := (Finset.mem_Icc.mp (window_subset hqpos hdq)).2
    exact Finset.mem_Ioc.mpr ⟨hlow.trans_lt hw.1, hdN⟩
  · intro hd
    obtain ⟨hlo, hdN⟩ := Finset.mem_Ioc.mp hd
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hlo
    have hqpos : 0 < N / d := by
      have : 1 ≤ N / d := (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdN)
      omega
    have hqK : N / d < K := by
      apply (Nat.div_lt_iff_lt_mul hdpos).mpr
      have hn := (Nat.div_lt_iff_lt_mul hK).mp hlo
      simpa [Nat.mul_comm] using hn
    exact Finset.mem_biUnion.mpr
      ⟨N / d, Finset.mem_Icc.mpr ⟨hqpos, by omega⟩,
        mem_window_quotient hdpos hdN⟩

private theorem quotient_tail_convolution_eq_windows
    (a e : ℕ → ℝ) (N K : ℕ) (hK : 0 < K) :
    (∑ d ∈ Finset.Ioc (N / K) N, a d * e (N / d)) =
      ∑ q ∈ Finset.Icc 1 (K - 1), e q * ∑ d ∈ window N q, a d := by
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.Icc 1 (K - 1)) : Set ℕ) (window N) := by
    intro q hq r hr hqr
    apply Finset.disjoint_left.mpr
    intro d hdq hdr
    have hqe := quotient_of_mem_window (Finset.mem_Icc.mp hq).1 hdq
    have hre := quotient_of_mem_window (Finset.mem_Icc.mp hr).1 hdr
    exact hqr (hqe.symm.trans hre)
  rw [← quotient_tail_windows N K hK, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [quotient_of_mem_window (Finset.mem_Icc.mp hq).1 hd]
  ring

/-- Every fixed finite collection of quotient windows cancels unconditionally.
The coefficients e(q) are unrestricted because K is fixed before N grows. -/
theorem mobius_quotient_tail_convolution_tendsto_zero
    (e : ℕ → ℝ) (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N => ∑ d ∈ Finset.Ioc (N / K) N,
      ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * e (N / d))
      atTop (𝓝 0) := by
  have ht := tendsto_finsetSum (Finset.Icc 1 (K - 1)) (fun q hq =>
    (((mobiusReciprocalSum_tendsto_zero.comp
      (nat_div_fixed_tendsto (Finset.mem_Icc.mp hq).1)).sub
      (mobiusReciprocalSum_tendsto_zero.comp
        (nat_div_fixed_tendsto (show 0 < q + 1 by omega)))).const_mul (e q)))
  have heq (N : ℕ) :
      (∑ d ∈ Finset.Ioc (N / K) N,
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * e (N / d)) =
      ∑ q ∈ Finset.Icc 1 (K - 1),
        e q * (mobiusReciprocalSum (N / q) - mobiusReciprocalSum (N / (q + 1))) := by
    rw [quotient_tail_convolution_eq_windows _ e N K hK]
    apply Finset.sum_congr rfl
    intro q hq
    rw [mobius_quotient_difference_eq_window N q (Finset.mem_Icc.mp hq).1]
  simpa only [← heq, Function.comp_def, sub_zero, mul_zero, Finset.sum_const_zero] using ht

/-- A cubic logarithmic remainder suffices for Möbius floor-convolution
cancellation. No logarithmic Mertens rate is assumed. -/
theorem mobius_log_cube_quotient_convolution_tendsto_zero
    (e : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ q, 0 < q → |e q| ≤ D / (1 + Real.log ((q : ℝ) + 1)) ^ 3) :
    Tendsto (fun N => ∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * e (N / d))
      atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
  have ha : ∀ d, 0 < d → |a d| ≤ 1 / (d : ℝ) := by
    intro d hd
    dsimp [a]
    simp only [abs_div, abs_of_nonneg (show 0 ≤ (d : ℝ) from Nat.cast_nonneg d)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hlog0 : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop))
  have hlog : Tendsto (fun K : ℕ => 1 + Real.log (K : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun K => by linarith) hlog0
  have hsmall : Tendsto (fun K : ℕ => 3 * D / (1 + Real.log (K : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hKsmall, hK⟩ :=
    ((hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))).and
      (eventually_gt_atTop (0 : ℕ))).exists
  have htail := mobius_quotient_tail_convolution_tendsto_zero e K hK
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN
  have ht := hN₀ N hN
  simp only [Real.dist_eq, sub_zero] at ht ⊢
  have hhead := reciprocal_log_cube_quotient_head_bound a e D hD ha he N K hK
  rw [← sum_positive_eq_shifted_range (fun d => a d * e (N / d)) (N / K)] at hhead
  have hdis : Disjoint (Finset.Icc 1 (N / K)) (Finset.Ioc (N / K) N) := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    have := Finset.mem_Icc.mp hd
    have := Finset.mem_Ioc.mp hd'
    omega
  have hu : Finset.Icc (1 : ℕ) (N / K) ∪ Finset.Ioc (N / K) N = Finset.Icc 1 N := by
    ext d
    have hle := Nat.div_le_self N K
    constructor
    · intro hd
      rcases Finset.mem_union.mp hd with hd | hd
      · obtain ⟨hdpos, hdlo⟩ := Finset.mem_Icc.mp hd
        exact Finset.mem_Icc.mpr ⟨hdpos, hdlo.trans hle⟩
      · obtain ⟨hdlo, hdhi⟩ := Finset.mem_Ioc.mp hd
        exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hdlo, hdhi⟩
    · intro hd
      obtain ⟨hdpos, hdhi⟩ := Finset.mem_Icc.mp hd
      by_cases hdlo : d ≤ N / K
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hdpos, hdlo⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hdlo, hdhi⟩))
  change |∑ d ∈ Finset.Icc 1 N, a d * e (N / d)| < ε
  rw [← hu, Finset.sum_union hdis]
  have habs := abs_add_le
    (∑ d ∈ Finset.Icc 1 (N / K), a d * e (N / d))
    (∑ d ∈ Finset.Ioc (N / K) N, a d * e (N / d))
  change |∑ d ∈ Finset.Ioc (N / K) N, a d * e (N / d)| < ε / 2 at ht
  linarith

end RiemannResearch.NumberTheory.PrimeNumberTheorem
