import RiemannResearch.NumberTheory.QuotientWindowEnergyLimit
import RiemannResearch.Analysis.BoundedSquareEnergy

/-!
# General quotient-kernel energy limit

The arithmetic inputs are an inverse-linear charge bound, bounded null partial
sums, and their exact quotient-window identity. The theorem applies to suitably
normalized finite combinations of dilated reciprocal Möbius charges.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.QuotientWindow

private theorem fixed_div_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => N / k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * k)] with N hN
  exact (Nat.le_div_iff_mul_le hk).mpr hN

/-- Exact signed decomposition for an arbitrary partial-sum kernel. -/
theorem quotient_kernel_energy_exact (F : ℕ → ℝ) (N k : ℕ) (hk : 0 < k) :
    (k : ℝ) * ((k : ℝ) + 1) *
        (F (N / k) / (k : ℝ) - F (N / (k + 1)) / ((k : ℝ) + 1)) ^ 2 =
      (F (N / k) - F (N / (k + 1))) ^ 2 +
      (F (N / k) - F (N / (k + 1))) ^ 2 / (k : ℝ) +
      2 * ((F (N / k) - F (N / (k + 1))) * F (N / (k + 1)) / (k : ℝ)) +
      F (N / (k + 1)) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- General scalar energy limit, retaining all signed correction terms. -/
theorem quotient_kernel_square_energy_tendsto (F η : ℕ → ℝ)
    (hzero : η 0 = 0)
    (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ))
    (hFbound : ∀ M, |F M| ≤ 1)
    (hFlim : Tendsto F atTop (𝓝 0))
    (hwindow : ∀ N d, 0 < d → F (N / d) - F (N / (d + 1)) =
      ∑ n ∈ window N d, η n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (k : ℝ) * ((k : ℝ) + 1) *
        (F (N / k) / (k : ℝ) - F (N / (k + 1)) / ((k : ℝ) + 1)) ^ 2)
      atTop (𝓝 (∑' n, η n ^ 2)) := by
  let a (N k : ℕ) := F (N / k) - F (N / (k + 1))
  let b (N k : ℕ) := F (N / (k + 1))
  have hb (k : ℕ) (_hk : 0 < k) :
      Tendsto (fun N => b N k) atTop (𝓝 (0 : ℝ)) :=
    hFlim.comp (fixed_div_tendsto (show 0 < k + 1 by omega))
  have ha (k : ℕ) (hk : 0 < k) :
      Tendsto (fun N => a N k) atTop (𝓝 (0 : ℝ)) := by
    have h1 := hFlim.comp (fixed_div_tendsto hk)
    simpa only [a, b, Function.comp_def, sub_zero] using h1.sub (hb k hk)
  have hbb (N k : ℕ) (_hk : 0 < k) : |b N k| ≤ 1 := hFbound _
  have hab (N k : ℕ) (_hk : 0 < k) : |a N k| ≤ 2 := by
    dsimp [a]
    calc
      _ ≤ |F (N / k)| + |F (N / (k + 1))| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (F (N / k)) (-F (N / (k + 1)))
      _ ≤ 2 := by linarith [hFbound (N / k), hFbound (N / (k + 1))]
  have hwlim (d : ℕ) (hd : 0 < d) :
      Tendsto (fun N => ∑ n ∈ window N d, η n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [a, hwindow _ _ hd] using ha d hd
  have hsum (N : ℕ) : (∑ k ∈ Finset.Icc 1 N, a N k ^ 2) =
      ∑ k ∈ Finset.Icc 1 N, (∑ n ∈ window N k, η n) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [a]
    rw [hwindow N k (Finset.mem_Icc.mp hk).1]
  have hA : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, a N k ^ 2)
      atTop (𝓝 (∑' n, η n ^ 2)) := by
    simpa only [hsum] using window_square_energy_tendsto η hzero hη hwlim
  have henergy (N : ℕ) : (∑ k ∈ Finset.Icc 1 N, a N k ^ 2) ≤ 10 := by
    rw [hsum]
    exact sum_window_sq_le_ten η hη N
  have hR := RiemannResearch.Analysis.BoundedSquareEnergy.inverse_linear_square_tendsto_zero
    a ha hab henergy
  have hC := RiemannResearch.Analysis.BoundedSquareEnergy.inverse_linear_mixed_tendsto_zero
    a b hb hbb henergy
  have hB := RiemannResearch.Analysis.BoundedSquareEnergy.pareto_square_tendsto_zero
    b hb hbb
  have he (N : ℕ) : (∑ k ∈ Finset.Icc 1 N,
      (k : ℝ) * ((k : ℝ) + 1) *
        (F (N / k) / (k : ℝ) - F (N / (k + 1)) / ((k : ℝ) + 1)) ^ 2) =
      (∑ k ∈ Finset.Icc 1 N, a N k ^ 2) +
      (∑ k ∈ Finset.Icc 1 N, a N k ^ 2 / (k : ℝ)) +
      2 * (∑ k ∈ Finset.Icc 1 N, a N k * b N k / (k : ℝ)) +
      (∑ k ∈ Finset.Icc 1 N, b N k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact quotient_kernel_energy_exact F N k (Finset.mem_Icc.mp hk).1
  have htotal := ((hA.add hR).add (hC.const_mul 2)).add hB
  simpa only [← he, add_zero, mul_zero] using htotal

/- This body is appended inside RiemannResearch.NumberTheory.QuotientWindow. -/

/-- The homogeneous form permits any common positive coefficient/partial-sum bound. -/
theorem quotient_kernel_square_energy_tendsto_scaled (F η : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C) (hzero : η 0 = 0)
    (hη : ∀ n, 0 < n → |η n| ≤ C / (n : ℝ))
    (hFbound : ∀ M, |F M| ≤ C)
    (hFlim : Tendsto F atTop (𝓝 0))
    (hwindow : ∀ N d, 0 < d → F (N / d) - F (N / (d + 1)) =
      ∑ n ∈ window N d, η n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (k : ℝ) * ((k : ℝ) + 1) *
        (F (N / k) / (k : ℝ) - F (N / (k + 1)) / ((k : ℝ) + 1)) ^ 2)
      atTop (𝓝 (∑' n, η n ^ 2)) := by
  have hC0 : C ≠ 0 := ne_of_gt hC
  have hη' (n : ℕ) (hn : 0 < n) : |η n / C| ≤ 1 / (n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    rw [abs_div, abs_of_pos hC]
    calc
      _ ≤ (C / (n : ℝ)) / C := div_le_div_of_nonneg_right (hη n hn) (le_of_lt hC)
      _ = 1 / (n : ℝ) := by field_simp
  have hF' (M : ℕ) : |F M / C| ≤ 1 := by
    rw [abs_div, abs_of_pos hC]
    exact (div_le_iff₀ hC).mpr (by simpa only [one_mul] using hFbound M)
  have hlim' : Tendsto (fun M => F M / C) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hFlim.div_const C
  have hwindow' (N d : ℕ) (hd : 0 < d) :
      F (N / d) / C - F (N / (d + 1)) / C = ∑ n ∈ window N d, η n / C := by
    rw [← Finset.sum_div, ← hwindow N d hd]
    ring
  have ht := quotient_kernel_square_energy_tendsto
    (fun M => F M / C) (fun n => η n / C)
    (by simp only [hzero, zero_div]) hη' hF' hlim' hwindow'
  have hsum : C ^ 2 * (∑' n, (η n / C) ^ 2) = ∑' n, η n ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    field_simp
  have he (N : ℕ) : C ^ 2 * (∑ k ∈ Finset.Icc 1 N,
      (k : ℝ) * ((k : ℝ) + 1) *
        ((F (N / k) / C) / (k : ℝ) - (F (N / (k + 1)) / C) / ((k : ℝ) + 1)) ^ 2) =
      ∑ k ∈ Finset.Icc 1 N,
        (k : ℝ) * ((k : ℝ) + 1) *
          (F (N / k) / (k : ℝ) - F (N / (k + 1)) / ((k : ℝ) + 1)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Finset.mem_Icc.mp hk).1
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring
  have hscaled : Tendsto (fun N : ℕ => C ^ 2 * (∑ k ∈ Finset.Icc 1 N,
      (k : ℝ) * ((k : ℝ) + 1) *
        ((F (N / k) / C) / (k : ℝ) -
          (F (N / (k + 1)) / C) / ((k : ℝ) + 1)) ^ 2))
      atTop (𝓝 (C ^ 2 * (∑' n, (η n / C) ^ 2))) := ht.const_mul (C ^ 2)
  rw [hsum] at hscaled
  exact hscaled.congr' (Eventually.of_forall he)

end RiemannResearch.NumberTheory.QuotientWindow
