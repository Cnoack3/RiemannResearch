import RiemannResearch.Probability.ContinuousProjectionCompression
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A vanishing trace forces positive spectral determinants to converge to one

The dimension can vary without bound. The disk estimate also applies after
rescaling, with the trace of the rescaled matrix. This addresses the determinant
normalization in the 13 October 2026 CRT carry and zeta trace note.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ComplexOrder
namespace RiemannResearch.Analysis.VanishingTraceDeterminant

private theorem product_bound {ι : Type*} (s : Finset ι) (w : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + w i)) - 1‖ ≤ Real.exp (∑ i ∈ s, ‖w i‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Real.exp_add]
    let P := ∏ i ∈ s, (1 + w i)
    let E := Real.exp (∑ i ∈ s, ‖w i‖)
    change ‖P - 1‖ ≤ E - 1 at ih
    have hP : ‖P‖ ≤ E := by
      have h := norm_add_le (P - 1) 1
      rw [sub_add_cancel, norm_one] at h
      linarith
    have hsplit : (1 + w j) * P - 1 = (P - 1) + w j * P := by ring
    change ‖(1 + w j) * P - 1‖ ≤ Real.exp ‖w j‖ * E - 1
    rw [hsplit]
    have hE : 0 ≤ E := (Real.exp_pos _).le
    calc
      _ ≤ ‖P - 1‖ + ‖w j‖ * ‖P‖ := by simpa only [norm_mul] using norm_add_le (P - 1) (w j * P)
      _ ≤ (E - 1) + ‖w j‖ * E := add_le_add ih (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right (Real.add_one_le_exp ‖w j‖) hE]

theorem eigenvalue_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (i : ι) :
    hA.isHermitian.eigenvalues i ≤ A.trace.re := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  simpa using (Finset.single_le_sum
    (f := hA.isHermitian.eigenvalues) (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i))

theorem det_le_mean_trace_pow {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    A.det.re ≤ (A.trace.re / Fintype.card ι) ^ Fintype.card ι := by
  let l := hA.isHermitian.eigenvalues
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : 0 < ∑ _ : ι, (1 : ℝ) := by simpa using hc
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : ι => (1 : ℝ)) l
    (fun _ _ => zero_le_one) hsum (fun i _ => hA.eigenvalues_nonneg i)
  have ham : (∏ i, l i) ^ (Fintype.card ι : ℝ)⁻¹ ≤ (∑ i, l i) / Fintype.card ι := by
    simpa using h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg
    (Finset.prod_nonneg (fun i _ => hA.eigenvalues_nonneg i)) _) ham (Fintype.card ι)
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hA.eigenvalues_nonneg i))
    (ne_of_gt Fintype.card_pos)] at hpow
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  change (∏ i, (l i : ℂ)).re ≤ ((∑ i, (l i : ℂ)).re / Fintype.card ι) ^ Fintype.card ι
  rw [← Complex.ofReal_prod, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.ofReal_re]
  exact hpow

/-- A rank-independent estimate for the actual matrix determinant on a complex disk. -/
theorem det_disk_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (z : ℂ) {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖(1 - z ^ 2 • A).det - 1‖ ≤ Real.exp (R ^ 2 * A.trace.re) - 1 := by
  classical
  have htr : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have ht : 0 ≤ A.trace.re := htr ▸ Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i)
  rw [show 1 - z ^ 2 • A = 1 + (-(z ^ 2)) • A by rw [neg_smul, sub_eq_add_neg],
    hA.isHermitian.det_one_add_smul_eq_prod_complex]
  apply (product_bound Finset.univ (fun i => -(z ^ 2) * (hA.isHermitian.eigenvalues i : ℂ))).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    _ = ‖z‖ ^ 2 * A.trace.re := by
      rw [htr, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [norm_mul, norm_neg, norm_pow, Complex.norm_of_nonneg (hA.eigenvalues_nonneg i)])
    _ ≤ _ := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg z) ((norm_nonneg z).trans hz)).mpr hz) ht

/-- Uniform on each disk, even as the number of eigenvalues grows. -/
theorem det_tendstoUniformlyOn_disk {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (ht : Tendsto (fun n => (A n).trace.re) atTop (𝓝 0)) (R : ℝ) :
    TendstoUniformlyOn (fun n z => (1 - z ^ 2 • A n).det) (fun _ => (1 : ℂ))
      atTop {z : ℂ | ‖z‖ ≤ R} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun n => Real.exp (R ^ 2 * (A n).trace.re) - 1) atTop (𝓝 0) := by
    simpa using ((Real.continuous_exp.continuousAt.tendsto.comp (ht.const_mul (R ^ 2))).sub_const 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  simpa only [dist_comm (1 : ℂ), dist_eq_norm] using (det_disk_bound (hA n) z hz).trans_lt hn

/-- Any pointwise candidate at any complex argument must have value one. -/
theorem limit_eq_one {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (ht : Tendsto (fun n => (A n).trace.re) atTop (𝓝 0)) (z F : ℂ)
    (hF : Tendsto (fun n => (1 - z ^ 2 • A n).det) atTop (𝓝 F)) : F = 1 :=
  tendsto_nhds_unique hF ((det_tendstoUniformlyOn_disk A hA ht ‖z‖).tendsto_at (le_refl ‖z‖))

end RiemannResearch.Analysis.VanishingTraceDeterminant
