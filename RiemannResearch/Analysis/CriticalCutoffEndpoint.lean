import RiemannResearch.Analysis.CriticalCutoffGrowth

/-!
# Quantitative critical-cutoff inequalities

Source: elementary optimization of the critical Mellin cutoff already proved in
`RH/ParetoCriticalMellinCutoff`. These scalar refinements are derived here from
explicit inequalities; the RH consumer is `RH/ProjectedDualMassEndpoint`.

A nonzero critical boundary value yields a logarithmic error/mass tradeoff and
an eventual endpoint lower bound with quadratic profile loss. No arithmetic or
zeta-zero existence input is hidden in these scalar statements.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- A critical boundary value forces an eventual endpoint lower bound, including
the quadratic loss in the cutoff profile. All analytic inputs are explicit. -/
theorem mass_endpoint_lower_bound_of_critical_cutoff
    (φ B Q : ℕ → ℝ) (hφ : Tendsto φ atTop atTop)
    (hB : ∀ n, 0 ≤ B n) (hQ : ∀ n, 0 ≤ Q n)
    (a C D L : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 < L)
    (herror : ∀ᶠ n : ℕ in atTop, Q n ^ 4 ≤ C * B n ^ 2 * Real.exp (-a * φ n))
    (hcut : ∀ n : ℕ, ∀ R : ℝ, 0 < R →
      L ≤ Q n * Real.sqrt R + 2 * (D + B n) * Real.exp (-R / 2)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      κ ≤ φ n ^ 2 * (Real.exp (-a * φ n) * B n ^ 2) := by
  let c : ℝ := a + 1
  have hc : 0 < c := by dsimp [c]; linarith
  let κ : ℝ := min 1 (L ^ 4 / (32 * (C + 1) * c ^ 2))
  have hden : 0 < 32 * (C + 1) * c ^ 2 := by positivity
  have hk : 0 < κ := by
    exact lt_min (by norm_num) (div_pos (pow_pos hL 4) hden)
  have hk1 : κ ≤ 1 := min_le_left _ _
  have hkbound : C * c ^ 2 * κ ≤ L ^ 4 / 32 := by
    have hfrac : κ ≤ L ^ 4 / (32 * (C + 1) * c ^ 2) := min_le_right _ _
    have hh := (le_div_iff₀ hden).mp hfrac
    have hmono : C * c ^ 2 * κ ≤ (C + 1) * c ^ 2 * κ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (sq_nonneg c)) hk.le
    nlinarith
  have he1 : Tendsto (fun n => Real.exp (-c * φ n)) atTop (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr
      (hφ.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have he2 : Tendsto (fun n => Real.exp (-φ n)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_comp_nhds_zero.mpr
      (hφ.const_mul_atTop_of_neg (by norm_num : (-1 : ℝ) < 0))
    simpa only [neg_one_mul] using ht
  have hu : Tendsto
      (fun n => 8 * D ^ 2 * Real.exp (-c * φ n) + 8 * Real.exp (-φ n))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (he1.const_mul (8 * D ^ 2)).add (he2.const_mul 8)
  refine ⟨κ, hk, ?_⟩
  filter_upwards [herror, hφ.eventually_ge_atTop 1,
    hu.eventually_lt_const (by positivity : (0 : ℝ) < (L / 2) ^ 2)] with n hn hpn hun
  by_contra hnlow
  have hf : φ n ^ 2 * (Real.exp (-a * φ n) * B n ^ 2) < κ := lt_of_not_ge hnlow
  let Z : ℝ := Real.exp (-a * φ n) * B n ^ 2
  have hZ : 0 ≤ Z := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hp2 : 1 ≤ φ n ^ 2 := by nlinarith
  have hZle : Z ≤ 1 := by
    have hmono : Z ≤ φ n ^ 2 * Z := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp2 hZ
    exact hmono.trans (hf.le.trans hk1)
  have hexp : Real.exp (-c * φ n) =
      Real.exp (-a * φ n) * Real.exp (-φ n) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  have hbtail : B n ^ 2 * Real.exp (-c * φ n) ≤ Real.exp (-φ n) := by
    calc
      _ = Z * Real.exp (-φ n) := by rw [hexp]; dsimp [Z]; ring
      _ ≤ 1 * Real.exp (-φ n) :=
        mul_le_mul_of_nonneg_right hZle (Real.exp_pos _).le
      _ = _ := one_mul _
  let T : ℝ := 2 * (D + B n) * Real.exp (-(c * φ n) / 2)
  have hT : 0 ≤ T :=
    mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hD (hB n)))
      (Real.exp_pos _).le
  have hexpsq : Real.exp (-(c * φ n) / 2) ^ 2 = Real.exp (-c * φ n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hTbound : T ^ 2 ≤
      8 * D ^ 2 * Real.exp (-c * φ n) + 8 * Real.exp (-φ n) := by
    have hsum : (D + B n) ^ 2 ≤ 2 * D ^ 2 + 2 * B n ^ 2 := by
      nlinarith [sq_nonneg (D - B n)]
    have hh := mul_le_mul_of_nonneg_right hsum (Real.exp_pos (-c * φ n)).le
    dsimp [T]
    rw [mul_pow, mul_pow, hexpsq]
    nlinarith
  have hTsmall : T < L / 2 := by
    have hh : T ^ 2 < (L / 2) ^ 2 := hTbound.trans_lt hun
    nlinarith
  have hR : 0 < c * φ n := mul_pos hc (by linarith)
  let H : ℝ := Q n * Real.sqrt (c * φ n)
  have hH : 0 ≤ H := mul_nonneg (hQ _) (Real.sqrt_nonneg _)
  have hHlarge : L / 2 < H := by
    have hh := hcut n (c * φ n) hR
    change L ≤ H + T at hh
    linarith
  have hH2 : (L / 2) ^ 2 < H ^ 2 :=
    (sq_lt_sq₀ (by linarith : 0 ≤ L / 2) hH).mpr hHlarge
  have hH4 : L ^ 4 / 16 < H ^ 4 := by
    have hh := (sq_lt_sq₀ (sq_nonneg (L / 2)) (sq_nonneg H)).mpr hH2
    nlinarith only [hh]
  have hsqrt : (Real.sqrt (c * φ n)) ^ 4 = (c * φ n) ^ 2 := by
    calc
      _ = ((Real.sqrt (c * φ n)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hR.le]
  have hHupper : H ^ 4 ≤ C * c ^ 2 * (φ n ^ 2 * Z) := by
    dsimp only [H]
    rw [mul_pow, hsqrt]
    calc
      _ ≤ (C * B n ^ 2 * Real.exp (-a * φ n)) * (c * φ n) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by dsimp [Z]; ring
  have hHupper' : H ^ 4 ≤ C * c ^ 2 * κ := hHupper.trans
    (mul_le_mul_of_nonneg_left hf.le (mul_nonneg hC (sq_nonneg c)))
  have hL4 : 0 < L ^ 4 := pow_pos hL 4
  linarith

/-- The endpoint lower bound recovers divergence at every strict exponent,
without any further cutoff or sign assumptions. -/
theorem mass_strict_growth_of_endpoint_lower_bound
    (φ B : ℕ → ℝ) (hφ : Tendsto φ atTop atTop)
    {a κ : ℝ} (hκ : 0 < κ)
    (hbound : ∀ᶠ n : ℕ in atTop,
      κ ≤ φ n ^ 2 * (Real.exp (-a * φ n) * B n ^ 2))
    (b : ℝ) (hba : b < a) :
    Tendsto (fun n => Real.exp (-b * φ n) * B n ^ 2) atTop atTop := by
  have hpoly : Tendsto (fun n => φ n ^ 2 * Real.exp (-(a-b)*φ n))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (2:ℝ) (a-b) (by linarith)).comp hφ
    simpa only [Function.comp_def, Real.rpow_two] using h
  apply tendsto_atTop.mpr
  intro K
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (φ n ^ 2 * Real.exp (-(a-b)*φ n)) * K < κ := by
    have h := hpoly.mul_const K
    simp only [zero_mul] at h
    exact h.eventually_lt_const hκ
  filter_upwards [hbound, hsmall] with n hn hsmalln
  by_contra hnot
  have hle : Real.exp (-b * φ n) * B n ^ 2 ≤ K := (lt_of_not_ge hnot).le
  have hprod := mul_le_mul_of_nonneg_left hle
    (mul_nonneg (sq_nonneg (φ n)) (Real.exp_pos (-(a-b)*φ n)).le)
  have hid : (φ n ^ 2 * Real.exp (-(a-b)*φ n)) *
      (Real.exp (-b * φ n) * B n ^ 2) =
      φ n ^ 2 * (Real.exp (-a * φ n) * B n ^ 2) := by
    rw [show -a*φ n = -(a-b)*φ n + -b*φ n by ring, Real.exp_add]
    ring
  rw [hid] at hprod
  linarith

/-- A nonzero critical Mellin value imposes a quantitative tradeoff between
Hilbert error and pointwise amplitude. No arithmetic-energy estimate is used. -/
theorem critical_cutoff_logarithmic_tradeoff
    (B Q D L : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hL : 0 < L)
    (hcut : ∀ R : ℝ, 0 < R →
      L ≤ Q * Real.sqrt R + 2 * (D + B) * Real.exp (-R / 2)) :
    L ^ 2 / 8 ≤ Q ^ 2 * Real.log (4 * (D + B + L) / L) := by
  let S : ℝ := D + B + L
  have hS : 0 < S := by dsimp [S]; linarith
  let z : ℝ := 4 * S / L
  have hz : 1 < z := by
    apply (lt_div_iff₀ hL).mpr
    dsimp [S]
    linarith
  have hz0 : 0 < z := zero_lt_one.trans hz
  let R : ℝ := 2 * Real.log z
  have hR : 0 < R := mul_pos (by norm_num) (Real.log_pos hz)
  have hexp : Real.exp (-R / 2) = L / (4 * S) := by
    calc
      _ = (Real.exp (Real.log z))⁻¹ := by
        dsimp [R]
        rw [show -(2 * Real.log z) / 2 = -Real.log z by ring, Real.exp_neg]
      _ = z⁻¹ := by rw [Real.exp_log hz0]
      _ = _ := by dsimp [z]; rw [inv_div]
  have htail : 2 * (D + B) * Real.exp (-R / 2) ≤ L / 2 := by
    rw [hexp, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 4 * S)).mpr
    dsimp [S]
    nlinarith [sq_nonneg L]
  have hhead : L / 2 ≤ Q * Real.sqrt R := by
    have hh := hcut R hR
    linarith
  have hsq : (L / 2) ^ 2 ≤ (Q * Real.sqrt R) ^ 2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ L / 2)
      (mul_nonneg hQ (Real.sqrt_nonneg R))).mpr hhead
  rw [mul_pow, Real.sq_sqrt hR.le] at hsq
  change L ^ 2 / 8 ≤ Q ^ 2 * Real.log z
  dsimp [R] at hsq
  nlinarith only [hsq]

end RiemannResearch.Analysis
