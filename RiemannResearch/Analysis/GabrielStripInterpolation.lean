import RiemannResearch.Analysis.GabrielFiniteInterpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Gabriel interpolation for continuous vertical moments at exponents 4/3 and 2

Chourasiya and Simonič, https://arxiv.org/html/2507.15184v2, equations (19)--(21).
Finite-family analytic interpolation is applied to a common uniform grid.
Uniform continuity controls its quadrature error simultaneously under every
vertical translation. This allows uniform boundary window estimates to be
used in the Hadamard three-lines argument.
-/
noncomputable section
open Set Complex Complex.HadamardThreeLines MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.InghamInterpolation

private theorem weighted_finite_gabriel {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hhol : ∀ j ∈ s, DiffContOnCl ℂ (f j) (verticalStrip 0 1))
    (hbd : ∀ j ∈ s, ∃ B : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖f j z‖ ≤ B)
    {w A B : ℝ} (hw : 0 < w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : ∀ z : ℂ, z.re = 0 → (w * ∑ j ∈ s, ‖f j z‖^(4/3:ℝ))^(3/4:ℝ) ≤ A)
    (hR : ∀ z : ℂ, z.re = 1 → (w * ∑ j ∈ s, ‖f j z‖^(2:ℝ))^(1/2:ℝ) ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    (w * ∑ j ∈ s, ‖f j (θ:ℂ)‖ ^ (4/(3-θ)))^((3-θ)/4) ≤ A^(1-θ)*B^θ := by
  have hnorm (k : ℝ) (p r : ℝ) (M : ℝ)
      (H : ∀ z : ℂ, z.re = k → (w*∑ j ∈ s, ‖f j z‖ ^ p)^r ≤ M) :
      ∀ z : ℂ, z.re = k → (∑ j ∈ s, ‖f j z‖ ^ p)^r ≤ M / w^r := by
    intro z hz
    have hh := H z hz
    rw [Real.mul_rpow hw.le (Finset.sum_nonneg
      (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))] at hh
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hw _)).mpr (by simpa [mul_comm] using hh)
  have H := finite_gabriel_interpolation s f hhol hbd
    (hnorm 0 (4/3) (3/4) A hL) (hnorm 1 2 (1/2) B hR) hθ
  rw [Real.mul_rpow hw.le (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))]
  apply (mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hw.le _)).trans_eq
  rw [Real.div_rpow hA (Real.rpow_nonneg hw.le _), Real.div_rpow hB (Real.rpow_nonneg hw.le _),
    ← Real.rpow_mul hw.le, ← Real.rpow_mul hw.le, div_mul_div_comm, ← Real.rpow_add hw]
  have he : (3/4:ℝ)*(1-θ)+(1/2)*θ = (3-θ)/4 := by ring
  rw [he]
  field_simp [(Real.rpow_pos_of_pos hw ((3-θ)/4)).ne']

/-- Uniform Riemann sum error for every translate of a grid. -/
theorem gaussian_grid_error {g : ℝ → ℝ} (hg : Continuous g) {h e : ℝ} (hh : 0 ≤ h)
    (hosc : ∀ x y : ℝ, |x-y| ≤ h → |g x-g y| ≤ e) (x : ℝ) (N : ℕ) :
    |h * (∑ j ∈ Finset.range N, g (x+j*h)) - ∫ t in x..x+N*h, g t| ≤ N*h*e := by
  let p (j : ℕ) := x+j*h
  have hstep (j : ℕ) : p (j+1) = p j + h := by dsimp [p]; push_cast; ring
  have hcell (j : ℕ) :
      |h*g (p j) - ∫ t in p j..p (j+1), g t| ≤ e*h := by
    have hj : p j ≤ p (j+1) := by rw [hstep]; linarith
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := p j) (b := p (j+1))
      (f := fun t : ℝ => g (p j)-g t) (C := e) (by
        intro t ht
        rw [uIoc_of_le hj] at ht
        apply hosc
        rw [abs_of_nonpos (by linarith [ht.1])]
        linarith [ht.2,hstep j])
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hg.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
      show p (j+1)-p j=h by rw [hstep]; ring, abs_of_nonneg hh] at H
    exact H
  have hadd := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := p) (n := N)
    (fun j _ => hg.intervalIntegrable (p j) (p (j+1)))
  change |h * (∑ j ∈ Finset.range N, g (p j)) - ∫ t in x..p N, g t| ≤ _
  rw [show x=p 0 by simp [p], ← hadd, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ j ∈ Finset.range N, |h*g (p j) - ∫ t in p j..p (j+1), g t| :=
          Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _j ∈ Finset.range N, e*h := Finset.sum_le_sum (fun j _ => hcell j)
       _ = _ := by simp; ring

private theorem slice_eq (z : ℂ) (k t : ℝ) (hz : z.re = k) :
    z+(t:ℂ)*I = (k:ℂ)+((z.im+t:ℝ):ℂ)*I := by
  apply Complex.ext <;> simp [hz]



/-- Moment density of a vertical trace on the normalized closed strip. -/
def stripMomentDensity (F : ℂ → ℂ) (x p t : ℝ) : ℝ := ‖F ((x:ℂ)+(t:ℂ)*I)‖^p

private theorem modulus_for_grid {g : ℝ → ℝ} (hg : UniformContinuous g)
    {e : ℝ} (he : 0 < e) : ∃ d > 0, ∀ x y : ℝ, |x-y| < d → |g x-g y| ≤ e := by
  obtain ⟨d,hd,hg'⟩ := Metric.uniformContinuous_iff.mp hg e he
  refine ⟨d,hd,?_⟩
  intro x y hxy
  have hxy' : dist x y < d := by simpa [Real.dist_eq] using hxy
  simpa only [Real.dist_eq] using (hg' hxy').le

/-- Continuous mixed-norm interpolation for every finite observation window.
The input boundary moment inequalities hold on all translations of the same
window. In particular they follow from the full vertical boundary integrals.
The reciprocal power on the interior line is exactly `(3-θ)/4`. -/
theorem gabriel_vertical_window {F : ℂ → ℂ}
    (hhol : DiffContOnCl ℂ F (verticalStrip 0 1))
    (hbd : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ C)
    {θ L ML MR : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) (hL : 0 < L)
    (hML : 0 ≤ ML) (hMR : 0 ≤ MR)
    (hu0 : UniformContinuous (stripMomentDensity F 0 (4/3)))
    (hu1 : UniformContinuous (stripMomentDensity F 1 2))
    (hut : UniformContinuous (stripMomentDensity F θ (4/(3-θ))))
    (hleft : ∀ y : ℝ, ∫ t in y..y+L, stripMomentDensity F 0 (4/3) t ≤ ML)
    (hright : ∀ y : ℝ, ∫ t in y..y+L, stripMomentDensity F 1 2 t ≤ MR) (x : ℝ) :
    (∫ t in x..x+L, stripMomentDensity F θ (4/(3-θ)) t)^((3-θ)/4) ≤
      (ML^(3/4:ℝ))^(1-θ)*(MR^(1/2:ℝ))^θ := by
  classical
  let Q := ∫ t in x..x+L, stripMomentDensity F θ (4/(3-θ)) t
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg (by linarith)
    (fun t _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hden : 0 < 3-θ := by linarith [hθ.2]
  have hwa : 0 ≤ 1-θ := by linarith [hθ.2]
  have approx (e : ℝ) (he : 0 < e) :
      (max 0 (Q-L*e))^((3-θ)/4) ≤ ((ML+L*e)^(3/4:ℝ))^(1-θ)*
        ((MR+L*e)^(1/2:ℝ))^θ := by
    obtain ⟨d0,hd0,hg0⟩ := modulus_for_grid hu0 he
    obtain ⟨d1,hd1,hg1⟩ := modulus_for_grid hu1 he
    obtain ⟨dt,hdt,hgt⟩ := modulus_for_grid hut he
    let d := min d0 (min d1 dt)
    have hd : 0 < d := lt_min hd0 (lt_min hd1 hdt)
    obtain ⟨N,hN⟩ := exists_nat_gt (L/d)
    have hN0 : 0 < (N:ℝ) := (div_pos hL hd).trans hN
    let h := L / (N:ℝ)
    have hh : 0 < h := div_pos hL hN0
    have hNd : (N:ℝ)*h=L := by dsimp [h]; field_simp
    have hsmall : h < d := (div_lt_iff₀ hN0).mpr (by
      have := (div_lt_iff₀ hd).mp hN
      linarith [mul_comm (N:ℝ) d])
    let t (j : ℕ) : ℝ := x+j*h
    let f (j : ℕ) (z : ℂ) := F (z+(t j:ℂ)*I)
    have hfj (j : ℕ) : DiffContOnCl ℂ (f j) (verticalStrip 0 1) := by
      apply hhol.comp (differentiable_id.add_const _).diffContOnCl
      intro z hz
      simpa [verticalStrip] using hz
    obtain ⟨C,hC⟩ := hbd
    have hbound (j : ℕ) : ∃ D : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖f j z‖ ≤ D := by
      refine ⟨C,fun z hz => hC _ ?_⟩
      simpa [verticalClosedStrip] using hz
    have grid (k p M : ℝ) (hg : Continuous (stripMomentDensity F k p))
        (ho : ∀ y v : ℝ, |y-v| ≤ h →
          |stripMomentDensity F k p y-stripMomentDensity F k p v| ≤ e)
        (hm : ∀ y : ℝ, ∫ u in y..y+L, stripMomentDensity F k p u ≤ M) :
        ∀ z : ℂ, z.re=k →
          h * ∑ j ∈ Finset.range N, ‖f j z‖^p ≤ M+L*e := by
      intro z hz
      have herr := gaussian_grid_error hg hh.le ho (z.im+x) N
      rw [hNd] at herr
      have hsum : (∑ j ∈ Finset.range N, ‖f j z‖^p) =
          ∑ j ∈ Finset.range N, stripMomentDensity F k p (z.im+x+j*h) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [f, t, stripMomentDensity]
        rw [slice_eq z k _ hz, add_assoc z.im x]
      rw [hsum]
      have H := (le_abs_self _).trans herr
      linarith [hm (z.im+x)]
    have H0 := grid 0 (4/3) ML hu0.continuous (fun y v hy => hg0 y v
      ((hy.trans_lt hsmall).trans_le (min_le_left _ _))) hleft
    have H1 := grid 1 2 MR hu1.continuous (fun y v hy => hg1 y v
      ((hy.trans_lt hsmall).trans_le ((min_le_right _ _).trans (min_le_left _ _)))) hright
    have hi := gaussian_grid_error hut.continuous hh.le (fun y v hy => hgt y v
      ((hy.trans_lt hsmall).trans_le ((min_le_right _ _).trans (min_le_right _ _)))) x N
    rw [hNd] at hi
    let V := h*∑ j ∈ Finset.range N, ‖f j (θ:ℂ)‖^(4/(3-θ))
    have hV0 : 0 ≤ V := mul_nonneg hh.le (Finset.sum_nonneg
      (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))
    have htQ : Q-L*e ≤ V := by
      change |V-Q| ≤ L*e at hi
      linarith [(abs_le.mp hi).1]
    have H := weighted_finite_gabriel (Finset.range N) f (fun j _ => hfj j)
      (fun j _ => hbound j) hh
      (Real.rpow_nonneg (show 0 ≤ ML+L*e by positivity) (3/4:ℝ))
      (Real.rpow_nonneg (show 0 ≤ MR+L*e by positivity) (1/2:ℝ))
      (fun z hz => Real.rpow_le_rpow (mul_nonneg hh.le (Finset.sum_nonneg
        (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))) (H0 z hz) (by norm_num))
      (fun z hz => Real.rpow_le_rpow (mul_nonneg hh.le (Finset.sum_nonneg
        (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))) (H1 z hz) (by norm_num)) hθ
    exact (Real.rpow_le_rpow (le_max_left _ _) (max_le hV0 htQ) (by positivity)).trans H
  have hcL : Continuous (fun e : ℝ => (max 0 (Q-L*e))^((3-θ)/4)) := by
    fun_prop (disch := positivity)
  have hcR : Continuous (fun e : ℝ => ((ML+L*e)^(3/4:ℝ))^(1-θ)*((MR+L*e)^(1/2:ℝ))^θ) := by
    have := hθ.1
    fun_prop (disch := positivity)
  have hfinal := le_of_tendsto_of_tendsto
    ((hcL.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))
    ((hcR.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun e he => approx e he)
  simpa [max_eq_right hQ, Q] using hfinal

end RiemannResearch.Analysis.InghamInterpolation
