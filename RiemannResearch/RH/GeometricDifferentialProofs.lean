import RiemannResearch.RH.GeometricDifferentialResearchTargets
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric covariance derivative

Proves the actual derivative and absolute summability in
`GeometricCovarianceDerivativeTarget` by locally uniform differentiation of
geometric series and exact first-moment centering.
-/
namespace RiemannResearch.RH.Pareto
noncomputable section
open scoped BigOperators

private theorem geometricProbability_nat_hasSum {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasSum (fun n : ℕ => geometricProbability n t * (n : ℝ)) (t / (1-t)) := by
  have ht : ‖t‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos ht0] using ht1
  have hne : 1-t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  convert! (hasSum_coe_mul_geometric_of_norm_lt_one ht).mul_left (1-t) using 1
  · funext n
    simp only [geometricProbability]
    ring
  · field_simp [hne]

private theorem bounded_geometric_nat_summable {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (fun n : ℕ => f n * geometricProbability n t * (n : ℝ)) := by
  have hp (n : ℕ) : 0 ≤ geometricProbability n t :=
    geometricProbability_nonneg n ⟨ht0.le, ht1.le⟩
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) ((geometricProbability_nat_hasSum ht0 ht1).summable.mul_left C)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp n),
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  calc
    |f n| * geometricProbability n t * (n : ℝ) ≤
        C * geometricProbability n t * (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hf n) (hp n)) (Nat.cast_nonneg n)
    _ = _ := by ring

private theorem geometricTransform_hasDerivAt_series {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (geometricTransform f)
      (∑' n : ℕ, f n * (-(t^n) + (1-t) * ((n : ℝ) * t^(n-1)))) t := by
  let r : ℝ := (t+1)/2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have htr : t < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hf 0)
  let g : ℕ → ℝ → ℝ := fun n x => f n * geometricProbability n x
  let d : ℕ → ℝ → ℝ := fun n x =>
    f n * (-(x^n) + (1-x) * ((n : ℝ) * x^(n-1)))
  let u : ℕ → ℝ := fun n => C * (r^n + (n : ℝ)*r^(n-1))
  have hslope : Summable (fun n : ℕ => (n : ℝ) * r^(n-1)) := by
    have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable.mul_right r⁻¹
    apply hs.congr
    intro n
    cases n with
    | zero => simp
    | succ n => simp [pow_succ, mul_assoc, ne_of_gt hr0]
  have hu : Summable u :=
    ((hasSum_geometric_of_norm_lt_one hrnorm).summable.add hslope).mul_left C
  have hd (n : ℕ) (x : ℝ) (_hx : x ∈ Set.Ioo 0 r) :
      HasDerivAt (g n) (d n x) x := by
    convert! (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul
      ((hasDerivAt_id x).pow n)).const_mul (f n) using 1 <;>
      simp [g, d, geometricProbability]
  have hbound (n : ℕ) (x : ℝ) (hx : x ∈ Set.Ioo 0 r) : ‖d n x‖ ≤ u n := by
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2.le.trans hr1.le
    have hxpow : x^n ≤ r^n := pow_le_pow_left₀ hx0 hx.2.le n
    have hxpred : x^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ hx0 hx.2.le (n-1)
    have hprod : (1-x) * ((n : ℝ)*x^(n-1)) ≤ (n : ℝ)*r^(n-1) := by
      calc
        _ ≤ 1 * ((n : ℝ)*x^(n-1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (n : ℝ)*r^(n-1) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_left hxpred (Nat.cast_nonneg n)
    calc
      ‖d n x‖ = |f n| * ‖-(x^n) + (1-x) * ((n : ℝ)*x^(n-1))‖ := by
        simp [d, norm_mul, Real.norm_eq_abs]
      _ ≤ C * ‖-(x^n) + (1-x) * ((n : ℝ)*x^(n-1))‖ :=
        mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)
      _ ≤ C * (‖-(x^n)‖ + ‖(1-x) * ((n : ℝ)*x^(n-1))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hC
      _ = C * (x^n + (1-x)*((n : ℝ)*x^(n-1))) := by
        rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx0 n),
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ u n := mul_le_mul_of_nonneg_left (add_le_add hxpow hprod) hC
  have hs := (geometricTransform_norm_summable hf ⟨ht0.le, ht1⟩).of_norm
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (0 : ℝ) r).isPreconnected hd hbound ⟨ht0,htr⟩ hs ⟨ht0,htr⟩

/-- Complete centered covariance identity, with absolute summability and an actual derivative. -/
theorem geometricCovarianceDerivativeTarget_proved : GeometricCovarianceDerivativeTarget := by
  intro f hbounded t ht0 ht1
  obtain ⟨C,hf⟩ := hbounded
  have htne : t ≠ 0 := ne_of_gt ht0
  have hone : 1-t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  let p : ℕ → ℝ := fun n => geometricProbability n t
  let μ : ℝ := t/(1-t)
  let m : ℝ := geometricTransform f t
  let s : ℕ → ℝ := fun n => p n*((n : ℝ)-μ)
  have hp : HasSum p 1 := geometricProbability_hasSum ⟨ht0.le,ht1⟩
  have hpn : HasSum (fun n => p n*(n : ℝ)) μ := geometricProbability_nat_hasSum ht0 ht1
  have hs : HasSum s 0 := by
    convert! hpn.sub (hp.mul_right μ) using 1
    · funext n
      dsimp [s]
      ring
    · ring
  have hfp : Summable (fun n => f n*p n) :=
    (geometricTransform_norm_summable hf ⟨ht0.le,ht1⟩).of_norm
  have hfn : Summable (fun n => f n*p n*(n : ℝ)) :=
    bounded_geometric_nat_summable hf ht0 ht1
  have hfs : Summable (fun n => f n*s n) := by
    convert! hfn.sub (hfp.mul_right μ) using 1
    funext n
    dsimp [s]
    ring
  have hcov : Summable (fun n => p n*(f n-m)*((n : ℝ)-μ)) := by
    convert! hfs.sub (hs.summable.mul_left m) using 1
    funext n
    dsimp [s]
    ring
  refine ⟨hcov, ?_⟩
  have hcovsum : (∑' n, p n*(f n-m)*((n : ℝ)-μ)) = ∑' n, f n*s n := by
    calc
      _ = ∑' n, (f n*s n - m*s n) := by
        apply tsum_congr
        intro n
        dsimp [s]
        ring
      _ = (∑' n, f n*s n) - m * (∑' n, s n) := by
        rw [hfs.tsum_sub (hs.summable.mul_left m), tsum_mul_left]
      _ = _ := by rw [hs.tsum_eq]; ring
  have hterm (n : ℕ) :
      f n * (-(t^n)+(1-t)*((n : ℝ)*t^(n-1))) = (f n*s n)/t := by
    dsimp [s,p,μ,geometricProbability]
    cases n with
    | zero => simp; field_simp [htne, hone]
    | succ n => simp only [Nat.succ_sub_one,pow_succ]; field_simp [htne, hone]; ring
  rw [(geometricTransform_hasDerivAt_series hf ht0 ht1).deriv]
  change (∑' n, f n * (-(t^n)+(1-t)*((n : ℝ)*t^(n-1)))) =
    (∑' n, p n*(f n-m)*((n : ℝ)-μ))/t
  simp_rw [hterm]
  rw [hcovsum, tsum_div_const]

end
end RiemannResearch.RH.Pareto
