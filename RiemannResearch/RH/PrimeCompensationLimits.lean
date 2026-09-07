import RiemannResearch.RH.SignedWeilCorrelation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convergent remainder measures in exact prime-square compensation

Source: user-provided argument,
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`, §6.
The results here concern actual arithmetic/gamma weights. They do not assume
their moment integrability, or assume a full Weil value to be zero.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimeCompensationLimits

/-- The kernel in the displacement-energy version of the Weil formula. -/
noncomputable def displacementKernel (t : ℝ) : ℝ :=
  Real.exp (-t / 2) / (1 - Real.exp (-2 * t))

theorem displacementKernel_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ displacementKernel t := by
  apply div_nonneg (Real.exp_pos _).le
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))

/-- The displayed displacement kernel is exactly the existing gamma kernel. -/
theorem displacementKernel_eq_weilGammaKernel (t : ℝ) :
    displacementKernel t = SignedWeilCorrelation.weilGammaKernel t := by
  unfold displacementKernel SignedWeilCorrelation.weilGammaKernel
  have h1 : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : (1 - Real.exp (-2 * t)) * Real.exp t =
      Real.exp t - Real.exp (-t) := by
    rw [sub_mul, one_mul, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [← h1, ← h2, mul_div_mul_right _ _ (Real.exp_ne_zero t)]

/-- Elementary domination at both zero and infinity; no small-t term is omitted. -/
theorem displacementKernel_secondMoment_le {t : ℝ} (ht : 0 < t) :
    displacementKernel t * t ^ 2 ≤
      (t / 2 + t ^ 2) * Real.exp (-t / 2) := by
  have hd : 0 < 1 - Real.exp (-2 * t) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * t))
    (Real.exp_pos (-2 * t)).le
  have hb : t ≤ (1 / 2 + t) * (1 - Real.exp (-2 * t)) := by
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hb ht.le
  have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-t / 2)).le
  unfold displacementKernel
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The second displacement moment of the actual archimedean measure is finite. -/
theorem integrable_displacementKernel_secondMoment :
    IntegrableOn (fun t => displacementKernel t * t ^ 2) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-t / 2)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul, mul_neg, one_mul, div_eq_mul_inv, mul_comm] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : ℝ)) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have h2 : IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-t / 2)) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_two, neg_mul, mul_neg, one_mul,
      div_eq_mul_inv, mul_comm] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (2 : ℝ)) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hi : IntegrableOn
      (fun t : ℝ => (t / 2 + t ^ 2) * Real.exp (-t / 2)) (Ioi 0) := by
    have he : (fun t : ℝ => (t / 2 + t ^ 2) * Real.exp (-t / 2)) =
        (fun t : ℝ => (t * Real.exp (-t / 2)) / 2 + t ^ 2 * Real.exp (-t / 2)) := by
      ext t
      ring
    rw [he]
    exact (h1.div_const 2).add h2
  apply hi.mono'
  · have hm : Measurable (fun t : ℝ => displacementKernel t * t ^ 2) := by
      unfold displacementKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (displacementKernel_nonneg ht) (sq_nonneg t))]
    exact displacementKernel_secondMoment_le ht

/-- The moment provider also applies directly to the canonical gamma kernel. -/
theorem integrable_weilGammaKernel_secondMoment :
    IntegrableOn (fun t => SignedWeilCorrelation.weilGammaKernel t * t ^ 2)
      (Ioi 0) := by
  simpa only [displacementKernel_eq_weilGammaKernel] using
    integrable_displacementKernel_secondMoment

/-- Every prime power of order at least three, with exponent indexed by `j+3`. -/
noncomputable def higherPrimePowerWeight (p j : ℕ) : ℝ :=
  if p.Prime then Real.log p * (p : ℝ) ^ (-3 / 2 : ℝ) *
    ((p : ℝ) ^ (-1 / 2 : ℝ)) ^ j else 0

noncomputable def higherPrimePowerDisplacement (p j : ℕ) : ℝ :=
  ((j : ℝ) + 3) * Real.log p

/-- This is the coefficient `log p / p^((j+3)/2)`, not a surrogate measure. -/
theorem higherPrimePowerWeight_eq (p j : ℕ) :
    higherPrimePowerWeight p j =
      if p.Prime then Real.log p / (p : ℝ) ^ (((j : ℝ) + 3) / 2) else 0 := by
  unfold higherPrimePowerWeight
  split_ifs with hp
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hj : ((p : ℝ) ^ (-1 / 2 : ℝ)) ^ j =
        (p : ℝ) ^ ((-1 / 2 : ℝ) * (j : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    rw [hj, mul_assoc, ← Real.rpow_add hp0]
    have he : (-3 / 2 : ℝ) + (-1 / 2) * (j : ℝ) = -(((j : ℝ) + 3) / 2) := by ring
    rw [he, Real.rpow_neg hp0.le]
    rfl
  · rfl

theorem higherPrimePowerWeight_nonneg (p j : ℕ) :
    0 ≤ higherPrimePowerWeight p j := by
  unfold higherPrimePowerWeight
  split_ifs with hp
  · exact mul_nonneg
      (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
  · exact le_rfl

private theorem log_nat_mul_rpow_le (p : ℕ) :
    Real.log p * (p : ℝ) ^ (-3 / 2 : ℝ) ≤
      4 * (p : ℝ) ^ (-5 / 4 : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hb := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hh := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hp0.le (-3 / 2))
  have he : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ) =
      (p : ℝ) ^ (-5 / 4 : ℝ) := by
    rw [← Real.rpow_add hp0]
    norm_num
  calc
    _ ≤ ((p : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) * (p : ℝ) ^ (-3 / 2 : ℝ) := hh
    _ = 4 * ((p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ)) := by ring
    _ = _ := by rw [he]

private theorem log_nat_cube_mul_rpow_le (p : ℕ) :
    Real.log p ^ 3 * (p : ℝ) ^ (-3 / 2 : ℝ) ≤
      1728 * (p : ℝ) ^ (-5 / 4 : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)
  have hb := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 12)
  have hb3 : Real.log p ^ 3 ≤ ((p : ℝ) ^ (1 / 12 : ℝ) / (1 / 12)) ^ 3 :=
    pow_le_pow_left₀ hl0 hb 3
  have he1 : ((p : ℝ) ^ (1 / 12 : ℝ)) ^ 3 = (p : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  have he2 : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ) =
      (p : ℝ) ^ (-5 / 4 : ℝ) := by
    rw [← Real.rpow_add hp0]
    norm_num
  calc
    _ ≤ ((p : ℝ) ^ (1 / 12 : ℝ) / (1 / 12)) ^ 3 *
        (p : ℝ) ^ (-3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hb3 (Real.rpow_nonneg hp0.le _)
    _ = 1728 * (((p : ℝ) ^ (1 / 12 : ℝ)) ^ 3 *
        (p : ℝ) ^ (-3 / 2 : ℝ)) := by ring
    _ = _ := by rw [he1, he2]

private noncomputable def universalPowerRatio : ℝ := (2 : ℝ) ^ (-1 / 2 : ℝ)

private theorem universalPowerRatio_nonneg : 0 ≤ universalPowerRatio :=
  Real.rpow_nonneg (by norm_num) _

private theorem universalPowerRatio_lt_one : universalPowerRatio < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

private theorem primePowerRatio_le {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (-1 / 2 : ℝ) ≤ universalPowerRatio := by
  apply Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hp.two_le) (by norm_num)

private theorem summable_weight_majorant :
    Summable (fun pj : ℕ × ℕ =>
      4 * (pj.1 : ℝ) ^ (-5 / 4 : ℝ) * universalPowerRatio ^ pj.2) := by
  have hr0 := universalPowerRatio_nonneg
  have hA : Summable (fun p : ℕ => 4 * (p : ℝ) ^ (-5 / 4 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 4
  have hB : Summable (fun j : ℕ => universalPowerRatio ^ j) :=
    summable_geometric_of_lt_one universalPowerRatio_nonneg universalPowerRatio_lt_one
  apply (summable_prod_of_nonneg (by intro pj; dsimp; positivity)).mpr
  constructor
  · intro p
    exact hB.mul_left (4 * (p : ℝ) ^ (-5 / 4 : ℝ))
  · simpa only [tsum_mul_left] using hA.mul_right (∑' j : ℕ, universalPowerRatio ^ j)

/-- The complete higher-prime-power mass converges, without prime-counting hypotheses. -/
theorem summable_higherPrimePowerWeight :
    Summable (fun pj : ℕ × ℕ => higherPrimePowerWeight pj.1 pj.2) := by
  have hr0 := universalPowerRatio_nonneg
  apply summable_weight_majorant.of_nonneg_of_le
    (fun pj => higherPrimePowerWeight_nonneg _ _)
  intro pj
  rcases pj with ⟨p, j⟩
  unfold higherPrimePowerWeight
  split_ifs with hp
  · exact mul_le_mul (log_nat_mul_rpow_le p)
      (pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _) (primePowerRatio_le hp) j)
      (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) j) (by positivity)
  · positivity

private theorem summable_polynomial_geometric :
    Summable (fun j : ℕ => ((j : ℝ) + 3) ^ 2 * universalPowerRatio ^ j) := by
  have hr : ‖universalPowerRatio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg universalPowerRatio_nonneg]
    exact universalPowerRatio_lt_one
  have h0 := summable_geometric_of_norm_lt_one hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  refine ((h2.add (h1.mul_left 6)).add (h0.mul_left 9)).congr ?_
  intro j
  simp only [pow_one]
  ring

private theorem summable_moment_majorant :
    Summable (fun pj : ℕ × ℕ =>
      1728 * (pj.1 : ℝ) ^ (-5 / 4 : ℝ) *
        (((pj.2 : ℝ) + 3) ^ 2 * universalPowerRatio ^ pj.2)) := by
  have hr0 := universalPowerRatio_nonneg
  have hA : Summable (fun p : ℕ => 1728 * (p : ℝ) ^ (-5 / 4 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 1728
  apply (summable_prod_of_nonneg (by intro pj; dsimp; positivity)).mpr
  constructor
  · intro p
    exact summable_polynomial_geometric.mul_left (1728 * (p : ℝ) ^ (-5 / 4 : ℝ))
  · simpa only [tsum_mul_left] using hA.mul_right
      (∑' j : ℕ, ((j : ℝ) + 3) ^ 2 * universalPowerRatio ^ j)

/-- The actual second displacement moment of every higher prime power is summable. -/
theorem summable_higherPrimePower_secondMoment :
    Summable (fun pj : ℕ × ℕ => higherPrimePowerWeight pj.1 pj.2 *
      higherPrimePowerDisplacement pj.1 pj.2 ^ 2) := by
  have hr0 := universalPowerRatio_nonneg
  apply summable_moment_majorant.of_nonneg_of_le
    (fun pj => mul_nonneg (higherPrimePowerWeight_nonneg _ _) (sq_nonneg _))
  intro pj
  rcases pj with ⟨p, j⟩
  unfold higherPrimePowerWeight higherPrimePowerDisplacement
  split_ifs with hp
  · have hpow : ((p : ℝ) ^ (-1 / 2 : ℝ)) ^ j ≤ universalPowerRatio ^ j :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _) (primePowerRatio_le hp) j
    have hm := mul_le_mul (log_nat_cube_mul_rpow_le p)
      (mul_le_mul_of_nonneg_left hpow (sq_nonneg ((j : ℝ) + 3)))
      (mul_nonneg (sq_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) j))
      (by positivity : 0 ≤ 1728 * (p : ℝ) ^ (-5 / 4 : ℝ))
    nlinarith [hm]
  · simp only [zero_mul]
    positivity

/-- The full higher-power correction, including every exponent at least three. -/
noncomputable def higherPrimePowerCorrection (c : ℝ → ℝ) (R : ℝ) : ℝ :=
  2 * ∑' pj : ℕ × ℕ, higherPrimePowerWeight pj.1 pj.2 *
    (1 - c (higherPrimePowerDisplacement pj.1 pj.2 / R))

/-- Finite second moment supplies convergence and the quadratic-scale estimate.
The hypothesis is a pointwise displacement bound on the profile, not an
assumption of convergence or a prime-number estimate. -/
theorem higherPrimePowerCorrection_bound (c : ℝ → ℝ) (R B : ℝ)
    (hB : 0 ≤ B)
    (hc : ∀ t : ℝ, |1 - c (t / R)| ≤ B * (t / R) ^ 2) :
    Summable (fun pj : ℕ × ℕ => higherPrimePowerWeight pj.1 pj.2 *
      (1 - c (higherPrimePowerDisplacement pj.1 pj.2 / R))) ∧
    |higherPrimePowerCorrection c R| ≤
      (2 * B / R ^ 2) * ∑' pj : ℕ × ℕ,
        higherPrimePowerWeight pj.1 pj.2 * higherPrimePowerDisplacement pj.1 pj.2 ^ 2 := by
  let M : ℕ × ℕ → ℝ := fun pj =>
    higherPrimePowerWeight pj.1 pj.2 * higherPrimePowerDisplacement pj.1 pj.2 ^ 2
  let f : ℕ × ℕ → ℝ := fun pj => higherPrimePowerWeight pj.1 pj.2 *
    (1 - c (higherPrimePowerDisplacement pj.1 pj.2 / R))
  have hM : Summable M := summable_higherPrimePower_secondMoment
  have hdom (pj : ℕ × ℕ) : ‖f pj‖ ≤ (B / R ^ 2) * M pj := by
    simp only [f, M, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (higherPrimePowerWeight_nonneg _ _)]
    calc
      _ ≤ higherPrimePowerWeight pj.1 pj.2 *
          (B * (higherPrimePowerDisplacement pj.1 pj.2 / R) ^ 2) :=
        mul_le_mul_of_nonneg_left (hc _) (higherPrimePowerWeight_nonneg _ _)
      _ = _ := by ring
  have hf : Summable f := (hM.mul_left (B / R ^ 2)).of_norm_bounded hdom
  refine ⟨hf, ?_⟩
  have hb : ‖∑' pj, f pj‖ ≤ (B / R ^ 2) * ∑' pj, M pj := by
    calc
      _ ≤ ∑' pj, ‖f pj‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ ∑' pj, (B / R ^ 2) * M pj :=
        Summable.tsum_le_tsum hdom hf.norm (hM.mul_left _)
      _ = _ := tsum_mul_left
  unfold higherPrimePowerCorrection
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Real.norm_eq_abs, f, M, mul_assoc, mul_div_assoc] using hs

/-- Adding back the complete constant is a legitimate infinite-series identity. -/
theorem higherPrimePowerSector_exact (c : ℝ → ℝ) (R : ℝ)
    (hc : ∀ t, |c t| ≤ 1) :
    (-2 * ∑' pj : ℕ × ℕ, higherPrimePowerWeight pj.1 pj.2 *
      c (higherPrimePowerDisplacement pj.1 pj.2 / R)) =
    -2 * (∑' pj : ℕ × ℕ, higherPrimePowerWeight pj.1 pj.2) +
      higherPrimePowerCorrection c R := by
  have hs : Summable (fun pj : ℕ × ℕ => higherPrimePowerWeight pj.1 pj.2 *
      c (higherPrimePowerDisplacement pj.1 pj.2 / R)) := by
    apply summable_higherPrimePowerWeight.of_norm_bounded
    intro pj
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (higherPrimePowerWeight_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_left (hc _) (higherPrimePowerWeight_nonneg _ _)).trans_eq
      (mul_one _)
  unfold higherPrimePowerCorrection
  have he : (fun pj : ℕ × ℕ => higherPrimePowerWeight pj.1 pj.2 *
      (1 - c (higherPrimePowerDisplacement pj.1 pj.2 / R))) =
    (fun pj : ℕ × ℕ => higherPrimePowerWeight pj.1 pj.2 -
      higherPrimePowerWeight pj.1 pj.2 * c (higherPrimePowerDisplacement pj.1 pj.2 / R)) := by
    ext pj
    ring
  rw [he, Summable.tsum_sub summable_higherPrimePowerWeight hs]
  ring

end RiemannResearch.RH.PrimeCompensationLimits
