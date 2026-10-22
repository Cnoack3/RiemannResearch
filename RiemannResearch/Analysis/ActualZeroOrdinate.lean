/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.RH.WeilExplicitFormula.Statement.SeamClosed
import RiemannResearch.RH.WeilExplicitFormula.RvM.LocalCount
import RiemannResearch.RH.WeilExplicitFormula.RvM.CompletedZeta

/-!
# Actual zeta-zero ordinate cutoffs and unconditional reflection estimates

All zeros, multiplicities and cutoffs below are those of Mathlib's actual
`riemannZeta`. The finite identities and estimates have no analytic assumptions.
The sufficient Landau estimate is in ActualUniformRationalLandau. The classical
unconditional Selberg exponential density theorem is not yet formalized here.
-/

noncomputable section
open Filter MeasureTheory Complex Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- Distinct actual nontrivial zeros in the positive-height cutoff. -/
def cutoff (T : ℝ) : Finset ℂ := (zerosIn_finite 0 T).toFinset

@[simp] theorem mem_cutoff {T : ℝ} {ρ : ℂ} :
    ρ ∈ cutoff T ↔ IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  simp [cutoff, zerosIn]

/-- Multiplicity is always positive at an actual zero. -/
theorem multiplicity_pos {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff T) :
    0 < zeroMult ρ := zetaSeam.one_le_mult ρ (mem_cutoff.mp hρ).1

/-- This bound is proved for actual zeros, not accepted as a sampling input. -/
theorem displacement_lt_half {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff T) :
    |ρ.re - 1 / 2| < 1 / 2 := by
  obtain ⟨hzero, hlo, hhi⟩ := mem_cutoff.mp hρ
  rw [abs_lt]
  constructor <;> linarith [hzero.2.1, hzero.2.2]

theorem count_eq_sum (T : ℝ) :
    Ncount 0 T = ∑ ρ ∈ cutoff T, zeroMult ρ := by
  rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite 0 T)]
  rfl

/-- A finite type containing one element for each copy of every zero. -/
abbrev Copies (T : ℝ) := (ρ : {z // z ∈ cutoff T}) × Fin (zeroMult ρ.1)

theorem card_copies (T : ℝ) : Fintype.card (Copies T) = Ncount 0 T := by
  classical
  simp [Copies, Fintype.card_sigma, count_eq_sum, Finset.sum_attach]

/-- A genuine multiplicity-weighted zero sum. -/
def sum (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ ρ ∈ cutoff T, (zeroMult ρ : ℂ) * f ρ

/-- Real-valued multiplicity-weighted zero sum. -/
def realSum (T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ ρ ∈ cutoff T, (zeroMult ρ : ℝ) * f ρ

@[simp] theorem sum_one (T : ℝ) : sum T (fun _ => 1) = (Ncount 0 T : ℂ) := by
  simp [sum, count_eq_sum]

@[simp] theorem realSum_one (T : ℝ) : realSum T (fun _ => 1) = (Ncount 0 T : ℝ) := by
  simp [realSum, count_eq_sum]

@[simp] theorem sum_add (T : ℝ) (f g : ℂ → ℂ) :
    sum T (fun ρ => f ρ + g ρ) = sum T f + sum T g := by
  simp [sum, mul_add, Finset.sum_add_distrib]

@[simp] theorem sum_sub (T : ℝ) (f g : ℂ → ℂ) :
    sum T (fun ρ => f ρ - g ρ) = sum T f - sum T g := by
  simp [sum, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem sum_mul_const (T : ℝ) (f : ℂ → ℂ) (c : ℂ) :
    sum T (fun ρ => f ρ * c) = sum T f * c := by
  simp [sum, mul_assoc, Finset.sum_mul]

@[simp] theorem realSum_mul_const (T : ℝ) (f : ℂ → ℝ) (c : ℝ) :
    realSum T (fun ρ => f ρ * c) = realSum T f * c := by
  simp [realSum, mul_assoc, Finset.sum_mul]

theorem realSum_nonneg (T : ℝ) (f : ℂ → ℝ) (hf : ∀ ρ ∈ cutoff T, 0 ≤ f ρ) :
    0 ≤ realSum T f := by
  exact Finset.sum_nonneg (fun ρ hρ => mul_nonneg (Nat.cast_nonneg _) (hf ρ hρ))

theorem realSum_mono (T : ℝ) (f g : ℂ → ℝ)
    (hfg : ∀ ρ ∈ cutoff T, f ρ ≤ g ρ) : realSum T f ≤ realSum T g := by
  exact Finset.sum_le_sum (fun ρ hρ =>
    mul_le_mul_of_nonneg_left (hfg ρ hρ) (Nat.cast_nonneg _))

theorem norm_sum_le (T : ℝ) (f : ℂ → ℂ) :
    ‖sum T f‖ ≤ realSum T (fun ρ => ‖f ρ‖) := by
  simpa only [sum, realSum, norm_mul, Complex.norm_natCast] using
    (_root_.norm_sum_le (cutoff T) (fun ρ => (zeroMult ρ : ℂ) * f ρ))

/-- Reflection preserves actual positive-height cutoffs and all multiplicities. -/
theorem reflect_mem {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff T) : reflect ρ ∈ cutoff T := by
  obtain ⟨hz, hlo, hhi⟩ := mem_cutoff.mp hρ
  exact mem_cutoff.mpr ⟨zetaSeam.reflect_zero ρ hz, by simpa [reflect_im] using hlo,
    by simpa [reflect_im] using hhi⟩

theorem sum_reflect (T : ℝ) (f : ℂ → ℂ) :
    sum T (fun ρ => f (reflect ρ)) = sum T f := by
  classical
  unfold sum
  apply Finset.sum_bij (fun ρ _ => reflect ρ)
  · exact fun ρ hρ => reflect_mem hρ
  · intro a ha b hb hab
    simpa only [reflect_reflect] using congrArg reflect hab
  · intro ρ hρ
    exact ⟨reflect ρ, reflect_mem hρ, reflect_reflect ρ⟩
  · intro ρ hρ
    rw [zetaSeam.mult_reflect ρ (mem_cutoff.mp hρ).1]

/-- Centered Landau sum for the actual zeros. -/
def landauSum (T u : ℝ) : ℂ :=
  sum T (fun ρ => Complex.exp ((u : ℂ) * (ρ - 1 / 2)))

/-- Fourier sum of the actual ordinates, counting multiplicities. -/
def ordinateSum (T u : ℝ) : ℂ := sum T (fun ρ => phase u ρ.im)

/-- Total squared horizontal displacement, counting multiplicities. -/
def horizontalEnergy (T : ℝ) : ℝ := realSum T (fun ρ => (ρ.re - 1 / 2) ^ 2)

theorem horizontalEnergy_nonneg (T : ℝ) : 0 ≤ horizontalEnergy T :=
  realSum_nonneg T _ (fun _ _ => sq_nonneg _)

theorem horizontalEnergy_le_count (T : ℝ) :
    horizontalEnergy T ≤ (Ncount 0 T : ℝ) / 4 := by
  have hb : ∀ ρ ∈ cutoff T, (ρ.re - 1 / 2) ^ 2 ≤ 1 / 4 := by
    intro ρ hρ
    have h := displacement_lt_half hρ
    nlinarith [sq_abs (ρ.re - 1 / 2), abs_nonneg (ρ.re - 1 / 2)]
  calc
    _ ≤ realSum T (fun _ => 1 / 4) := realSum_mono T _ _ hb
    _ = _ := by simp only [realSum, ← Finset.sum_mul, ← Nat.cast_sum,
      ← count_eq_sum, div_eq_mul_inv, one_mul]

theorem exp_centered_eq (u : ℝ) (ρ : ℂ) :
    Complex.exp ((u : ℂ) * (ρ - 1 / 2)) =
      phase u ρ.im * (Real.exp (u * (ρ.re - 1 / 2)) : ℂ) := by
  rw [phase, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- Exact reflection cancellation; no RH or asymptotic estimate is used. -/
theorem landauSum_eq_cosh (T u : ℝ) :
    landauSum T u = sum T (fun ρ => phase u ρ.im *
      (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)) := by
  have hr := sum_reflect T (fun ρ => phase u ρ.im *
    (Real.exp (u * (ρ.re - 1 / 2)) : ℂ))
  have hneg : sum T (fun ρ => phase u ρ.im *
      (Real.exp (-(u * (ρ.re - 1 / 2))) : ℂ)) = landauSum T u := by
    unfold landauSum
    simp_rw [exp_centered_eq]
    convert hr using 2
    funext ρ
    rw [reflect_im, reflect_re]
    congr 3; ring
  have heq : (fun ρ : ℂ => phase u ρ.im *
      (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)) =
      (fun ρ => (phase u ρ.im * (Real.exp (u * (ρ.re - 1 / 2)) : ℂ) +
        phase u ρ.im * (Real.exp (-(u * (ρ.re - 1 / 2))) : ℂ)) * (2 : ℂ)⁻¹) := by
    funext ρ
    rw [Real.cosh_eq]
    push_cast
    ring
  rw [heq, sum_mul_const, sum_add, hneg]
  unfold landauSum
  simp_rw [exp_centered_eq]
  ring

/-- A Taylor bound with cancellation of the linear terms. -/
theorem cosh_sub_one_bound (a : ℝ) :
    ‖(Real.cosh a : ℂ) - 1‖ ≤ a ^ 2 * Real.exp |a| := by
  have hp := Complex.norm_exp_sub_sum_le_norm_mul_exp (a : ℂ) 2
  have hm := Complex.norm_exp_sub_sum_le_norm_mul_exp (-a : ℂ) 2
  simp [Finset.sum_range_succ, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp hm
  have heq : (Real.cosh a : ℂ) - 1 =
      ((Complex.exp (a : ℂ) - (1 + a)) +
        (Complex.exp (-a : ℂ) - (1 - a))) * (2 : ℂ)⁻¹ := by
    rw [Real.cosh_eq]
    push_cast
    ring
  rw [heq, norm_mul]
  have ht := norm_add_le (Complex.exp (a : ℂ) - (1 + a))
    (Complex.exp (-a : ℂ) - (1 - a))
  simp only [← sub_eq_add_neg] at hm
  norm_num at *
  linarith

/-- The actual, multiplicity-weighted second-order weight-removal inequality. -/
theorem ordinate_landau_error (T u : ℝ) :
    ‖ordinateSum T u - landauSum T u‖ ≤
      (u ^ 2 * Real.exp (|u| / 2)) * horizontalEnergy T := by
  rw [ordinateSum, landauSum_eq_cosh, ← sum_sub]
  have hp : ∀ ρ ∈ cutoff T,
      ‖phase u ρ.im - phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)‖ ≤
      (ρ.re - 1 / 2) ^ 2 * (u ^ 2 * Real.exp (|u| / 2)) := by
    intro ρ hρ
    have heq : phase u ρ.im - phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) =
        phase u ρ.im * (1 - (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)) := by ring
    rw [heq, norm_mul, phase_norm, one_mul, norm_sub_rev]
    have ha : |u * (ρ.re - 1 / 2)| ≤ |u| / 2 := by
      rw [abs_mul]
      nlinarith [displacement_lt_half hρ, abs_nonneg u]
    calc
      _ ≤ (u * (ρ.re - 1 / 2)) ^ 2 * Real.exp |u * (ρ.re - 1 / 2)| :=
        cosh_sub_one_bound _
      _ ≤ (u * (ρ.re - 1 / 2)) ^ 2 * Real.exp (|u| / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ realSum T (fun ρ => ‖phase u ρ.im -
        phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)‖) := norm_sum_le _ _
    _ ≤ realSum T (fun ρ => (ρ.re - 1 / 2) ^ 2 * (u ^ 2 * Real.exp (|u| / 2))) :=
      realSum_mono T _ _ hp
    _ = _ := by rw [realSum_mul_const]; exact mul_comm _ _


/-- Every actual zero with positive imaginary part is in the critical strip.
Thus the cutoff has not silently discarded any positive-ordinate zeta zero. -/
theorem positive_zero_in_strip {ρ : ℂ} (hz : riemannZeta ρ = 0) (hi : 0 < ρ.im) :
    IsNontrivialZero ρ := by
  have hρ : ρ ≠ 0 := by intro h; subst ρ; simp at hi
  have hG : Gammaℝ ρ ≠ 0 := by
    intro h
    obtain ⟨n, rfl⟩ := Gammaℝ_eq_zero_iff.mp h
    simp at hi
  have hc : completedRiemannZeta ρ = 0 := by
    rw [Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hρ hG, hz, mul_zero]
  refine ⟨hz, ?_, ?_⟩
  · by_contra h
    exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_re_nonpos (le_of_not_gt h) hc
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hz

theorem mem_cutoff_iff_zeta {T : ℝ} {ρ : ℂ} :
    ρ ∈ cutoff T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  constructor
  · intro h
    obtain ⟨hz, hlo, hhi⟩ := mem_cutoff.mp h
    exact ⟨hz.1, hlo, hhi⟩
  · rintro ⟨hz, hlo, hhi⟩
    exact mem_cutoff.mpr ⟨positive_zero_in_strip hz hlo, hlo, hhi⟩

/-- Countability of the actual positive zeros, with no chosen enumeration. -/
theorem positive_zeros_countable :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.im}.Countable := by
  have hc : (⋃ n : ℕ, zerosIn 0 (n : ℝ)).Countable :=
    Set.countable_iUnion (fun n => (zerosIn_finite 0 (n : ℝ)).countable)
  apply hc.mono
  intro ρ hρ
  obtain ⟨n, hn⟩ := exists_nat_gt ρ.im
  exact Set.mem_iUnion.mpr ⟨n, positive_zero_in_strip hρ.1 hρ.2, hρ.2, hn.le⟩

abbrev PositiveZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.im}
instance : Countable PositiveZero := positive_zeros_countable.to_subtype

/-- Countably many zero copies, retaining analytic multiplicity. -/
abbrev PositiveCopies := (ρ : PositiveZero) × Fin (zeroMult ρ.1)
instance : Countable PositiveCopies := inferInstance

/-- The normalized ordinate sum, defined even for empty cutoffs. -/
def average (T : ℝ) (f : ℂ → ℂ) : ℂ := sum T f / (Ncount 0 T : ℂ)

/-- Normalized horizontal energy, not assumed to tend to zero. -/
def relativeEnergy (T : ℝ) : ℝ := horizontalEnergy T / (Ncount 0 T : ℝ)

theorem normalized_ordinate_landau_error (T u : ℝ) :
    ‖ordinateSum T u / (Ncount 0 T : ℂ) - landauSum T u / (Ncount 0 T : ℂ)‖ ≤
      (u ^ 2 * Real.exp (|u| / 2)) * relativeEnergy T := by
  rw [← sub_div, norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((u ^ 2 * Real.exp (|u| / 2)) * horizontalEnergy T) / (Ncount 0 T : ℝ) :=
      div_le_div_of_nonneg_right (ordinate_landau_error T u) (Nat.cast_nonneg _)
    _ = _ := by unfold relativeEnergy; ring

/-- Local multiplicity growth, instantiated with the actual zeta function. -/
theorem local_zero_count : ∃ C : ℝ, 1 ≤ C ∧
    ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ C * Real.log (|t| + 3) :=
  Zeta23.RvM.zeta_local_zero_count

/-- No horizontal first moment survives reflection, for any height cutoff. -/
theorem centered_first_moment_zero (T : ℝ) :
    sum T (fun ρ => (ρ.re - 1 / 2 : ℝ)) = 0 := by
  have h := sum_reflect T (fun ρ => ((ρ.re - 1 / 2 : ℝ) : ℂ))
  have heq : sum T (fun ρ => (((reflect ρ).re - 1 / 2 : ℝ) : ℂ)) =
      -sum T (fun ρ => ((ρ.re - 1 / 2 : ℝ) : ℂ)) := by
    unfold sum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp only
    rw [reflect_re]
    push_cast
    ring
  rw [heq] at h
  linear_combination - (1 / 2 : ℂ) * h


/-- Vanishing horizontal energy is exactly the critical-line assertion on the cutoff. -/
theorem horizontalEnergy_eq_zero_iff (T : ℝ) :
    horizontalEnergy T = 0 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    have hle := Finset.single_le_sum
      (fun σ (_ : σ ∈ cutoff T) => mul_nonneg (Nat.cast_nonneg (zeroMult σ) :
        (0 : ℝ) ≤ (zeroMult σ : ℝ)) (sq_nonneg (σ.re - 1 / 2))) hρ
    change (zeroMult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 ≤ horizontalEnergy T at hle
    have hm : (0 : ℝ) < (zeroMult ρ : ℝ) := by exact_mod_cast multiplicity_pos hρ
    rw [h] at hle
    have hs : (ρ.re - 1 / 2) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hle) hm
    nlinarith [sq_nonneg (ρ.re - 1 / 2)]
  · intro h
    unfold horizontalEnergy realSum
    apply Finset.sum_eq_zero
    intro ρ hρ
    dsimp only
    rw [h ρ hρ]
    norm_num

/-- Ordinate projection on the actual multiset represented by its finite copy type. -/
def copyOrdinate (T : ℝ) (c : Copies T) : ℝ := c.1.1.im

/-- Exact absence of collisions among zero copies is equivalent to all zeros in
that cutoff being simple and on the critical line. This does NOT assert injectivity. -/
theorem copyOrdinate_injective_iff (T : ℝ) :
    Function.Injective (copyOrdinate T) ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  constructor
  · intro hinj ρ hρ
    let c : Copies T := ⟨⟨ρ, hρ⟩, ⟨0, multiplicity_pos hρ⟩⟩
    let d : Copies T := ⟨⟨reflect ρ, reflect_mem hρ⟩,
      ⟨0, multiplicity_pos (reflect_mem hρ)⟩⟩
    have hsame : copyOrdinate T c = copyOrdinate T d := (reflect_im ρ).symm
    have hre := congrArg (fun x : Copies T => x.1.1.re) (hinj hsame)
    change ρ.re = (reflect ρ).re at hre
    rw [reflect_re] at hre
    refine ⟨by linarith, ?_⟩
    by_contra hm
    have htwo : 1 < zeroMult ρ := by have := multiplicity_pos hρ; omega
    let e : Copies T := ⟨⟨ρ, hρ⟩, ⟨1, htwo⟩⟩
    have h01 := congrArg (fun x : Copies T => x.2.val)
      (hinj (show copyOrdinate T c = copyOrdinate T e from rfl))
    change (0 : ℕ) = 1 at h01
    omega
  · intro hall a b hab
    rcases a with ⟨a, ai⟩
    rcases b with ⟨b, bi⟩
    have hv : a = b := by
      apply Subtype.ext
      apply Complex.ext
      · rw [(hall _ a.property).1, (hall _ b.property).1]
      · exact hab
    subst b
    have hsize := (hall a.val a.property).2
    have hidx : ai = bi := by
      apply Fin.ext
      have ha := ai.isLt
      have hb := bi.isLt
      omega
    subst bi
    rfl


/-- Weighted sums equal literal sums over the finite multiset of zero copies. -/
theorem sum_eq_copies (T : ℝ) (f : ℂ → ℂ) :
    sum T f = ∑ c : Copies T, f c.1.1 := by
  classical
  simp [sum, Copies, Fintype.sum_sigma, nsmul_eq_mul,
    ← Finset.sum_attach (cutoff T) (fun ρ => (zeroMult ρ : ℂ) * f ρ)]

theorem realSum_eq_copies (T : ℝ) (f : ℂ → ℝ) :
    realSum T f = ∑ c : Copies T, f c.1.1 := by
  classical
  simp [realSum, Copies, Fintype.sum_sigma, nsmul_eq_mul,
    ← Finset.sum_attach (cutoff T) (fun ρ => (zeroMult ρ : ℝ) * f ρ)]


/-- Complete signed correction, before any norm bound is taken. -/
def coshCorrection (T u : ℝ) : ℂ := sum T (fun ρ =>
  phase u ρ.im * ((Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) - 1))

theorem exact_signed_correction (T u : ℝ) :
    ordinateSum T u = landauSum T u - coshCorrection T u := by
  rw [landauSum_eq_cosh, coshCorrection, ← sum_sub]
  unfold ordinateSum
  congr 1
  funext ρ
  ring

/-! ## Symmetric good/bad masks with complete signed corrections -/

def goodWeight (δ : ℝ) (ρ : ℂ) : ℂ :=
  if |ρ.re - 1 / 2| ≤ δ then 1 else 0

def badWeight (δ : ℝ) (ρ : ℂ) : ℂ := 1 - goodWeight δ ρ

theorem abs_displacement_reflect (ρ : ℂ) :
    |(reflect ρ).re - 1 / 2| = |ρ.re - 1 / 2| := by
  rw [reflect_re]
  have h : 1 - ρ.re - 1 / 2 = -(ρ.re - 1 / 2) := by ring
  rw [h, abs_neg]

theorem goodWeight_reflect (δ : ℝ) (ρ : ℂ) :
    goodWeight δ (reflect ρ) = goodWeight δ ρ := by
  simp only [goodWeight, abs_displacement_reflect]

theorem badWeight_reflect (δ : ℝ) (ρ : ℂ) :
    badWeight δ (reflect ρ) = badWeight δ ρ := by
  simp only [badWeight, goodWeight_reflect]

theorem weighted_sum_split (T δ : ℝ) (f : ℂ → ℂ) :
    sum T f = sum T (fun ρ => goodWeight δ ρ * f ρ) +
      sum T (fun ρ => badWeight δ ρ * f ρ) := by
  rw [← sum_add]
  congr 1
  funext ρ
  unfold badWeight
  ring

def weightedLandauSum (T u : ℝ) (w : ℂ → ℂ) : ℂ :=
  sum T (fun ρ => w ρ * Complex.exp ((u : ℂ) * (ρ - 1 / 2)))

def weightedOrdinateSum (T u : ℝ) (w : ℂ → ℂ) : ℂ :=
  sum T (fun ρ => w ρ * phase u ρ.im)

def weightedCoshCorrection (T u : ℝ) (w : ℂ → ℂ) : ℂ :=
  sum T (fun ρ => w ρ * phase u ρ.im *
    ((Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) - 1))

/-- Actual-zero reflection with an invariant weight. The explicit good/bad
weights below discharge invariance without any analytic assumption. -/
theorem weightedLandauSum_eq_cosh (T u : ℝ) (w : ℂ → ℂ)
    (hw : ∀ ρ, w (reflect ρ) = w ρ) :
    weightedLandauSum T u w = sum T (fun ρ => w ρ * phase u ρ.im *
      (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)) := by
  have hr := sum_reflect T (fun ρ => w ρ * phase u ρ.im *
    (Real.exp (u * (ρ.re - 1 / 2)) : ℂ))
  have hneg : sum T (fun ρ => w ρ * phase u ρ.im *
      (Real.exp (-(u * (ρ.re - 1 / 2))) : ℂ)) =
        weightedLandauSum T u w := by
    unfold weightedLandauSum
    simp_rw [exp_centered_eq, ← mul_assoc]
    convert hr using 2
    funext ρ
    rw [hw, reflect_im, reflect_re]
    congr 3
    ring
  have heq : (fun ρ : ℂ => w ρ * phase u ρ.im *
      (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)) =
      (fun ρ => (w ρ * phase u ρ.im * (Real.exp (u * (ρ.re - 1 / 2)) : ℂ) +
        w ρ * phase u ρ.im * (Real.exp (-(u * (ρ.re - 1 / 2))) : ℂ)) *
          (2 : ℂ)⁻¹) := by
    funext ρ
    rw [Real.cosh_eq]
    push_cast
    ring
  rw [heq, sum_mul_const, sum_add, hneg]
  unfold weightedLandauSum
  simp_rw [exp_centered_eq, ← mul_assoc]
  ring

theorem weighted_exact_signed_correction (T u : ℝ) (w : ℂ → ℂ)
    (hw : ∀ ρ, w (reflect ρ) = w ρ) :
    weightedOrdinateSum T u w =
      weightedLandauSum T u w - weightedCoshCorrection T u w := by
  rw [weightedLandauSum_eq_cosh T u w hw, weightedCoshCorrection, ← sum_sub]
  unfold weightedOrdinateSum
  congr 1
  funext ρ
  ring

theorem good_exact_signed_correction (T u δ : ℝ) :
    weightedOrdinateSum T u (goodWeight δ) =
      weightedLandauSum T u (goodWeight δ) -
        weightedCoshCorrection T u (goodWeight δ) :=
  weighted_exact_signed_correction T u _ (goodWeight_reflect δ)

theorem bad_exact_signed_correction (T u δ : ℝ) :
    weightedOrdinateSum T u (badWeight δ) =
      weightedLandauSum T u (badWeight δ) -
        weightedCoshCorrection T u (badWeight δ) :=
  weighted_exact_signed_correction T u _ (badWeight_reflect δ)


end RiemannResearch.Analysis.ActualZeroOrdinate
