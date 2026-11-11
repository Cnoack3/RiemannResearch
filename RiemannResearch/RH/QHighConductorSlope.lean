import RiemannResearch.RH.QMatchedOscillationKernel
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# High-conductor slope representers

Source: short-head localization argument in the full oscillation catalog,
10 November 2026. The result uses the complete Q norm, not a finite surrogate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiemannResearch.RH.QHighConductorSlope
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeCorrectionKernel
open RiemannResearch.Analysis.ResidualizedProjectionKernel

/-- Every member is linear on the physical sites 0,...,H. -/
def HasLinearHead (U : Submodule ℝ QHilbert) (H : ℕ) : Prop :=
  ∀ f ∈ U, ∀ n ≤ H, qSequence f n = (n : ℝ) * qSequence f 1

theorem high_span_linear (D : Set ℕ) (H : ℕ) (hH : 1 ≤ H)
    (hD : ∀ q ∈ D, H < q) :
    HasLinearHead (Submodule.span ℝ (qResidue '' D)) H := by
  intro f hf n hn
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨q, hq, rfl⟩ := hf
      have hnq : n < q := hn.trans_lt (hD q hq)
      have h1q : 1 < q := hH.trans_lt (hD q hq)
      simp only [qSequence_qResidue, ArithmeticCumulative.residueFraction,
        Nat.mod_eq_of_lt hnq, Nat.mod_eq_of_lt h1q, Nat.cast_one]
      ring
  | zero => simp [show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]
  | add f g hf hg ihf ihg =>
      change qSequenceLinear (f + g) n = (n : ℝ) * qSequenceLinear (f + g) 1
      simp only [map_add, Pi.add_apply]
      change qSequence f n + qSequence g n = (n : ℝ) * (qSequence f 1 + qSequence g 1)
      rw [ihf, ihg]
      ring
  | smul c f hf ih =>
      change qSequenceLinear (c • f) n = (n : ℝ) * qSequenceLinear (c • f) 1
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      change c * qSequence f n = (n : ℝ) * (c * qSequence f 1)
      rw [ih]
      ring

variable (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]

def slopeRepresenter : QHilbert := U.starProjection (evaluation 1)
def slopeEnergy : ℝ := ‖slopeRepresenter U‖ ^ 2

theorem inner_slope (f : QHilbert) (hf : f ∈ U) :
    inner ℝ f (slopeRepresenter U) = qSequence f 1 := by
  rw [slopeRepresenter, ← projection_inner,
    Submodule.starProjection_eq_self_iff.mpr hf, inner_evaluation]

theorem slope_value_one :
    qSequence (slopeRepresenter U) 1 = slopeEnergy U := by
  rw [← inner_slope U (slopeRepresenter U)
    (show slopeRepresenter U ∈ U from U.starProjection_apply_mem _)]
  exact real_inner_self_eq_norm_sq _

theorem projected_evaluation_of_linear_head (H : ℕ) (hlin : HasLinearHead U H)
    (n : ℕ) (hn : n ≤ H) :
    U.starProjection (evaluation n) = (n : ℝ) • slopeRepresenter U := by
  apply ext_inner_left ℝ
  intro f
  rw [← projection_inner, inner_evaluation, real_inner_smul_right,
    slopeRepresenter, ← projection_inner, inner_evaluation]
  exact hlin _ (U.starProjection_apply_mem f) n hn

theorem pairKernel_eq_slope (H : ℕ) (hlin : HasLinearHead U H)
    (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    QMatchedOscillationKernel.pairKernel U n m =
      ((n : ℝ) - m) • slopeRepresenter U := by
  rw [QMatchedOscillationKernel.pairKernel, map_sub,
    projected_evaluation_of_linear_head U H hlin n hn,
    projected_evaluation_of_linear_head U H hlin m hm, sub_smul]

theorem slope_physical (H : ℕ) (hlin : HasLinearHead U H)
    (s : ℕ) (hs : s ≤ H) :
    qSequence (slopeRepresenter U) s = (s : ℝ) * slopeEnergy U := by
  rw [hlin (slopeRepresenter U)
    (show slopeRepresenter U ∈ U from U.starProjection_apply_mem _) s hs, slope_value_one]

theorem linear_head_energy (H : ℕ) (f : QHilbert)
    (hf : ∀ s ≤ H, qSequence f s = (s : ℝ) * qSequence f 1) :
    (H : ℝ) * (qSequence f 1) ^ 2 / zetaTwo ≤ ‖f‖ ^ 2 := by
  have hcoord (i : ℕ) (hi : i < H) :
      (f i) ^ 2 = (qSequence f 1) ^ 2 / zetaTwo := by
    rw [← qSequence_weighted_square, hf (i + 1) (by omega),
      positiveQWeight]
    have hiR : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  calc
    (H : ℝ) * (qSequence f 1) ^ 2 / zetaTwo =
        ∑ i ∈ Finset.range H, (f i) ^ 2 := by
      simp only [Finset.sum_congr rfl (fun i hi =>
        hcoord i (Finset.mem_range.mp hi)), Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ ∑' i, (f i) ^ 2 :=
      (qCoordinate_square_summable f).sum_le_tsum _ (fun _ _ => sq_nonneg _)
    _ = ‖f‖ ^ 2 := (qNorm_sq f).symm

theorem slopeEnergy_le (H : ℕ) (hH : 0 < H) (hlin : HasLinearHead U H) :
    slopeEnergy U ≤ zetaTwo / H := by
  have h := linear_head_energy H (slopeRepresenter U)
    (hlin _ (U.starProjection_apply_mem _))
  rw [slope_value_one] at h
  change (H : ℝ) * (slopeEnergy U) ^ 2 / zetaTwo ≤ slopeEnergy U at h
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have ha : 0 ≤ slopeEnergy U := sq_nonneg _
  have he := (div_le_iff₀ zetaTwo_pos).mp h
  apply (le_div_iff₀ hp).mpr
  by_cases hz : slopeEnergy U = 0
  · simpa only [hz, zero_mul] using zetaTwo_pos.le
  · have hap : 0 < slopeEnergy U := lt_of_le_of_ne ha (Ne.symm hz)
    nlinarith

/-- The signed head contribution is exactly a scalar multiple of the residual mean. -/
theorem high_head_pairing (H A : ℕ) (hlin : HasLinearHead U H) (hA : A ≤ H)
    (r : ℕ → ℝ) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    (∑ s ∈ Finset.Icc 1 A, Pareto.positiveWeight s * r s *
      (qSequence (QMatchedOscillationKernel.pairKernel U n m) s / s)) =
    ((n : ℝ) - m) * slopeEnergy U *
      ∑ s ∈ Finset.Icc 1 A, Pareto.positiveWeight s * r s := by
  rw [pairKernel_eq_slope U H hlin n m hn hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs0 : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1))
  have hsH := (Finset.mem_Icc.mp hs).2.trans hA
  have hsm := congrFun (qSequenceLinear.map_smul ((n : ℝ) - m)
    (slopeRepresenter U)) s
  change qSequence (((n : ℝ) - m) • slopeRepresenter U) s =
    ((n : ℝ) - m) * qSequence (slopeRepresenter U) s at hsm
  rw [hsm, slope_physical U H hlin s hsH]
  field_simp

end RiemannResearch.RH.QHighConductorSlope
