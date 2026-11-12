import RiemannResearch.RH.QMatchedShortHead
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.Analysis.ResidueOscillation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import RiemannResearch.RH.QHighConductorSlope
import RiemannResearch.RH.QFullCRTDisplacement
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual full-conductor short-head localization

Source: user-provided November 10 localization argument.
The low Schur pairing remains signed and unresolved. The exact decomposition,
uniformly vanishing remainder, and bounded high-conductor contribution
are independent of RH. The November 12 extension identifies the exact fixed-pair
limit and weakens the sufficient common-bound hypothesis to pairwise frequent
control. It does not supply that common arithmetic bound.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullShortHeadLocalization
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QSquarefreeCorrectionKernel
open QFiniteSupportDualCriterion QAnnihilatorTailEscape
open QMatchedResidualTails QMatchedOscillationKernel QMatchedShortHead QHighConductorSlope
open QFullDivisorProjection QSquarefreeLatticePackets
open RiemannResearch.Analysis.ResidualizedProjectionKernel
open RiemannResearch.Analysis.NestedOrthogonalDecomposition
open RiemannResearch.Analysis.SublinearTailCutoff

def highStage (L : ℕ+) (H : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (qResidue '' {q | q ∈ (L : ℕ).divisors ∧ H < q})

instance highStage_finiteDimensional (L : ℕ+) (H : ℕ) :
    FiniteDimensional ℝ (highStage L H) := by
  apply FiniteDimensional.span_of_finite
  exact (((L : ℕ).divisors.finite_toSet).subset (fun _ h => h.1)).image qResidue

theorem highStage_le (L : ℕ+) (H : ℕ) :
    highStage L H ≤ divisorStage (L : ℕ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, hq, rfl⟩
  exact Submodule.subset_span ⟨q, (Nat.mem_divisors.mp hq.1).1, rfl⟩

theorem highStage_linear (L : ℕ+) (H : ℕ) (hH : 1 ≤ H) :
    HasLinearHead (highStage L H) H :=
  high_span_linear _ H hH (fun _ h => h.2)

theorem actual_slope_bound (L : ℕ+) (H : ℕ) (hH : 0 < H) :
    slopeEnergy (highStage L H) ≤ zetaTwo / H :=
  slopeEnergy_le _ H hH (highStage_linear L H hH)

theorem signedHead_sub (A : ℕ) (r : ThresholdHilbert) (f g : QHilbert) :
    signedHead A r (f - g) = signedHead A r f - signedHead A r g := by
  simp only [signedHead, inner_finiteHead_eq_sum, toPareto_sub, map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (reciprocalD (toPareto f) i - reciprocalD (toPareto g) i) * r i =
    reciprocalD (toPareto f) i * r i - reciprocalD (toPareto g) i * r i
  ring

theorem high_head_exact (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (H A : ℕ) (hlin : HasLinearHead U H) (hA : A ≤ H)
    (r : ThresholdHilbert) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    signedHead A r (pairKernel U n m) =
      ((n : ℝ) - m) * slopeEnergy U * inner ℝ r (finiteHead A hilbertOne) := by
  rw [signedHead, inner_finiteHead_eq_sum, inner_finiteHead_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiH : i + 1 ≤ H := (Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans hA
  have hval : qSequence (pairKernel U n m) (i + 1) =
      ((n : ℝ) - m) * ((i + 1 : ℕ) : ℝ) * slopeEnergy U := by
    rw [pairKernel_eq_slope U H hlin n m hn hm]
    have hsm := congrFun (qSequenceLinear.map_smul ((n : ℝ) - m)
      (slopeRepresenter U)) (i + 1)
    change qSequence (((n : ℝ) - m) • slopeRepresenter U) (i + 1) =
      ((n : ℝ) - m) * qSequence (slopeRepresenter U) (i + 1) at hsm
    rw [hsm, slope_physical U H hlin (i + 1) hiH]
    ring
  rw [reciprocalD_apply]
  change (Real.sqrt (paretoWeight i) * qSequence (pairKernel U n m) (i + 1) /
      ((i : ℝ) + 1)) * r i =
    ((n : ℝ) - m) * slopeEnergy U *
      ((Real.sqrt (paretoWeight i) * zeroAnchor (fun _ => (1 : ℝ)) (i + 1)) * r i)
  rw [hval]
  simp only [zeroAnchor, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    if_false, mul_one, Nat.cast_add, Nat.cast_one]
  field_simp

theorem head_mean_bound (A : ℕ) (r : ThresholdHilbert) :
    |inner ℝ r (finiteHead A hilbertOne)| ≤ ‖r‖ := by
  have ho : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  calc
    _ ≤ ‖r‖ * ‖finiteHead A hilbertOne‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖r‖ * ‖hilbertOne‖ :=
      mul_le_mul_of_nonneg_left (finiteHead_norm_le A hilbertOne) (norm_nonneg r)
    _ = ‖r‖ := by rw [ho, mul_one]

theorem high_head_bound (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (H A : ℕ) (hH : 0 < H) (hlin : HasLinearHead U H) (hA : A ≤ H)
    (r : ThresholdHilbert) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    |signedHead A r (pairKernel U n m)| ≤ zetaTwo * ‖r‖ := by
  have hZ := zetaTwo_pos
  have hnR : (n : ℝ) ≤ H := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ H := by exact_mod_cast hm
  have hnm : |(n : ℝ) - m| ≤ H := by
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
  have ha : 0 ≤ slopeEnergy U := sq_nonneg _
  have hb := slopeEnergy_le U H hH hlin
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hb' := (le_div_iff₀ hp).mp hb
  have hc : |(n : ℝ) - m| * slopeEnergy U ≤ zetaTwo := by
    nlinarith [mul_le_mul_of_nonneg_right hnm ha]
  rw [high_head_exact U H A hlin hA r n m hn hm, abs_mul, abs_mul,
    abs_of_nonneg ha]
  exact mul_le_mul hc (head_mean_bound A r) (abs_nonneg _) hZ.le

/-- This vector is the Q projection onto the residualized low space. -/
theorem remaining_kernel_mem (S U : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] [U.HasOrthogonalProjection] (hUS : U ≤ S)
    (n m : ℕ) :
    pairKernel S n m - pairKernel U n m ∈ S ⊓ Uᗮ :=
  projection_difference_mem hUS _

theorem remaining_kernel_eq_projection (S U : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] [U.HasOrthogonalProjection]
    [(S ⊓ Uᗮ).HasOrthogonalProjection] (hUS : U ≤ S) (n m : ℕ) :
    pairKernel S n m - pairKernel U n m =
      (S ⊓ Uᗮ).starProjection (evaluation n - evaluation m) :=
  (carry_projection_apply hUS _).symm

/-- Every signed off-diagonal Gram entry survives the high-space elimination. -/
theorem residualized_gram_entry (U : Submodule ℝ QHilbert)
    [U.HasOrthogonalProjection] (f g : QHilbert) :
    inner ℝ (f - U.starProjection f) (g - U.starProjection g) =
      inner ℝ f g - inner ℝ (U.starProjection f) (U.starProjection g) := by
  have hf : U.starProjection (U.starProjection f) = U.starProjection f :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem f)
  have hg : U.starProjection (U.starProjection g) = U.starProjection g :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem g)
  have h1 := projection_inner U f (U.starProjection g)
  rw [hg] at h1
  have h2 := projection_inner U (U.starProjection f) g
  rw [hf] at h2
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem matchedResidual_orthogonal (L : ℕ+) :
    matchedResidual L ∈ (paretoStage L)ᗮ := by
  have he : matchedResidual L =
      toPareto qOne - (paretoStage L).starProjection (toPareto qOne) := by
    simp only [matchedResidual, pOptimizer, toPareto_sub, toPareto_pFit]
  rw [he]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- Exact decomposition for actual matched fits, with no estimated cross term. -/
theorem actual_head_tail (L : ℕ+) (A n m : ℕ) :
    zetaTwo * (qSequence (QFullDivisorProjection.displacement L) n -
      qSequence (QFullDivisorProjection.displacement L) m) =
    signedHead A (matchedResidual L) (pairKernel (divisorStage (L : ℕ)) n m) +
    signedTail A (matchedResidual L) (pairKernel (divisorStage (L : ℕ)) n m) := by
  have he := matched_pair_identity (divisorStage (L : ℕ)) (paretoStage L)
    (toPareto_mem_stage_iff L) qOne n m
  change zetaTwo * (qSequence (QFullDivisorProjection.displacement L) n -
    qSequence (QFullDivisorProjection.displacement L) m) =
    inner ℝ (matchedResidual L)
      (screenReciprocal (paretoStage L) (pairKernel (divisorStage (L : ℕ)) n m)) at he
  rw [he]
  exact screened_signed_head_tail _ A _ (matchedResidual_orthogonal L) _

def physicalCutoff (L : ℕ → ℕ+) (H : ℕ) : ℕ :=
  cutoff (tailEnvelope (fun j => matchedResidual (L j))) H

def remainderBound (L : ℕ → ℕ+) (H : ℕ) : ℝ :=
  zetaTwo * Real.sqrt 2 * ((H : ℝ) *
    tailEnvelope (fun j => matchedResidual (L j)) (physicalCutoff L H) /
      Real.sqrt (((physicalCutoff L H : ℝ) + 1) * ((physicalCutoff L H : ℝ) + 2)))

theorem actual_localization_bound (L : ℕ → ℕ+) (H n m j : ℕ)
    (hn : n ≤ H) (hm : m ≤ H) :
    |zetaTwo * (qSequence (QFullDivisorProjection.displacement (L j)) n -
      qSequence (QFullDivisorProjection.displacement (L j)) m) -
      signedHead (physicalCutoff L H) (matchedResidual (L j))
        (pairKernel (divisorStage (L j : ℕ)) n m)| ≤ remainderBound L H := by
  rw [actual_head_tail (L j) (physicalCutoff L H) n m, add_sub_cancel_left]
  exact signedTail_bound _ (fun j => matchedResidual_norm_le_one (L j))
    _ H (physicalCutoff L H) n m j hn hm

theorem localization_limits (L : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (L i : ℕ) ∣ (L j : ℕ))
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    Tendsto (physicalCutoff L) atTop atTop ∧
    Tendsto (fun H : ℕ => (physicalCutoff L H : ℝ) / H) atTop (𝓝 0) ∧
    (∀ᶠ H in atTop, physicalCutoff L H ≤ H) ∧
    Tendsto (remainderBound L) atTop (𝓝 0) := by
  have hρ := matched_tailEnvelope_tendsto L hnest hcofinal
  refine ⟨cutoff_tendsto _, cutoff_sublinear _ hρ, cutoff_eventually_le_head _ hρ, ?_⟩
  exact uniform_signedTail_tendsto_bound _ _ (matchedResidual_tendsto L hnest hcofinal)
    (fun j => matchedResidual_norm_le_one (L j))

/-- High slope + signed residualized low head + complete signed tail. -/
theorem actual_three_term_split (L : ℕ+) (H A n m : ℕ) (hH : 1 ≤ H)
    (hA : A ≤ H) (hn : n ≤ H) (hm : m ≤ H) :
    zetaTwo * (qSequence (QFullDivisorProjection.displacement L) n -
      qSequence (QFullDivisorProjection.displacement L) m) =
    ((n : ℝ) - m) * slopeEnergy (highStage L H) *
      inner ℝ (matchedResidual L) (finiteHead A hilbertOne) +
    signedHead A (matchedResidual L)
      (pairKernel (divisorStage (L : ℕ)) n m - pairKernel (highStage L H) n m) +
    signedTail A (matchedResidual L) (pairKernel (divisorStage (L : ℕ)) n m) := by
  rw [actual_head_tail L A n m, signedHead_sub,
    ← high_head_exact (highStage L H) H A (highStage_linear L H hH) hA _ n m hn hm]
  ring


/-- Vanishing of the signed remainder for arbitrary moving stages and sites.
The stage selector need not be monotone or tend to infinity. -/
theorem signed_remainder_tendsto (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (j n m : ℕ → ℕ) (hn : ∀ H, n H ≤ H) (hm : ∀ H, m H ≤ H) :
    Tendsto (fun H => signedTail (physicalCutoff R H) (matchedResidual (R (j H)))
      (pairKernel (divisorStage (R (j H) : ℕ)) (n H) (m H))) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (localization_limits R hnest hcofinal).2.2.2
  intro H
  simpa only [Real.norm_eq_abs, remainderBound] using
    signedTail_bound (fun j => matchedResidual (R j))
      (fun j => matchedResidual_norm_le_one (R j))
      (divisorStage (R (j H) : ℕ)) H (physicalCutoff R H) (n H) (m H) (j H)
      (hn H) (hm H)

/-- Conditional research reduction. ONLY the signed residualized short-head
pairing is an open arithmetic hypothesis; the high part and tail have providers. -/
theorem riemannHypothesis_of_short_schur_bound
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (C : ℝ)
    (hSchur : ∀ᶠ j in atTop, ∀ n m, 0 < n → 0 < m → n ≤ H j → m ≤ H j →
      n % L = m % L →
      |signedHead (physicalCutoff R (H j)) (matchedResidual (R j))
        (pairKernel (divisorStage (R j : ℕ)) n m -
          pairKernel (highStage (R j) (H j)) n m)| ≤ C) :
    RiemannHypothesis := by
  apply QFullCRTDisplacement.riemannHypothesis_of_finite_residue_oscillation
    L hL ((zetaTwo + C + 1) / zetaTwo)
  intro n m hn hm hnm
  have ht := QFullDivisorProjection.displacement_tendsto R hnest hcofinal
  have hlim := ((qSequence_tendsto_of_tendsto ht n).sub
    (qSequence_tendsto_of_tendsto ht m)).abs
  have hloc := localization_limits R hnest hcofinal
  have htail : ∀ᶠ j in atTop, remainderBound R (H j) < 1 :=
    (hloc.2.2.2.comp hH).eventually_lt_const (by norm_num)
  have hcut := hH.eventually hloc.2.2.1
  apply le_of_tendsto hlim
  filter_upwards [htail, hcut, hH.eventually (eventually_ge_atTop n),
    hH.eventually (eventually_ge_atTop m), hH.eventually (eventually_ge_atTop 1), hSchur]
    with j htailj hcutj hnj hmj hpos hSchurj
  have he := actual_three_term_split (R j) (H j) (physicalCutoff R (H j))
    n m hpos hcutj hnj hmj
  have hh := high_head_bound (highStage (R j) (H j)) (H j) (physicalCutoff R (H j))
    hpos (highStage_linear (R j) (H j) hpos) hcutj (matchedResidual (R j)) n m hnj hmj
  rw [high_head_exact _ _ _ (highStage_linear (R j) (H j) hpos) hcutj
    (matchedResidual (R j)) n m hnj hmj] at hh
  have hhigh : |((n : ℝ) - m) * slopeEnergy (highStage (R j) (H j)) *
      inner ℝ (matchedResidual (R j)) (finiteHead (physicalCutoff R (H j)) hilbertOne)| ≤
      zetaTwo := by
    exact hh.trans (by nlinarith [matchedResidual_norm_le_one (R j), zetaTwo_pos])
  have hlow := hSchurj n m hn hm hnj hmj hnm
  have htailb := signedTail_bound (fun j => matchedResidual (R j))
    (fun j => matchedResidual_norm_le_one (R j)) (divisorStage (R j : ℕ))
    (H j) (physicalCutoff R (H j)) n m j hnj hmj
  change |signedTail (physicalCutoff R (H j)) (matchedResidual (R j))
    (pairKernel (divisorStage (R j : ℕ)) n m)| ≤ remainderBound R (H j) at htailb
  have hab := congrArg abs he
  rw [abs_mul, abs_of_pos zetaTwo_pos] at hab
  have htri := (abs_add_le
    (((n : ℝ) - m) * slopeEnergy (highStage (R j) (H j)) *
      inner ℝ (matchedResidual (R j)) (finiteHead (physicalCutoff R (H j)) hilbertOne) +
      signedHead (physicalCutoff R (H j)) (matchedResidual (R j))
        (pairKernel (divisorStage (R j : ℕ)) n m -
          pairKernel (highStage (R j) (H j)) n m))
    (signedTail (physicalCutoff R (H j)) (matchedResidual (R j))
      (pairKernel (divisorStage (R j : ℕ)) n m))).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  apply (le_div_iff₀ zetaTwo_pos).mpr
  nlinarith


/-- Keep the fixed physical separation instead of bounding it by the growing head. -/
theorem high_head_pair_bound (U : Submodule ℝ QHilbert)
    [U.HasOrthogonalProjection] (H A : ℕ) (hH : 0 < H)
    (hlin : HasLinearHead U H) (hA : A ≤ H)
    (r : ThresholdHilbert) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    |signedHead A r (pairKernel U n m)| ≤
      |(n : ℝ) - m| * (zetaTwo / H) * ‖r‖ := by
  rw [high_head_exact U H A hlin hA r n m hn hm, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ slopeEnergy U from sq_nonneg _)]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (slopeEnergy_le U H hH hlin) (abs_nonneg _))
    (head_mean_bound A r) (abs_nonneg _)
    (mul_nonneg (abs_nonneg _) (div_nonneg zetaTwo_pos.le (Nat.cast_nonneg H)))

/-- The actual signed residualized low-head term, with the canonical physical cutoff. -/
def shortSchur (R : ℕ → ℕ+) (j H n m : ℕ) : ℝ :=
  signedHead (physicalCutoff R H) (matchedResidual (R j))
    (pairKernel (divisorStage (R j : ℕ)) n m -
      pairKernel (highStage (R j) H) n m)

/-- Exact signed finite identity; neither the high term nor the tail is discarded. -/
theorem shortSchur_exact (R : ℕ → ℕ+) (j H n m : ℕ) :
    shortSchur R j H n m =
      zetaTwo * (qSequence (QFullDivisorProjection.displacement (R j)) n -
        qSequence (QFullDivisorProjection.displacement (R j)) m) -
      signedHead (physicalCutoff R H) (matchedResidual (R j))
        (pairKernel (highStage (R j) H) n m) -
      signedTail (physicalCutoff R H) (matchedResidual (R j))
        (pairKernel (divisorStage (R j : ℕ)) n m) := by
  rw [shortSchur, signedHead_sub, actual_head_tail]
  ring

/-- At fixed sites the high-conductor contribution vanishes, with no residual decay rate. -/
theorem high_head_fixed_pair_tendsto (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (n m : ℕ) :
    Tendsto (fun j => signedHead (physicalCutoff R (H j)) (matchedResidual (R j))
      (pairKernel (highStage (R j) (H j)) n m)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun j => zetaTwo / (H j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hH)
  have hb : Tendsto (fun j => |(n : ℝ) - m| * (zetaTwo / (H j : ℝ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hdiv.const_mul |(n : ℝ) - m|
  apply squeeze_zero_norm' _ hb
  filter_upwards [hH.eventually (localization_limits R hnest hcofinal).2.2.1,
    hH.eventually (eventually_ge_atTop 1), hH.eventually (eventually_ge_atTop n),
    hH.eventually (eventually_ge_atTop m)] with j hA hpos hn hm
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |(n : ℝ) - m| * (zetaTwo / H j) * ‖matchedResidual (R j)‖ :=
      high_head_pair_bound _ _ _ hpos (highStage_linear (R j) (H j) hpos)
        hA _ n m hn hm
    _ ≤ |(n : ℝ) - m| * (zetaTwo / H j) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (matchedResidual_norm_le_one (R j))
        (mul_nonneg (abs_nonneg _) (div_nonneg zetaTwo_pos.le (Nat.cast_nonneg _)))

/-- The complete signed tail vanishes at every fixed pair along any cofinal heads. -/
theorem tail_fixed_pair_tendsto (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (n m : ℕ) :
    Tendsto (fun j => signedTail (physicalCutoff R (H j)) (matchedResidual (R j))
      (pairKernel (divisorStage (R j : ℕ)) n m)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ ((localization_limits R hnest hcofinal).2.2.2.comp hH)
  filter_upwards [hH.eventually (eventually_ge_atTop n),
    hH.eventually (eventually_ge_atTop m)] with j hn hm
  simpa only [Real.norm_eq_abs, Function.comp_apply, remainderBound] using
    signedTail_bound (fun j => matchedResidual (R j))
      (fun j => matchedResidual_norm_le_one (R j))
      (divisorStage (R j : ℕ)) (H j) (physicalCutoff R (H j)) n m j hn hm

/-- Unconditional pointwise limit of the actual signed Schur term. This is not a
uniform estimate over a growing set of pairs and does not assume the residual is zero. -/
theorem shortSchur_tendsto (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (n m : ℕ) :
    Tendsto (fun j => shortSchur R j (H j) n m) atTop
      (𝓝 (zetaTwo * (qSequence QFullDisplacement.displacement n -
        qSequence QFullDisplacement.displacement m))) := by
  have hd := QFullDivisorProjection.displacement_tendsto R hnest hcofinal
  have hd' := ((qSequence_tendsto_of_tendsto hd n).sub
    (qSequence_tendsto_of_tendsto hd m)).const_mul zetaTwo
  simpa only [shortSchur_exact, sub_zero] using
    (hd'.sub (high_head_fixed_pair_tendsto R hnest hcofinal H hH n m)).sub
      (tail_fixed_pair_tendsto R hnest hcofinal H hH n m)

/-- A common bound at arbitrarily late stages for each fixed pair passes to the
limit with constant C/zeta(2), without an additive high-part or tail allowance. -/
theorem residue_oscillation_of_frequent_shortSchur_bound (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (L : ℕ) (C : ℝ)
    (hSchur : ∀ n m, 0 < n → 0 < m → n % L = m % L →
      ∃ᶠ j in atTop, |shortSchur R j (H j) n m| ≤ C) :
    RiemannResearch.Analysis.ResidueOscillation.Bound
      (qSequence QFullDisplacement.displacement) L (C / zetaTwo) := by
  intro n m hn hm hnm
  have hb := le_of_tendsto_of_frequently
    (shortSchur_tendsto R hnest hcofinal H hH n m).abs (hSchur n m hn hm hnm)
  rw [abs_mul, abs_of_pos zetaTwo_pos] at hb
  exact (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)

/-- Conditional research reduction. The good stages may depend on the pair, but
one constant C must work for every positive congruent pair. This common-C provider
remains an open arithmetic obligation; simultaneous growing-window bounds are unnecessary. -/
theorem riemannHypothesis_of_frequent_shortSchur_bound (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (C : ℝ)
    (hSchur : ∀ n m, 0 < n → 0 < m → n % L = m % L →
      ∃ᶠ j in atTop, |shortSchur R j (H j) n m| ≤ C) :
    RiemannHypothesis :=
  QFullCRTDisplacement.riemannHypothesis_of_finite_residue_oscillation L hL
    (C / zetaTwo)
    (residue_oscillation_of_frequent_shortSchur_bound R hnest hcofinal H hH L C hSchur)

/-- The weaker common-C condition is equivalent to zero actual full Q residual.
Neither side is supplied unconditionally by this equivalence. -/
theorem residual_zero_iff_frequent_shortSchur_bound (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (L : ℕ) (hL : 0 < L) :
    QFullDisplacement.qResidual = 0 ↔
      ∃ C : ℝ, ∀ n m, 0 < n → 0 < m → n % L = m % L →
        ∃ᶠ j in atTop, |shortSchur R j (H j) n m| ≤ C := by
  constructor
  · intro hr
    refine ⟨1, ?_⟩
    intro n m _ _ _
    have ht := (shortSchur_tendsto R hnest hcofinal H hH n m).abs
    rw [QFullDisplacement.displacement_eq_zero_of_qResidual_eq_zero hr] at ht
    simp only [show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear,
      Pi.zero_apply, sub_self, mul_zero, abs_zero] at ht
    exact ((ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono
      (fun _ h => h.le)).frequently
  · rintro ⟨C, hC⟩
    exact (QFullCRTDisplacement.residual_zero_iff_finite_residue_oscillation L hL).mpr
      ⟨C / zetaTwo,
        residue_oscillation_of_frequent_shortSchur_bound R hnest hcofinal H hH L C hC⟩

/-- If RH fails, each proposed bound is eventually exceeded at one fixed pair.
The pair may depend on the bound; this does not claim divergence at a single pair. -/
theorem fixed_pair_escape_of_not_riemannHypothesis (R : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hRH : ¬ RiemannHypothesis) (L : ℕ) (hL : 0 < L) (C : ℝ) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n % L = m % L ∧
      ∀ᶠ j in atTop, C < |shortSchur R j (H j) n m| := by
  obtain ⟨n, m, hn, hm, hnm, hb⟩ :=
    QFullCRTDisplacement.unbounded_oscillation_of_not_riemannHypothesis
      hRH L hL (C / zetaTwo)
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  apply (shortSchur_tendsto R hnest hcofinal H hH n m).abs.eventually
  apply Ioi_mem_nhds
  rw [abs_mul, abs_of_pos zetaTwo_pos]
  have hc := (div_lt_iff₀ zetaTwo_pos).mp hb
  nlinarith


end RiemannResearch.RH.QFullShortHeadLocalization
