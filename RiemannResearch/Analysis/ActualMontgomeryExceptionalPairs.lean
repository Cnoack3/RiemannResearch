/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryExceptionalPairs
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroTailDensityTransfer

/-!
# Actual zero copies and the exceptional-pair estimate

Lamzouri, *The distribution of small gaps between zeros of the Riemann zeta
function*, https://arxiv.org/html/2611.14486v1 , Lemma 2.3, supplies the
integer moment hypothesis on the microscopic Cauchy rows. His Lemma 2.1
supplies the companion horizontal exponential moment. We derive the latter
from the repository's Selberg density predicate with the finite endpoint
retained. The two independent analytic inputs are parameters to the result.
-/

noncomputable section
open Filter Set MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
open ActualZeroOrdinate MontgomeryExceptionalPairs

/-- Horizontal mark on the logarithmic scale used by Lamzouri. -/
def mark (T : ℝ) (i : Copies T) : ℝ := Real.log T * copyDisplacement T i

/-- Local ordinate weight, evaluated on individual analytic zero copies. -/
def gapWeight (T : ℝ) (i j : Copies T) : ℝ :=
  1 / (1 + ((i.1.1.im - j.1.1.im) * Real.log T) ^ 2)

theorem gapWeight_nonneg (T : ℝ) (i j : Copies T) : 0 ≤ gapWeight T i j := by
  unfold gapWeight
  positivity

theorem gapWeight_symm (T : ℝ) (i j : Copies T) : gapWeight T i j = gapWeight T j i := by
  unfold gapWeight
  congr 2
  ring

theorem one_le_gap_row (T : ℝ) (i : Copies T) : 1 ≤ rowMass Finset.univ (gapWeight T) i := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Copies T))) =>
    gapWeight_nonneg T i j) (Finset.mem_univ i)
  simpa [rowMass, gapWeight] using h

/-- Exact sum of the unit term and the finite layer-cake remainder. Critical
line copies contribute one even though the tail is defined with a strict cut. -/
theorem sum_exp_mark_identity (T b : ℝ) :
    (∑ i : Copies T, Real.exp (b * mark T i)) = (Ncount 0 T : ℝ) +
      badWeightedSum T 0 (fun x => Real.exp ((b * Real.log T) * x) - 1) := by
  classical
  have h1 : (Ncount 0 T : ℝ) = ∑ _i : Copies T, (1 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, mul_one]
  rw [h1]
  unfold badWeightedSum FiniteStrictTail.badSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < copyDisplacement T i
  · simp [mark, hi, mul_assoc]
  · have h0 : copyDisplacement T i = 0 :=
      le_antisymm (le_of_not_gt hi) (abs_nonneg _)
    simp [mark, h0]

/-- Finite-height version of Lamzouri's exponential moment, with the
upper-strip endpoint and constants explicit. -/
theorem normalized_exp_mark_le {T b a C c : ℝ} (hT : 1 < T)
    (hb : 0 ≤ b) (hba : b < a) (hC : 0 ≤ C) (hc : 0 < c)
    (hD : SelbergDensityBound T C a) (hN : c * T * Real.log T ≤ (Ncount 0 T : ℝ)) :
    (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ * Real.exp (b * mark T i)) ≤
      1 + (2 * C / c) * (b / (a-b)) *
        (1 - Real.exp (-((a-b) * Real.log T) / 2)) := by
  let l := b * Real.log T
  let q := a * Real.log T
  let K := 2 * C * T * Real.log T
  have hL : 0 < Real.log T := Real.log_pos hT
  have hT' : 0 < T := by linarith
  have hl : 0 ≤ l := mul_nonneg hb hL.le
  have hlq : l < q := mul_lt_mul_of_pos_right hba hL
  have hN' : 0 < (Ncount 0 T : ℝ) := (mul_pos (mul_pos hc hT') hL).trans_le hN
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbad := badWeightedSum_le_of_expTail T 0 K q
    (fun x => Real.exp (l * x)-1) (fun x => l*Real.exp (l*x))
    (by norm_num) (by fun_prop)
    (fun x => by
      simpa only [Function.comp_def, mul_one, one_mul, mul_comm] using
        (((Real.hasDerivAt_exp (l*x)).comp x ((hasDerivAt_id x).const_mul l)).sub_const 1))
    (by simp) (fun x _ => mul_nonneg hl (Real.exp_nonneg _))
    (fun x hx => strictTail_of_selbergDensity T C a x hT' hx hD)
  have hI : (∫ x in (0:ℝ)..1/2, Real.exp (-q*x)*(l*Real.exp (l*x))) =
      l * ((1 - Real.exp (-(q-l)/2))/(q-l)) := by
    have heq : (fun x : ℝ => Real.exp (-q*x)*(l*Real.exp (l*x))) =
        (fun x => l * Real.exp (-(q-l)*x)) := by
      funext x
      rw [mul_left_comm, ← Real.exp_add]
      ring_nf
    rw [heq, intervalIntegral.integral_const_mul,
      Real.integral_neg_exp 0 (1/2) (q-l) (sub_ne_zero.mpr hlq.ne')]
    simp [div_eq_mul_inv]
  rw [hI] at hbad
  simp only [mul_zero, Real.exp_zero, sub_self, zero_mul, zero_add] at hbad
  have he : 0 ≤ 1 - Real.exp (-(q-l)/2) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hmul : 0 ≤ l * ((1 - Real.exp (-(q-l)/2))/(q-l)) :=
    mul_nonneg hl (div_nonneg he (sub_pos.mpr hlq).le)
  have hK' : K ≤ (Ncount 0 T : ℝ) * (2*C/c) := by
    calc
      K = (c*T*Real.log T) * (2*C/c) := by dsimp [K]; field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hN (div_nonneg (by positivity) hc.le)
  rw [← Finset.mul_sum, sum_exp_mark_identity]
  have hrat : l * ((1 - Real.exp (-(q-l)/2))/(q-l)) =
      (b/(a-b)) * (1 - Real.exp (-((a-b)*Real.log T)/2)) := by
    have hdiff : q-l = (a-b)*Real.log T := by dsimp [q,l]; ring
    rw [hdiff]
    dsimp [l]
    field_simp [hL.ne', sub_ne_zero.mpr hba.ne']
    <;> ring
  have hx := hbad.trans (mul_le_mul_of_nonneg_right hK' hmul)
  rw [hrat] at hx
  calc
    _ ≤ (Ncount 0 T : ℝ)⁻¹ * ((Ncount 0 T : ℝ) +
        (Ncount 0 T : ℝ) * (2 * C / c) * ((b / (a-b)) * (1 - Real.exp (-((a-b) * Real.log T) / 2)))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hx) (inv_nonneg.mpr hN'.le)
    _ = _ := by
      rw [mul_add, inv_mul_cancel₀ hN'.ne']
      generalize (2 * C / c) = h
      generalize (b / (a - b)) = k
      generalize (1 - Real.exp (-((a-b) * Real.log T) / 2)) = z
      field_simp [hN'.ne'] <;> ring

/-- Literature assumption for the integer moments of microscopic row sums.
Lamzouri's Lemma 2.3 deduces it from Fujii's short-interval moment estimates. -/
def FujiiMicroscopicRowMoments : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
    (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ * (rowMass Finset.univ (gapWeight T) i) ^ k) ≤ C

theorem eventually_real_row_moment (h : FujiiMicroscopicRowMoments) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ * rowMass Finset.univ (gapWeight T) i ^ p) ≤ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt p
  have hk' : 1 ≤ k := by
    exact_mod_cast hp.trans hk.le
  obtain ⟨C, hC, hb⟩ := h k hk'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with T hT
  apply le_trans _ hT
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_gap_row T i) hk.le


open scoped Classical in
/-- Every strict exponent below the Conrey--Baluyot threshold is available
for the signed normalized deletion error. The error includes both ordered
cross terms and the exceptional self-pairs. The pointwise test-function
bound is explicit. Each occurrence is a separate summation index. -/
theorem eventually_signed_deletion_le
    (hDensity : ConreyBaluyotDensityHypothesis) (hRows : FujiiMicroscopicRowMoments)
    {θ κ A : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) (hgap : κ < 1 - 7 * θ / 4) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ (E : Finset (Copies T))
      (F : Copies T × Copies T → ℂ),
      (∀ e ∈ incident Finset.univ E, ‖F e‖ ≤ A *
        (((Ncount 0 T : ℝ)⁻¹ * gapWeight T e.1 e.2) *
        Real.exp (θ * (mark T e.1 + mark T e.2)))) →
      ‖(∑ e ∈ (Finset.univ : Finset (Copies T)) ×ˢ Finset.univ, F e) -
        (∑ e ∈ (Finset.univ \ E) ×ˢ (Finset.univ \ E), F e)‖ ≤
          B * ((E.card : ℝ) / (Ncount 0 T : ℝ)) ^ κ := by
  classical
  obtain ⟨p, q, r, t, hp, hq, hrt, hcrit, hκ'⟩ := exists_removal_exponents hθ hκ hgap
  let b := 2 * p * θ * r
  have hb : 0 < b := mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) hθ) hrt.pos
  obtain ⟨a, hba, ha⟩ := exists_between hcrit
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hDensity a (hb.trans hba) ha
  obtain ⟨Q, hQ, hQt⟩ := eventually_real_row_moment hRows q hq.le
  obtain ⟨R, hR, hRt⟩ := eventually_real_row_moment hRows t hrt.symm.lt.le
  let c : ℝ := 1 / (16 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  let D := 1 + (2 * C / c) * (b / (a - b))
  have hfactor : 0 ≤ (2 * C / c) * (b / (a - b)) :=
    mul_nonneg (div_nonneg (by positivity) hc.le) (div_nonneg hb.le (sub_pos.mpr hba).le)
  have hD0 : 0 ≤ D := by dsimp [D]; linarith
  let u := 1 - q⁻¹
  let v := 1 - p⁻¹
  let H := (D / r + R / t) ^ p⁻¹
  let B := A * ((2 * Q ^ q⁻¹) ^ v * H)
  have hH : 0 ≤ H := Real.rpow_nonneg (add_nonneg (div_nonneg hD0 hrt.pos.le)
    (div_nonneg hR hrt.symm.pos.le)) _
  have hB : 0 ≤ B := mul_nonneg hA (mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hQ _)) _) hH)
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, eventually_count_ge_log, hQt, hRt] with T hT hN hQt hRt
  intro E F hF
  have hT' : 1 < T := hT₀.trans_le hT
  have hN' : 0 < (Ncount 0 T : ℝ) :=
    (mul_pos (mul_pos hc (by linarith)) (Real.log_pos hT')).trans_le hN
  have hDm : (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ * Real.exp (b * mark T i)) ≤ D := by
    apply (normalized_exp_mark_le hT' hb.le hba hC hc (hD T hT) hN).trans
    dsimp [D]
    have hh : 1 - Real.exp (-((a-b)*Real.log T)/2) ≤ 1 := sub_le_self _ (Real.exp_nonneg _)
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hh hfactor).trans_eq (mul_one _))
  let δ : ℝ := E.card / (Ncount 0 T : ℝ)
  have hδ : (∑ _i ∈ E, (Ncount 0 T : ℝ)⁻¹) ≤ δ := by
    simp [δ, div_eq_mul_inv]
  by_cases he : E = ∅
  · subst E
    simpa using (mul_nonneg hB (Real.rpow_nonneg (show (0:ℝ) ≤ 0 by norm_num) κ))
  have hδ0 : 0 < δ := div_pos (by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)) hN'
  have hδ1 : δ ≤ 1 := by
    apply (div_le_iff₀ hN').mpr
    rw [one_mul, ← card_copies T]
    exact_mod_cast Finset.card_le_univ E
  have hx := norm_signed_deletion_le Finset.univ E (Finset.subset_univ E)
    (gapWeight T) (gapWeight_nonneg T) (gapWeight_symm T) (mark T) F
    (inv_nonneg.mpr hN'.le) hA hp.le hq.le hrt hδ hQt hDm hRt hF
  apply hx.trans
  have hpow : (2 * δ ^ u * Q ^ q⁻¹) ^ v = (2 * Q ^ q⁻¹) ^ v * δ ^ (u * v) := by
    rw [show 2 * δ ^ u * Q ^ q⁻¹ = (2 * Q ^ q⁻¹) * δ ^ u by ring,
      Real.mul_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hQ _))
        (Real.rpow_nonneg hδ0.le _), ← Real.rpow_mul hδ0.le]
  change A * ((2 * δ ^ u * Q ^ q⁻¹) ^ v * H) ≤ B * δ ^ κ
  rw [hpow, show A * (((2 * Q ^ q⁻¹) ^ v * δ ^ (u*v)) * H) = B * δ ^ (u*v) by dsimp [B]; ring]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hκ'.le) hB

end RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
