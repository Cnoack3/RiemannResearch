/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodDensity
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualSelbergDyadicAssembly
import RiemannResearch.Analysis.ActualZeroDensityWindow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The transition window between the total count and the Ingham profile

The actual inclusive count is bounded by the minimum of the total-count and
Gabriel–Littlewood Ingham estimates in `ActualInghamLittlewoodDensity`. We identify where the
second majorant already gives the one-log Selberg profile. For any fixed
nonnegative slope below `4 / 3`, the uniform density input can be restricted to
`A < (σ-1 / 2) log T < 2 log log T / (4 / 3-a)`. The constants outside this
window are uniform in both variables. The bound inside it is an explicit
analytic hypothesis.

For the Ingham and Selberg normalizations see Chourasiya and Simonič,
<https://arxiv.org/abs/2507.15184>, and Baluyot, *On the Zeros of Riemann's
Zeta-function* (2017), §3.6.
-/

noncomputable section
open Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Exact comparison of the two positive profiles after taking logarithms.
The two surplus logarithms at the left edge are retained by `1+q`. -/
theorem ingham_profile_le_selberg_iff {T q a σ : ℝ} (hT : 1 < T) :
    T ^ q * (Real.log T) ^ (2 + q) ≤ T ^ (1 - a * (σ - 1 / 2)) * Real.log T ↔
      (1 + q) * Real.log (Real.log T) ≤
        (1 - q - a * (σ - 1 / 2)) * Real.log T := by
  have hT₀ : 0 < T := by linarith
  have hL := Real.log_pos hT
  have hs : T ^ (1 - a * (σ - 1 / 2)) * Real.log T =
      Real.exp (Real.log T * (1 - a * (σ - 1 / 2)) + Real.log (Real.log T)) := by
    rw [Real.exp_add, Real.exp_log hL, Real.rpow_def_of_pos hT₀]
  rw [hs, Real.rpow_def_of_pos hT₀, Real.rpow_def_of_pos hL,
    ← Real.exp_add, Real.exp_le_exp]
  constructor <;> intro h <;> nlinarith only [h]

/-- One absolute constant works for every height at least two and every slope
where the exact Ingham-to-Selberg profile comparison holds. -/
theorem exists_selberg_count_of_ingham_profile_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1, ∀ a : ℝ,
      let q := 3 * (1 - σ) / (2 - σ)
      (1 + q) * Real.log (Real.log T) ≤ (1 - q - a * (σ - 1 / 2)) * Real.log T →
        rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  obtain ⟨C, hC, hc⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ a q hcomp
  have hs := (ingham_profile_le_selberg_iff (show 1 < T by linarith)).mpr hcomp
  rw [mul_assoc]
  exact (hc T hT σ hσ).trans (mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans hs) hC.le)

/-- Exact real-part range on which the proved Ingham profile pays for a
single logarithm at its tangent slope. Equality is allowed on the boundary. -/
theorem ingham_profile_le_four_thirds_iff {T σ : ℝ} (hT : 1 < T)
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    let q := 3 * (1 - σ) / (2 - σ)
    T ^ q * (Real.log T) ^ (2 + q) ≤ T ^ (1 - (4 / 3 : ℝ) * (σ - 1 / 2)) * Real.log T ↔
      (5 - 4 * σ) * Real.log (Real.log T) ≤ (4 / 3 : ℝ) * (σ - 1 / 2) ^ 2 * Real.log T := by
  dsimp only
  rw [ingham_profile_le_selberg_iff hT]
  have hd : 0 < 2 - σ := by linarith only [hσ.2]
  have hl : (2 - σ) * (1 + 3 * (1 - σ) / (2 - σ)) = 5 - 4 * σ := by
    field_simp [hd.ne']
    <;> ring
  have hr : (2 - σ) * (1 - 3 * (1 - σ) / (2 - σ) - (4 / 3) * (σ - 1 / 2)) =
      (4 / 3) * (σ - 1 / 2) ^ 2 := by
    field_simp [hd.ne']
    <;> ring
  rw [← mul_le_mul_iff_right₀ hd, ← mul_assoc, hl, ← mul_assoc, hr]

/-- A single unconditional constant works on this moving region, including
every fixed real-part threshold strictly above one half at large heights. -/
theorem exists_one_log_four_thirds_on_ingham_region :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      (5 - 4 * σ) * Real.log (Real.log T) ≤ (4 / 3 : ℝ) * (σ - 1 / 2) ^ 2 * Real.log T →
      rightInclusiveCount T σ ≤ C * T ^ (1 - (4 / 3 : ℝ) * (σ - 1 / 2)) * Real.log T := by
  obtain ⟨C, hC, hcount⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ hregion
  have hcmp := (ingham_profile_le_four_thirds_iff (by linarith : 1 < T) hσ).2 hregion
  rw [mul_assoc]
  exact (hcount T hT σ hσ).trans
    (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hcmp) hC.le)

/-- The dyadic specialization of the curved one-log estimate in rStation
paper 184/v1 (2026), Theorem 1, with η₀ = 1. Its fourth-moment and
coefficient estimates are external analytic inputs.
<https://rstation.ai/problems/riemann_hypothesis/papers/184> -/
def DyadicInghamOneLog : Prop :=
  ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧ ∀ S : ℝ, H ≤ S → ∀ σ ∈ Ico (1 / 2 : ℝ) 1,
    rightInclusiveWindow S (2 * S) σ ≤ C * S ^ (3 * (1 - σ) / (2 - σ)) * Real.log S

/-- A dyadic Ingham exponent with one logarithm, uniform up to the critical
line, would give the global one-logarithm slope 4/3. The window hypothesis
is stated at its lower height, allows equality at σ, and omits the empty
threshold σ = 1. -/
theorem uniformSelbergDensity_four_thirds_of_dyadic_ingham_one_log
    (hw : DyadicInghamOneLog) :
    UniformSelbergDensity (4 / 3) := by
  obtain ⟨C, H, hC, hH, hb⟩ := hw
  apply uniformSelbergDensity_of_dyadic_windows (by norm_num) (by norm_num)
  refine ⟨C, H, hC, hH, ?_⟩
  intro T hT σ hσ
  have hS : H ≤ T / 2 := by linarith only [hT]
  have hS₁ : 1 < T / 2 := hH.trans_le hS
  have hST : T / 2 ≤ T := by linarith only [hS₁]
  have hT₁ : 1 ≤ T := hS₁.le.trans hST
  by_cases hs : σ < 1
  · have hbound := hb (T / 2) hS σ ⟨hσ.1, hs⟩
    rw [show 2 * (T / 2) = T by ring] at hbound
    have hd : 0 < 2 - σ := by linarith only [hσ.2]
    have hq : 0 ≤ 3 * (1 - σ) / (2 - σ) := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hσ.2)) hd.le
    have htangent : 3 * (1 - σ) / (2 - σ) ≤ 1 - (4 / 3 : ℝ) * (σ - 1 / 2) := by
      apply (div_le_iff₀ hd).mpr
      nlinarith only [sq_nonneg (σ - 1 / 2)]
    have hpow := (Real.rpow_le_rpow (zero_lt_one.trans hS₁).le hST hq).trans
      (Real.rpow_le_rpow_of_exponent_le hT₁ htangent)
    exact hbound.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hC) (Real.log_le_log (zero_lt_one.trans hS₁) hST)
      (Real.log_nonneg hS₁.le) (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hT₁) _)))
  · have he : σ = 1 := le_antisymm hσ.2 (le_of_not_gt hs)
    subst σ
    have hz : rightInclusiveWindow (T / 2) T 1 = 0 := by
      unfold rightInclusiveWindow realSum
      apply Finset.sum_eq_zero
      intro ρ hρ
      have hβ : ρ.re < 1 := (mem_cutoff.mp hρ).1.2.2
      simp [not_le_of_gt hβ]
    rw [hz]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hT₁) _))
      (Real.log_nonneg hT₁)

/-- The true count has a one-logarithm bound on both sides of the transition
window. The second region shrinks toward the critical line as height grows. -/
theorem exists_selberg_count_outside_transition {a : ℝ} (A : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 4 / 3) :
    ∃ C H : ℝ, 0 < C ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      ((σ - 1 / 2) * Real.log T ≤ A ∨
        2 * Real.log (Real.log T) ≤ (4 / 3 - a) * ((σ - 1 / 2) * Real.log T)) →
        rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  obtain ⟨B, hB, hsmall⟩ := exists_selberg_form_on_logarithmic_strip a A ha
  obtain ⟨F, hF, hfar⟩ := exists_selberg_count_of_ingham_profile_comparison
  refine ⟨max B F, max 9 (Real.exp 1), hB.trans_le (le_max_left _ _),
    (by linarith only [le_max_left (9 : ℝ) (Real.exp 1)]), ?_⟩
  intro T hT σ hσ hc
  have h9 := (le_max_left (9 : ℝ) (Real.exp 1)).trans hT
  have hT₀ : 0 < T := by linarith
  have hL : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  have hℓ := Real.log_nonneg hL
  have hm (b : ℝ) (hb : b ≤ max B F) :
      b * T ^ (1 - a * (σ - 1 / 2)) * Real.log T ≤
        max B F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hT₀.le _)) (by linarith)
  rcases hc with hs | hf
  · exact (hsmall T h9 σ hs).trans (hm B (le_max_left _ _))
  · let q := 3 * (1 - σ) / (2 - σ)
    have hq : q ≤ 1 := by
      apply (div_le_iff₀ (by linarith [hσ.2] : 0 < 2-σ)).mpr
      linarith [hσ.1]
    have hg := ingham_exponent_add_gap_le (η := σ - 1 / 2) ha'
      (sub_nonneg.mpr hσ.1) (show σ ∈ Icc (1 / 2 + (σ - 1 / 2)) 1 from ⟨by linarith, hσ.2⟩)
    have hdiff : (4 / 3 - a) * (σ - 1 / 2) ≤ 1 - q - a * (σ - 1 / 2) := by
      dsimp [q]; linarith only [hg]
    have hcomp : (1 + q) * Real.log (Real.log T) ≤
        (1 - q - a * (σ - 1 / 2)) * Real.log T := by
      calc
        _ ≤ 2 * Real.log (Real.log T) :=
          mul_le_mul_of_nonneg_right (by linarith) hℓ
        _ ≤ (4 / 3 - a) * ((σ - 1 / 2) * Real.log T) := hf
        _ = ((4 / 3 - a) * (σ - 1 / 2)) * Real.log T := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hdiff (by linarith)
    exact (hfar T (by linarith) σ hσ a hcomp).trans (hm F (le_max_right _ _))

/-- Uniform Selberg density reduces exactly to the intermediate range. At
every slope below `4 / 3` the upper end of this range is `O(log log T)` in the
coordinate `(σ-1 / 2) log T`. -/
theorem uniformSelbergDensity_iff_transition {a : ℝ} (A : ℝ)
    (ha : 0 ≤ a) (ha' : a < 4 / 3) :
    UniformSelbergDensity a ↔
      ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
        A < (σ - 1 / 2) * Real.log T →
        (4 / 3 - a) * ((σ - 1 / 2) * Real.log T) < 2 * Real.log (Real.log T) →
        rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  constructor
  · rintro ⟨C, H, hC, hH, h⟩
    exact ⟨C, H, hC, hH, fun T hT σ hσ _ _ => h T hT σ hσ⟩
  · rintro ⟨B, K, hB, hK, hm⟩
    obtain ⟨F, H, hF, hH, ho⟩ := exists_selberg_count_outside_transition A ha ha'.le
    refine ⟨max B F, max K H, hB.trans (le_max_left _ _), hK.trans_le (le_max_left _ _), ?_⟩
    intro T hT σ hσ
    have hTK := (le_max_left K H).trans hT
    have hTH := (le_max_right K H).trans hT
    have hT₀ : 0 < T := by linarith
    have hℓ := (Real.log_pos (hK.trans_le hTK)).le
    have hinc (c : ℝ) (hc : c ≤ max B F) :
        c * T ^ (1 - a * (σ - 1 / 2)) * Real.log T ≤
          max B F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hT₀.le _)) hℓ
    by_cases hs : (σ - 1 / 2) * Real.log T ≤ A
    · exact (ho T hTH σ hσ (Or.inl hs)).trans (hinc F (le_max_right _ _))
    by_cases hf : 2 * Real.log (Real.log T) ≤ (4 / 3 - a) * ((σ - 1 / 2) * Real.log T)
    · exact (ho T hTH σ hσ (Or.inr hf)).trans (hinc F (le_max_right _ _))
    exact (hm T hTK σ hσ (lt_of_not_ge hs) (lt_of_not_ge hf)).trans (hinc B (le_max_left _ _))

/-- It suffices to supply the dyadic count, with analytic multiplicity, only
in the same moving transition window. The full height count follows by
the existing dyadic assembly. -/
theorem uniformSelbergDensity_iff_dyadic_transition {a : ℝ} (A : ℝ)
    (ha : 0 ≤ a) (ha' : a < 4 / 3) :
    UniformSelbergDensity a ↔
      ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧ ∀ T : ℝ, 2 * H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
        A < (σ - 1 / 2) * Real.log T →
        (4 / 3 - a) * ((σ - 1 / 2) * Real.log T) < 2 * Real.log (Real.log T) →
        rightInclusiveWindow (T / 2) T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  rw [uniformSelbergDensity_iff_dyadic_windows ha (by linarith)]
  constructor
  · rintro ⟨C, H, hC, hH, h⟩
    exact ⟨C, H, hC, hH, fun T hT σ hσ _ _ => h T hT σ hσ⟩
  · rintro ⟨B, K, hB, hK, hmid⟩
    obtain ⟨F, H, hF, hH, hout⟩ := exists_selberg_count_outside_transition A ha ha'.le
    refine ⟨max B F, max K H, hB.trans (le_max_left _ _), hK.trans_le (le_max_left _ _), ?_⟩
    intro T hT σ hσ
    have hTK : 2 * K ≤ T := by linarith only [hT, le_max_left K H]
    have hTH : H ≤ T := by linarith only [hT, le_max_right K H, hH]
    have hT₀ : 0 < T := by linarith only [hTH, hH]
    have hℓ := (Real.log_pos (hH.trans_le hTH)).le
    have enlarge {c : ℝ} (hc : c ≤ max B F) :
        c * T ^ (1 - a * (σ - 1 / 2)) * Real.log T ≤
          max B F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hT₀.le _)) hℓ
    by_cases outside : (σ - 1 / 2) * Real.log T ≤ A ∨
        2 * Real.log (Real.log T) ≤ (4 / 3 - a) * ((σ - 1 / 2) * Real.log T)
    · have hw : rightInclusiveWindow (T / 2) T σ ≤ rightInclusiveCount T σ := by
        rw [rightInclusiveWindow_eq_sub (show T / 2 ≤ T by linarith only [hT₀])]
        exact sub_le_self _ (rightInclusiveCount_nonneg _ _)
      exact hw.trans ((hout T hTH σ hσ outside).trans (enlarge (le_max_right _ _)))
    · exact (hmid T hTK σ hσ (lt_of_not_ge (fun h => outside (.inl h)))
        (lt_of_not_ge (fun h => outside (.inr h)))).trans (enlarge (le_max_left _ _))

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_iff_dyadic_transition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformSelbergDensity_iff_dyadic_transition

end RiemannResearch.Analysis.ActualZeroOrdinate
