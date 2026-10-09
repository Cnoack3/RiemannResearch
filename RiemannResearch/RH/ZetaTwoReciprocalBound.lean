import RiemannResearch.Analysis.InfiniteWeightedCauchy
import RiemannResearch.RH.ReciprocalInfiniteCertificate
import RiemannResearch.RH.ZetaTwoOptimizerStage

/-!
# Unconditional reciprocal bounds for the actual inverse-square optimizer

Source: `RH/ReciprocalHeadCertificate20261008.md`, for the complete signed
normal equations, head-tail identity, and positive-form Cauchy assembly.
Every vector, atom, projection, residual and correction below uses the existing
actual `QHilbert` definitions. The infinite arithmetic tail is never truncated.
The stronger fixed cap uses an internally proved exact rational certificate;
neither cap is supplied as a hypothesis of the actual stage theorems.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoReciprocalBound
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoOptimizerStage
open ReciprocalHeadCertificate ReciprocalInfiniteCertificate
open RiemannResearch.Analysis.InfiniteWeightedCauchy

def rawSquare (f : QHilbert) (k : ℕ) : ℝ := (qSequence f k) ^ 2 / (k : ℝ) ^ 2

def residueCharge (d : ℕ) (f : QHilbert) (k : ℕ) : ℝ :=
  ((k % d : ℕ) : ℝ) * qSequence f k / (k : ℝ) ^ 2

def tailEnergy (τ : ℝ) (f : QHilbert) : ℝ :=
  ∑' i : ℕ, gap τ (i + 3) * rawSquare f (i + 3)

def headEnergy (τ : ℝ) (f : QHilbert) : ℝ :=
  (1 - τ) * (qSequence f 1) ^ 2 + ((1 / 2 - τ) / 4) * (qSequence f 2) ^ 2

private theorem rawSquare_eq (f : QHilbert) (k : ℕ) :
    rawSquare f k = zetaTwo * (positiveQWeight k * (qSequence f k) ^ 2) := by
  by_cases hk : k = 0
  · simp [hk, rawSquare]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    unfold rawSquare positiveQWeight
    field_simp [ne_of_gt zetaTwo_pos, hkR]

theorem rawSquare_summable (f : QHilbert) : Summable (rawSquare f) := by
  exact ((qSequence_square_summable f).mul_left zetaTwo).congr
    (fun k => (rawSquare_eq f k).symm)

theorem rawSquare_tsum (f : QHilbert) : (∑' k, rawSquare f k) = zetaTwo * ‖f‖ ^ 2 := by
  simp_rw [rawSquare_eq]
  rw [tsum_mul_left, ← qNorm_weighted_sq]

private theorem residueCharge_eq (d : ℕ) (hd : 0 < d) (f : QHilbert) (k : ℕ) :
    residueCharge d f k = (d : ℝ) * zetaTwo *
      (positiveQWeight k * qSequence (qResidue d) k * qSequence f k) := by
  rw [qSequence_qResidue]
  by_cases hk : k = 0
  · simp [hk, residueCharge]
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    unfold residueCharge positiveQWeight RiemannResearch.RH.ArithmeticCumulative.residueFraction
    field_simp [ne_of_gt zetaTwo_pos, hdR, hkR]

theorem residueCharge_summable (d : ℕ) (hd : 0 < d) (f : QHilbert) :
    Summable (residueCharge d f) := by
  exact ((qSequence_product_summable (qResidue d) f).mul_left ((d : ℝ) * zetaTwo)).congr
    (fun k => (residueCharge_eq d hd f k).symm)

theorem residueCharge_tsum (d : ℕ) (hd : 0 < d) (f : QHilbert) :
    (∑' k, residueCharge d f k) = (d : ℝ) * zetaTwo * inner ℝ (qResidue d) f := by
  simp_rw [residueCharge_eq d hd]
  rw [tsum_mul_left, ← qInner_weighted]

theorem signed_charge_summable (f : QHilbert) :
    Summable (fun i : ℕ => weightOne (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2) ∧
    Summable (fun i : ℕ => weightTwo (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2) := by
  have h2 := (summable_nat_add_iff 3).mpr (residueCharge_summable 2 (by norm_num) f)
  have h3 := (summable_nat_add_iff 3).mpr (residueCharge_summable 3 (by norm_num) f)
  constructor
  · exact h2.neg.congr (fun i => by unfold residueCharge weightOne; ring)
  · exact ((h2.sub h3).mul_left 2).congr
      (fun i => by unfold residueCharge weightTwo; ring)

/-- Exact signed recovery of both head sites from the entire arithmetic tail. -/
theorem signed_normal_equations (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0) :
    qSequence f 1 = ∑' i : ℕ, weightOne (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2 ∧
    qSequence f 2 = ∑' i : ℕ, weightTwo (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2 := by
  have hs2 := residueCharge_summable 2 (by norm_num) f
  have hs3 := residueCharge_summable 3 (by norm_num) f
  have he2 := hs2.sum_add_tsum_nat_add 3
  have he3 := hs3.sum_add_tsum_nat_add 3
  have hh2 : (∑ k ∈ Finset.range 3, residueCharge 2 f k) = qSequence f 1 := by
    norm_num [residueCharge, Finset.sum_range_succ]
  have hh3 : (∑ k ∈ Finset.range 3, residueCharge 3 f k) =
      qSequence f 1 + qSequence f 2 / 2 := by
    norm_num [residueCharge, Finset.sum_range_succ]
    ring
  rw [hh2, residueCharge_tsum 2 (by norm_num) f, h2] at he2
  rw [hh3, residueCharge_tsum 3 (by norm_num) f, h3] at he3
  have hs2tail := (summable_nat_add_iff 3).mpr hs2
  have hs3tail := (summable_nat_add_iff 3).mpr hs3
  constructor
  · have he : (∑' i : ℕ, weightOne (i + 3) * qSequence f (i + 3) /
        ((i + 3 : ℕ) : ℝ) ^ 2) = -(∑' i : ℕ, residueCharge 2 f (i + 3)) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro i
      unfold weightOne residueCharge
      ring
    rw [he]
    linarith
  · have he : (∑' i : ℕ, weightTwo (i + 3) * qSequence f (i + 3) /
        ((i + 3 : ℕ) : ℝ) ^ 2) =
        2 * ((∑' i : ℕ, residueCharge 2 f (i + 3)) -
          (∑' i : ℕ, residueCharge 3 f (i + 3))) := by
      rw [← hs2tail.tsum_sub hs3tail, ← tsum_mul_left]
      apply tsum_congr
      intro i
      unfold weightTwo residueCharge
      ring
    rw [he]
    linarith

private theorem rawReciprocal_summable (f : QHilbert) :
    Summable (fun k : ℕ => rawSquare f k / (k : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun k => by unfold rawSquare; positivity)
    _ (rawSquare_summable f)
  intro k
  by_cases hk : k = 0
  · simp [hk, rawSquare]
  · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    simpa using div_le_self (show 0 ≤ rawSquare f k by unfold rawSquare; positivity) hkr

theorem rawReciprocal_tsum (f : QHilbert) :
    (∑' k : ℕ, rawSquare f k / (k : ℝ)) = zetaTwo * inner ℝ f (reciprocalD f) := by
  simp_rw [rawSquare_eq]
  rw [reciprocalD_inner_physical, ← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

theorem tailEnergy_summable (τ : ℝ) (hτ : 1 / 3 < τ) (f : QHilbert) :
    Summable (fun i : ℕ => gap τ (i + 3) * rawSquare f (i + 3)) := by
  have hs := ((summable_nat_add_iff 3).mpr (rawSquare_summable f)).mul_left τ
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (gap_pos τ hτ _ (by omega)).le (by unfold rawSquare; positivity))
    _ hs
  intro i
  apply mul_le_mul_of_nonneg_right _ (by unfold rawSquare; positivity)
  unfold gap
  have : (0 : ℝ) ≤ 1 / ((i + 3 : ℕ) : ℝ) := by positivity
  linarith

theorem tailEnergy_nonneg (τ : ℝ) (hτ : 1 / 3 < τ) (f : QHilbert) : 0 ≤ tailEnergy τ f := by
  apply tsum_nonneg
  intro i
  exact mul_nonneg (gap_pos τ hτ _ (by omega)).le (by unfold rawSquare; positivity)

/-- Complete norm/reciprocal identity: both negative head squares are retained. -/
theorem reciprocal_gap_exact (τ : ℝ) (f : QHilbert) :
    zetaTwo * (τ * ‖f‖ ^ 2 - inner ℝ f (reciprocalD f)) =
      tailEnergy τ f - headEnergy τ f := by
  have hs := ((rawSquare_summable f).mul_left τ).sub (rawReciprocal_summable f)
  have he := hs.sum_add_tsum_nat_add 3
  have hhead : (∑ k ∈ Finset.range 3, (τ * rawSquare f k - rawSquare f k / (k : ℝ))) =
      -headEnergy τ f := by
    norm_num [Finset.sum_range_succ, rawSquare, headEnergy]
    ring
  have htail : (∑' i : ℕ, (τ * rawSquare f (i + 3) -
      rawSquare f (i + 3) / ((i + 3 : ℕ) : ℝ))) = tailEnergy τ f := by
    apply tsum_congr
    intro i
    unfold gap
    ring
  rw [hhead, htail, ((rawSquare_summable f).mul_left τ).tsum_sub
    (rawReciprocal_summable f), tsum_mul_left, rawSquare_tsum, rawReciprocal_tsum] at he
  linarith

def recoveryCharge (τ : ℝ) (a b : ℕ → ℝ) (x y : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (1 - τ) * a k * x + Real.sqrt ((1 / 2 - τ) / 4) * b k * y

def recoveryGramTerm (τ : ℝ) (a b : ℕ → ℝ) (x y : ℝ) (k : ℕ) : ℝ :=
  (recoveryCharge τ a b x y k) ^ 2 / ((k : ℝ) ^ 2 * gap τ k)

private theorem charge_pair_summable (τ : ℝ) (a b : ℕ → ℝ) (x y : ℝ) (f : QHilbert)
    (hs : Summable (fun i : ℕ => a (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2) ∧
      Summable (fun i : ℕ => b (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2)) :
    Summable (fun i : ℕ => recoveryCharge τ a b x y (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2) := by
  exact ((hs.1.mul_left (Real.sqrt (1 - τ) * x)).add
    (hs.2.mul_left (Real.sqrt ((1 / 2 - τ) / 4) * y))).congr
      (fun i => by unfold recoveryCharge; ring)

theorem headEnergy_le_tail (τ Λ : ℝ) (a b : ℕ → ℝ) (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2)
    (hΛ : 0 ≤ Λ)
    (hgramSum : ∀ x y : ℝ, Summable (fun i : ℕ => recoveryGramTerm τ a b x y (i + 3)))
    (hgram : ∀ x y : ℝ, (∑' i : ℕ, recoveryGramTerm τ a b x y (i + 3)) ≤ Λ * (x ^ 2 + y ^ 2))
    (f : QHilbert)
    (hsigned : Summable (fun i : ℕ => a (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2) ∧
      Summable (fun i : ℕ => b (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2))
    (hnormal : qSequence f 1 = ∑' i : ℕ, a (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2 ∧
      qSequence f 2 = ∑' i : ℕ, b (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2) :
    headEnergy τ f ≤ Λ * tailEnergy τ f := by
  let x := Real.sqrt (1 - τ) * qSequence f 1
  let y := Real.sqrt ((1 / 2 - τ) / 4) * qSequence f 2
  have hp1 : 0 ≤ 1 - τ := by linarith
  have hp2 : 0 ≤ (1 / 2 - τ) / 4 := by linarith
  have hs1 := Real.sq_sqrt (show 0 ≤ 1 - τ by linarith)
  have hs2 := Real.sq_sqrt (show 0 ≤ (1 / 2 - τ) / 4 by linarith)
  have hJ : 0 ≤ headEnergy τ f := by unfold headEnergy; positivity
  have hxy : x ^ 2 + y ^ 2 = headEnergy τ f := by
    dsimp only [x, y]
    rw [mul_pow, mul_pow, hs1, hs2]
    rfl
  have hsum : (∑' i : ℕ, recoveryCharge τ a b x y (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2) = headEnergy τ f := by
    calc
      _ = (Real.sqrt (1 - τ) * x) * (∑' i : ℕ, a (i + 3) *
          qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2) +
          (Real.sqrt ((1 / 2 - τ) / 4) * y) * (∑' i : ℕ, b (i + 3) *
          qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2) := by
        rw [← tsum_mul_left, ← tsum_mul_left,
          ← (hsigned.1.mul_left _).tsum_add
            (hsigned.2.mul_left _)]
        apply tsum_congr
        intro i
        unfold recoveryCharge
        ring
      _ = _ := by
        rw [← hnormal.1, ← hnormal.2]
        dsimp only [x, y]
        unfold headEnergy
        calc
          _ = (Real.sqrt (1 - τ)) ^ 2 * (qSequence f 1) ^ 2 +
              (Real.sqrt ((1 / 2 - τ) / 4)) ^ 2 * (qSequence f 2) ^ 2 := by ring
          _ = _ := by rw [hs1, hs2]
  have hcs := weighted_tsum_cauchy
    (fun i => recoveryCharge τ a b x y (i + 3) * qSequence f (i + 3) / ((i + 3 : ℕ) : ℝ) ^ 2)
    (fun i => gap τ (i + 3) * rawSquare f (i + 3))
    (fun i => recoveryGramTerm τ a b x y (i + 3))
    (charge_pair_summable τ a b x y f hsigned) (tailEnergy_summable τ hτ f)
    (hgramSum x y)
    (fun i => mul_nonneg (gap_pos τ hτ _ (by omega)).le (by unfold rawSquare; positivity))
    (fun i => div_nonneg (sq_nonneg _) (by
      exact mul_nonneg (sq_nonneg _) (gap_pos τ hτ _ (by omega)).le))
    (fun i => by
      have hk : (((i + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hg := ne_of_gt (gap_pos τ hτ (i + 3) (by omega))
      apply le_of_eq
      unfold rawSquare recoveryGramTerm
      field_simp [hk, hg])
  rw [hsum] at hcs
  change (headEnergy τ f) ^ 2 ≤ tailEnergy τ f * _ at hcs
  have hG := hgram x y
  rw [hxy] at hG
  have ht := tailEnergy_nonneg τ hτ f
  have hprod := mul_le_mul_of_nonneg_left hG ht
  by_cases hzero : headEnergy τ f = 0
  · rw [hzero]
    exact mul_nonneg hΛ ht
  · have hp : 0 < headEnergy τ f := lt_of_le_of_ne hJ (Ne.symm hzero)
    apply le_of_mul_le_mul_left (a := headEnergy τ f) _ hp
    nlinarith

theorem firstMoment_le_of_certificate (τ Λ : ℝ)
    (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2) (hΛ0 : 0 ≤ Λ) (hΛ : Λ < 1)
    (hgram : ∀ x y : ℝ, (∑' i : ℕ, gramTerm τ x y (i + 3)) ≤ Λ * (x ^ 2 + y ^ 2))
    (f : QHilbert) (h2 : inner ℝ (qResidue 2) f = 0)
    (h3 : inner ℝ (qResidue 3) f = 0) :
    inner ℝ f (reciprocalD f) ≤ τ * ‖f‖ ^ 2 := by
  have hJ := headEnergy_le_tail τ Λ weightOne weightTwo hτ hτ' hΛ0
    (fun x y => gram_summable τ x y hτ hτ') hgram f
    (signed_charge_summable f) (signed_normal_equations f h2 h3)
  have hT := tailEnergy_nonneg τ hτ f
  have he := reciprocal_gap_exact τ f
  have hΛT : Λ * tailEnergy τ f ≤ tailEnergy τ f := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hΛ.le hT
  have hTJ : headEnergy τ f ≤ tailEnergy τ f := hJ.trans hΛT
  have hp : 0 ≤ zetaTwo * (τ * ‖f‖ ^ 2 - inner ℝ f (reciprocalD f)) := by
    rw [he]
    exact sub_nonneg.mpr hTJ
  have hh := (mul_nonneg_iff_of_pos_left zetaTwo_pos).mp hp
  linarith

theorem original_firstMoment_remainder (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0) :
    (23 / 4160 : ℝ) * tailEnergy (3 / 7) f ≤
      zetaTwo * ((3 / 7 : ℝ) * ‖f‖ ^ 2 - inner ℝ f (reciprocalD f)) := by
  rw [reciprocal_gap_exact]
  have hJ := headEnergy_le_tail (3 / 7) (4137 / 4160) weightOne weightTwo
    (by norm_num) (by norm_num) (by norm_num)
    (fun x y => gram_summable (3 / 7) x y (by norm_num) (by norm_num))
    original_complete_gram_le f (signed_charge_summable f) (signed_normal_equations f h2 h3)
  linarith

theorem original_firstMoment_le (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0) :
    inner ℝ f (reciprocalD f) ≤ (3 / 7 : ℝ) * ‖f‖ ^ 2 :=
  firstMoment_le_of_certificate (3 / 7) (4137 / 4160) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) original_complete_gram_le f h2 h3

theorem sharper_firstMoment_le (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0) :
    inner ℝ f (reciprocalD f) ≤ (107 / 250 : ℝ) * ‖f‖ ^ 2 :=
  firstMoment_le_of_certificate (107 / 250) (33101057 / 33381000) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) sharper_complete_gram_le f h2 h3

/-- Cauchy-Schwarz for the actual positive reciprocal form. -/
theorem reciprocal_form_cauchy (f g : QHilbert) :
    (inner ℝ f (reciprocalD g)) ^ 2 ≤
      inner ℝ f (reciprocalD f) * inner ℝ g (reciprocalD g) := by
  let a := inner ℝ f (reciprocalD f)
  let b := inner ℝ g (reciprocalD g)
  let c := inner ℝ f (reciprocalD g)
  have hb0 : 0 ≤ b := reciprocalD_positive g
  by_cases hb : b = 0
  · have hg : g = 0 := reciprocalD_faithful g hb
    simp [hg]
  · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hcross : inner ℝ g (reciprocalD f) = c := by
      rw [real_inner_comm, reciprocalD_symmetric]
    have hp := reciprocalD_positive (b • f - c • g)
    rw [map_sub, map_smul, map_smul] at hp
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hcross] at hp
    change c ^ 2 ≤ a * b
    change 0 ≤ b * (b * a) - b * (c * c) -
      (c * (b * c) - c * (c * b)) at hp
    have he : b * (b * a) - b * (c * c) -
        (c * (b * c) - c * (c * b)) = b * (a * b - c ^ 2) := by ring
    rw [he] at hp
    by_contra hbad
    have hn := mul_neg_of_pos_of_neg hbpos
      (sub_neg.mpr (lt_of_not_ge hbad))
    nlinarith

/-- A mixed reciprocal-form estimate applying the cap only to the complete
screened image. The input need not lie in the complement or satisfy a
radical relation. Source: target-only assembly in
`RH/ConductorRecoveryStatus20261009.md`, section 4. -/
theorem screened_sq_le_firstMoment (τ : ℝ) (hτ : 0 ≤ τ)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hcap : ∀ s : QHilbert, s ∈ Vᗮ →
      inner ℝ s (reciprocalD s) ≤ τ * ‖s‖ ^ 2)
    (f : QHilbert) :
    ‖reciprocalD f - V.starProjection (reciprocalD f)‖ ^ 2 ≤
      τ * inner ℝ f (reciprocalD f) := by
  let s := reciprocalD f - V.starProjection (reciprocalD f)
  have hs : s ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hnorm : ‖s‖ ^ 2 = inner ℝ s (reciprocalD f) := by
    have hz : inner ℝ s (V.starProjection (reciprocalD f)) = 0 := by
      rw [real_inner_comm]
      exact (V.mem_orthogonal _).mp hs _ (V.starProjection_apply_mem _)
    have he : inner ℝ s s = inner ℝ s (reciprocalD f) := by
      change inner ℝ s (reciprocalD f - V.starProjection (reciprocalD f)) = _
      rw [inner_sub_right, hz, sub_zero]
    simpa only [real_inner_self_eq_norm_sq] using he
  have hcs := reciprocal_form_cauchy s f
  rw [← hnorm] at hcs
  have hp := mul_le_mul_of_nonneg_right (hcap s hs) (reciprocalD_positive f)
  change ‖s‖ ^ 2 ≤ τ * inner ℝ f (reciprocalD f)
  by_cases hz : ‖s‖ ^ 2 = 0
  · rw [hz]
    exact mul_nonneg hτ (reciprocalD_positive f)
  · have hspos : 0 < ‖s‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    by_contra hbad
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hspos
    nlinarith

/-- A universal actual-Q compression theorem for any subspace admitting
orthogonal projection. The final stage theorems discharge the first-moment
provider with the complete rational arithmetic certificates. -/
theorem screened_bound_of_firstMoment (τ : ℝ) (hτ : 0 ≤ τ)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hcap : ∀ f : QHilbert, f ∈ Vᗮ → inner ℝ f (reciprocalD f) ≤ τ * ‖f‖ ^ 2)
    (f : QHilbert) (hf : f ∈ Vᗮ) :
    ‖reciprocalD f - V.starProjection (reciprocalD f)‖ ^ 2 ≤ τ ^ 2 * ‖f‖ ^ 2 := by
  let s := reciprocalD f - V.starProjection (reciprocalD f)
  have hs : s ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hnorm : ‖s‖ ^ 2 = inner ℝ s (reciprocalD f) := by
    have hz : inner ℝ s (V.starProjection (reciprocalD f)) = 0 := by
      rw [real_inner_comm]
      exact (V.mem_orthogonal _).mp hs _ (V.starProjection_apply_mem _)
    have he : inner ℝ s s = inner ℝ s (reciprocalD f) := by
      change inner ℝ s (reciprocalD f - V.starProjection (reciprocalD f)) = _
      rw [inner_sub_right, hz, sub_zero]
    simpa only [real_inner_self_eq_norm_sq] using he
  have hfcap := hcap f hf
  have hscap := hcap s hs
  have hcs := reciprocal_form_cauchy s f
  rw [← hnorm] at hcs
  have hprod := mul_le_mul hscap hfcap (reciprocalD_positive f)
    (mul_nonneg hτ (sq_nonneg ‖s‖))
  change ‖s‖ ^ 2 ≤ τ ^ 2 * ‖f‖ ^ 2
  by_cases hz : ‖s‖ ^ 2 = 0
  · rw [hz]
    positivity
  · have hspos : 0 < ‖s‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    by_contra hbad
    have hp := mul_pos hspos (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith

theorem stage_contains_two_three (n : ℕ) (hn : 2 ≤ n) :
    qResidue 2 ∈ stage n ∧ qResidue 3 ∈ stage n := by
  constructor
  · unfold stage RiemannResearch.Analysis.ExhaustiveWalk.walkSpan
    apply Submodule.subset_span
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [squarefreeAtom, Nat.prime_two.squarefree]
  · unfold stage RiemannResearch.Analysis.ExhaustiveWalk.walkSpan
    apply Submodule.subset_span
    refine ⟨⟨1, by omega⟩, ?_⟩
    simp [squarefreeAtom, Nat.prime_three.squarefree]

theorem screenedResidual_sq_le_original (n : ℕ) (hn : 2 ≤ n) :
    ‖screenedResidual n‖ ^ 2 ≤ (9 / 49 : ℝ) * error n := by
  have hg := stage_contains_two_three n hn
  have h := screened_bound_of_firstMoment (3 / 7) (by norm_num)
    (stage n) (fun f hf => original_firstMoment_le f
      (((stage n).mem_orthogonal _).mp hf _ hg.1)
      (((stage n).mem_orthogonal _).mp hf _ hg.2)) (residual n) (residual_mem_orthogonal n)
  norm_num only [show (3 / 7 : ℝ) ^ 2 = 9 / 49 by norm_num] at h
  exact h

/-- The requested unconditional stage theorem, with no bound hypothesis. -/
theorem secondMoment_le_nine_div_fortyNine (n : ℕ) (hn : 2 ≤ n) :
    secondMoment n ≤ (9 / 49 : ℝ) := by
  unfold secondMoment
  exact (div_le_iff₀ (error_pos n)).mpr (screenedResidual_sq_le_original n hn)

theorem screenedResidual_sq_le_sharper (n : ℕ) (hn : 2 ≤ n) :
    ‖screenedResidual n‖ ^ 2 ≤ (11449 / 62500 : ℝ) * error n := by
  have hg := stage_contains_two_three n hn
  have h := screened_bound_of_firstMoment (107 / 250) (by norm_num)
    (stage n) (fun f hf => sharper_firstMoment_le f
      (((stage n).mem_orthogonal _).mp hf _ hg.1)
      (((stage n).mem_orthogonal _).mp hf _ hg.2)) (residual n) (residual_mem_orthogonal n)
  norm_num only [show (107 / 250 : ℝ) ^ 2 = 11449 / 62500 by norm_num] at h
  exact h

/-- A strictly stronger fixed positive cap from the same complete tail. -/
theorem secondMoment_bounds_sharper (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ secondMoment n ∧ secondMoment n ≤ (11449 / 62500 : ℝ) := by
  constructor
  · exact div_nonneg (sq_nonneg _) (error_pos n).le
  · unfold secondMoment
    exact (div_le_iff₀ (error_pos n)).mpr (screenedResidual_sq_le_sharper n hn)

theorem sharper_cap_lt_original : (11449 / 62500 : ℝ) < 9 / 49 := by norm_num

/-- The full signed identity is reused: both mismatch and screening squares
remain in `signedCorrection`; the positive quartic floor is subtracted. -/
theorem signedCorrection_le_sharper (n : ℕ) (hn : 2 ≤ n) :
    signedCorrection n ≤ (11449 / 62500 : ℝ) * error n - quarticFloor n := by
  have he := screenedResidual_energy_exact n
  have hb := screenedResidual_sq_le_sharper n hn
  linarith

theorem positiveCorrection_normalized_bounds (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ max (signedCorrection n) 0 / error n ∧
      max (signedCorrection n) 0 / error n ≤ (11449 / 62500 : ℝ) := by
  constructor
  · exact div_nonneg (le_max_right _ _) (error_pos n).le
  · apply (div_le_iff₀ (error_pos n)).mpr
    apply max_le
    · have hb := signedCorrection_le_sharper n hn
      have hfloor : 0 ≤ quarticFloor n := sq_nonneg _
      linarith
    · exact mul_nonneg (by norm_num) (error_pos n).le

end RiemannResearch.RH.ZetaTwoReciprocalBound
