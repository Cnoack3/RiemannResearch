import RiemannResearch.RH.MultiRangeDivisorCorrections
import RiemannResearch.RH.ConditionalResidueGram

/-!
# Signed multi-range projection budgets and certified infinite tails

Source: `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`, Sections 6--9.
Each range supplies one arbitrary deterministic finite linear combination.
The scalar step optimizes along that combination; this is not a claim that
an arbitrary supplied combination is the optimum over its entire range.
All energies and correlations are the actual infinite conditional means.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro ArithmeticCumulative

/-- Zero energy uses Lean's zero-division convention, justified below. -/
def signedProjectionStep (F G : ℕ → ℝ) (n : ℕ) : ℝ :=
  F n + (-conditionalMeanInner F G / conditionalMeanSquare G) * G n

def signedProjectionGain (F G : ℕ → ℝ) : ℝ :=
  (conditionalMeanInner F G)^2 / conditionalMeanSquare G

theorem signedProjectionStep_energy (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (hG : G ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanSquare (signedProjectionStep F G) =
      conditionalMeanSquare F - signedProjectionGain F G := by
  unfold signedProjectionStep
  by_cases hz : conditionalMeanSquare G = 0
  · simp [signedProjectionGain, hz]
  · exact conditionalMeanSquare_optimal_scalar F G hF hG hz

theorem signedProjectionGain_nonneg (F G : ℕ → ℝ) :
    0 ≤ signedProjectionGain F G :=
  div_nonneg (sq_nonneg _) (conditionalMeanSquare_nonneg _)

def rangeProjectionIterate (Y : ℕ) (s : ℕ → Finset ℕ) (x : ℕ → ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0 => canonicalMobiusHead Y
  | j+1 => signedProjectionStep (rangeProjectionIterate Y s x j)
      (divisorRangeCorrection (Y+1) (s j) (x j))

theorem rangeProjectionIterate_mem_class (Y : ℕ) (s : ℕ → Finset ℕ)
    (x : ℕ → ℕ → ℝ) (hs : ∀ j d, d ∈ s j → Y < d) (j : ℕ) :
    rangeProjectionIterate Y s x j ∈ conditionalHeadClass Y := by
  induction j with
  | zero => exact canonicalMobiusHead_mem_class Y
  | succ j ih =>
    apply add_mul_mem_conditionalHeadClass Y _ _ ih
    · exact divisorRangeCorrection_legal (Y+1) (s j) (x j) (by omega)
        (by intro d hd; have := hs j d hd; omega)
    · intro n _ hn
      exact divisorRangeCorrection_zero_head Y (Y+1) (s j) (x j) (by omega) (hs j) n hn

def rangeProjectionGain (Y : ℕ) (s : ℕ → Finset ℕ) (x : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  signedProjectionGain (rangeProjectionIterate Y s x j)
    (divisorRangeCorrection (Y+1) (s j) (x j))

/-- No mixed correlation has been discarded from this exact finite budget. -/
theorem rangeProjectionIterate_energy (Y : ℕ) (s : ℕ → Finset ℕ)
    (x : ℕ → ℕ → ℝ) (hs : ∀ j d, d ∈ s j → Y < d) (J : ℕ) :
    conditionalMeanSquare (rangeProjectionIterate Y s x J) =
      conditionalMeanSquare (canonicalMobiusHead Y) -
        ∑ j ∈ Finset.range J, rangeProjectionGain Y s x j := by
  induction J with
  | zero => simp [rangeProjectionIterate]
  | succ J ih =>
    rw [rangeProjectionIterate, signedProjectionStep_energy _ _
      (rangeProjectionIterate_mem_class Y s x hs J).1
      (divisorRangeCorrection_legal (Y+1) (s J) (x J) (by omega)
        (by intro d hd; have := hs J d hd; omega)), ih, Finset.sum_range_succ]
    unfold rangeProjectionGain
    ring

/-- Actual head mass limits the accumulated signed gains. -/
theorem rangeProjectionGain_budget (Y : ℕ) (s : ℕ → Finset ℕ)
    (x : ℕ → ℕ → ℝ) (hs : ∀ j d, d ∈ s j → Y < d) (J : ℕ) :
    0 ≤ (∑ j ∈ Finset.range J, rangeProjectionGain Y s x j) ∧
    (∑ j ∈ Finset.range J, rangeProjectionGain Y s x j) ≤
      conditionalMeanSquare (canonicalMobiusHead Y) - (Y : ℝ)/((Y : ℝ)+2) := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => signedProjectionGain_nonneg _ _)
  · have hb := (conditionalHeadMinimum_ge_head_mass Y).trans
      (conditionalHeadMinimum_le Y (rangeProjectionIterate_mem_class Y s x hs J))
    rw [rangeProjectionIterate_energy Y s x hs J] at hb
    linarith

/-- A bounded conditional mean gives a rigorous bound for the infinite tail. -/
theorem conditionalMeanTailSquare_le_of_mean_bound (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (N : ℕ) (L : ℝ) (_hL : 0 ≤ L)
    (hb : ∀ t, N < t → |cesaro F t| ≤ L) :
    conditionalMeanTailSquare N F ≤ 2 / ((N : ℝ)+2) * L^2 := by
  have hs := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hF).comp_injective
      (fun a b h => Nat.add_right_cancel h : Function.Injective (fun k : ℕ => k+N))
  have hq := (hasSum_mixtureWeight.summable).comp_injective
    (fun a b h => Nat.add_right_cancel h : Function.Injective (fun k : ℕ => k+N))
  calc
    _ ≤ ∑' k : ℕ, conditionalWeight (k+N) * L^2 := by
      apply Summable.tsum_le_tsum _ hs (hq.mul_right (L^2))
      intro k
      apply mul_le_mul_of_nonneg_left _ (conditionalWeight_pos _).le
      have hm := mul_self_le_mul_self (abs_nonneg (cesaro F (k+N+1)))
        (hb (k+N+1) (by omega))
      simpa only [← pow_two, sq_abs] using hm
    _ = _ := by rw [tsum_mul_right, conditionalWeight_tsum_tail]

/-- Every legal candidate receives an exact finite lower and certified upper bound. -/
theorem conditionalMeanSquare_finite_certificate (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (N : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ t, N < t → |cesaro F t| ≤ L) :
    (∑ k ∈ Finset.range N, conditionalWeight k * (cesaro F (k+1))^2) ≤
      conditionalMeanSquare F ∧
    conditionalMeanSquare F ≤
      (∑ k ∈ Finset.range N, conditionalWeight k * (cesaro F (k+1))^2) +
        2 / ((N : ℝ)+2) * L^2 := by
  have he := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hF).sum_add_tsum_nat_add N
  change _ + conditionalMeanTailSquare N F = conditionalMeanSquare F at he
  have hn := conditionalMeanTailSquare_nonneg N F
  have hu := conditionalMeanTailSquare_le_of_mean_bound F hF N L hL hb
  constructor <;> linarith

/-- An explicit coefficient bound for certification only, not the signed objective. -/
def divisorRangeMeanBound (A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s, |x d| * (((A : ℝ)/(d : ℝ)+1)/2)

theorem divisorAnchorDirection_mean_bound (A d t : ℕ) (hA : 0 < A) (hd : 0 < d) :
    |cesaro (divisorAnchorDirection A d) t| ≤ ((A : ℝ)/(d : ℝ)+1)/2 := by
  have he : cesaro (divisorAnchorDirection A d) t =
      (A : ℝ)/(d : ℝ)*cesaro (residueFraction A) t - cesaro (residueFraction d) t := by
    simp only [cesaro, divisorAnchorDirection, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [he]
  calc
    _ ≤ |(A : ℝ)/(d : ℝ)*cesaro (residueFraction A) t| +
        |cesaro (residueFraction d) t| := abs_sub _ _
    _ = (A : ℝ)/(d : ℝ)*cesaro (residueFraction A) t +
        cesaro (residueFraction d) t := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) (ArithmeticCumulative.CesaroResidue.cesaro_residue_nonneg _ _)),
        abs_of_nonneg (ArithmeticCumulative.CesaroResidue.cesaro_residue_nonneg _ _)]
    _ ≤ _ := by
      have ha := ArithmeticCumulative.CesaroResidue.cesaro_residue_le_half A t hA
      have hd' := ArithmeticCumulative.CesaroResidue.cesaro_residue_le_half d t hd
      have hm := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ (A:ℝ)/(d:ℝ))
      linarith

theorem divisorRangeCorrection_mean_bound (A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ)
    (hA : 0 < A) (hs : ∀ d ∈ s, 0 < d) (t : ℕ) :
    |cesaro (divisorRangeCorrection A s x) t| ≤ divisorRangeMeanBound A s x := by
  have he : cesaro (divisorRangeCorrection A s x) t =
      ∑ d ∈ s, x d * cesaro (divisorAnchorDirection A d) t :=
    cesaro_finsetCombination s x (fun d => divisorAnchorDirection A d) t
  rw [he]
  calc
    _ ≤ ∑ d ∈ s, |x d * cesaro (divisorAnchorDirection A d) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (divisorAnchorDirection_mean_bound A d t hA (hs d hd))
        (abs_nonneg _)

theorem correctedMobiusHead_mean_bound (Y : ℕ) (hY : 0 < Y)
    (s : Finset ℕ) (x : ℕ → ℝ) (hs : ∀ d ∈ s, Y < d) (t : ℕ) :
    |cesaro (correctedMobiusHead Y s x) t| ≤
      (Y : ℝ)+divisorRangeMeanBound (Y+1) s x := by
  have he : cesaro (correctedMobiusHead Y s x) t =
      cesaro (canonicalMobiusHead Y) t + cesaro (divisorRangeCorrection (Y+1) s x) t := by
    unfold correctedMobiusHead
    simpa only [one_mul] using cesaro_add_mul (canonicalMobiusHead Y)
      (divisorRangeCorrection (Y+1) s x) 1 t
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (canonicalMobiusHead_mean_abs_le Y hY t)
    (divisorRangeCorrection_mean_bound (Y+1) s x (by omega)
      (by intro d hd; have := hs d hd; omega) t))

/-- Centered inverse-endpoint control certifies the complete tail. For L=0
this gives cubic decay with an explicit coefficient-dependent constant.
Source: direct application of the existing complete-tail bound. -/
theorem conditionalMeanTailSquare_le_centered (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (N : ℕ) (L B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t, 0 < t → |cesaro F t - L| ≤ B / (t : ℝ)) :
    conditionalMeanTailSquare N F ≤
      2 / ((N : ℝ) + 2) * (|L| + B / ((N : ℝ) + 1)) ^ 2 := by
  apply conditionalMeanTailSquare_le_of_mean_bound F hF N _ (by positivity)
  intro t ht
  have htR : (N : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hden : B / (t : ℝ) ≤ B / ((N : ℝ) + 1) :=
    div_le_div_of_nonneg_left hB (by positivity) htR
  calc
    |cesaro F t| = |(cesaro F t - L) + L| := by congr 1; ring
    _ ≤ |cesaro F t - L| + |L| := abs_add_le _ _
    _ ≤ _ := by linarith [hb t (by omega)]

end RiemannResearch.RH.Pareto
