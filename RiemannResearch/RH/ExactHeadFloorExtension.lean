import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ExactHeadGreenProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Legal residue extensions of finite floor profiles
Source: user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, section 2.3. A terminal residue correction turns any positive - index
finite floor polynomial into a legal finite NB combination agreeing below P.
Divisibility is needed only for nonzero coefficients when asserting period P.
This separates exact finite legality from the unresolved uniform energy bound.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.FloorProfileExtension
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ExactHeadGreenProfile

def extension (P : ℕ) (D : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((P : ℝ) * (∑ d ∈ D, c d / (d : ℝ))) * residueFraction P n -
    ∑ d ∈ D, c d * residueFraction d n

theorem extension_zero (P : ℕ) (D : Finset ℕ) (c : ℕ → ℝ) :
    extension P D c 0 = 0 := by simp [extension,residueFraction]

theorem extension_below_period (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) (n : ℕ) (hn : n < P) :
    extension P D c n = ∑ d ∈ D, c d * grid d n := by
  have hs : (∑ d ∈ D, c d * residueFraction d n) =
      (n : ℝ) * (∑ d ∈ D, c d / (d : ℝ)) - ∑ d ∈ D, c d * grid d n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [residueFraction_eq_div_sub_floor d n (hD d hd)]
    unfold grid
    ring
  have hp : residueFraction P n = (n : ℝ) / (P : ℝ) := by
    simp [residueFraction, Nat.mod_eq_of_lt hn]
  unfold extension
  rw [hs,hp]
  have hP0 : (P : ℝ) ≠ 0 := by positivity
  field_simp [hP0]
  <;> ring

theorem extension_periodic (P : ℕ) (D : Finset ℕ) (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ D, c d ≠ 0 → d ∣ P) (n : ℕ) :
    extension P D c (n + P) = extension P D c n := by
  unfold extension
  have hp : residueFraction P (n + P) = residueFraction P n := by
    simp [residueFraction, Nat.add_mod]
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : c d = 0
  · simp [hc]
  · simp [residueFraction,Nat.add_mod,Nat.mod_eq_zero_of_dvd (hdiv d hd hc)]

theorem extension_terminal (P : ℕ) (D : Finset ℕ) (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ D, c d ≠ 0 → d ∣ P) :
    extension P D c P = 0 := by
  simpa [extension_zero] using extension_periodic P D c hdiv 0

private theorem residue_mem_legal (d : ℕ) (hd : 0 < d) :
    residueFraction d ∈ legalSeedSpan (Set.Ici 1) := by
  have hr : residue d ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [dilation_one] using
      (dilation_generator_mem (Set.Ici 1) (a := d) (m := 1)
        (show d ∈ Set.Ici 1 from hd) (by omega))
  have he : residueFraction d = (1 / (d : ℝ)) • residue d := by
    funext n
    simp [residueFraction,residue,div_eq_mul_inv,mul_comm]
  rw [he]
  exact (legalSeedSpan _).smul_mem _ hr

/-- Finite legal membership is proved, not included as a density premise. -/
theorem extension_mem_legal (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) :
    extension P D c ∈ legalSeedSpan (Set.Ici 1) := by
  have hp := (legalSeedSpan (Set.Ici 1)).smul_mem
    ((P : ℝ) * (∑ d ∈ D, c d / (d : ℝ))) (residue_mem_legal P hP)
  have hs : (∑ d ∈ D, c d • residueFraction d) ∈ legalSeedSpan (Set.Ici 1) := by
    apply (legalSeedSpan _).sum_mem
    intro d hd
    exact (legalSeedSpan _).smul_mem _ (residue_mem_legal d (hD d hd))
  convert (legalSeedSpan _).sub_mem hp hs using 1
  funext n
  simp [extension,Finset.sum_apply]

private theorem residue_abs_le_one (d : ℕ) (hd : 0 < d) (n : ℕ) :
    |residueFraction d n| ≤ 1 := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hm : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  unfold residueFraction
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_iff₀ hdR).mpr (by simpa using hm)

theorem extension_bounded (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) :
    ∀ n, |extension P D c n| ≤
      |(P : ℝ) * (∑ d ∈ D, c d / (d : ℝ))| + ∑ d ∈ D, |c d| := by
  intro n
  unfold extension
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (residue_abs_le_one P hP n)
      (abs_nonneg ((P : ℝ) * (∑ d ∈ D, c d / (d : ℝ))))
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (residue_abs_le_one d (hD d hd) n) (abs_nonneg (c d))

def hilbertExtension (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) : ThresholdHilbert :=
  sequenceHilbert (extension P D c) (by
    simpa only [pow_two] using weighted_summable_of_bounded
      (bounded_product (extension_bounded P hP D c hD) (extension_bounded P hP D c hD)))

theorem hilbertExtension_sequence (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) :
    hilbertSequence (hilbertExtension P hP D c hD) = extension P D c := by
  apply hilbertSequence_sequenceHilbert
  exact extension_zero P D c

theorem hilbertExtension_legal (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) :
    hilbertExtension P hP D c hD ∈ hilbertLegalClosure (Set.Ici 1) := by
  apply Submodule.le_topologicalClosure
  change hilbertSequence (hilbertExtension P hP D c hD) ∈ legalSeedSpan (Set.Ici 1)
  rw [hilbertExtension_sequence]
  exact extension_mem_legal P hP D c hD


theorem hilbertExtension_head (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) (x : ℕ) (hx : x < P)
    (hhead : ∀ n, 0 < n → n ≤ x → (∑ d ∈ D, c d * grid d n) = 1)
    (n : ℕ) (hn : 0 < n) (hnx : n ≤ x) :
    hilbertSequence (hilbertExtension P hP D c hD) n = 1 := by
  rw [hilbertExtension_sequence, extension_below_period P hP D c hD n (hnx.trans_lt hx)]
  exact hhead n hn hnx

/-- The norm of the actual legal Hilbert vector, with every progression tail. -/
theorem hilbertExtension_error_norm (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d)
    (hdiv : ∀ d ∈ D, c d ≠ 0 → d ∣ P) :
    ‖hilbertOne - hilbertExtension P hP D c hD‖ ^ 2 =
      ∑ r : Fin P, progressionWeight P (r.val + 1) *
        (1 - extension P D c (r.val + 1)) ^ 2 := by
  let C := |(P : ℝ) * (∑ d ∈ D, c d / (d : ℝ))| + ∑ d ∈ D, |c d|
  have hb : ∀ n, |1 - extension P D c n| ≤ 1 + C := by
    intro n
    exact (abs_sub _ _).trans (add_le_add (by norm_num) (extension_bounded P hP D c hD n))
  have hs : hilbertSequence (hilbertOne - hilbertExtension P hP D c hD) =
      hilbertSequence hilbertOne - hilbertSequence (hilbertExtension P hP D c hD) :=
    hilbertSequenceLinear.map_sub _ _
  rw [hilbert_norm_weighted_sq, hs, hilbertOne_sequence, hilbertExtension_sequence]
  calc
    _ = paretoInner (fun n => 1 - extension P D c n)
          (fun n => 1 - extension P D c n) := by
      unfold paretoInner
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        simp [positiveWeight]
      · simp [zeroAnchor, hn, pow_two]
    _ = _ := periodic_paretoInner P hP _ hb
      (by intro n; rw [extension_periodic P D c hdiv])

/-- Terminal mass plus the interior residual energy equals the full NB loss. -/
theorem hilbertExtension_error_split (P : ℕ) (hP : 0 < P) (D : Finset ℕ)
    (c : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d)
    (hdiv : ∀ d ∈ D, c d ≠ 0 → d ∣ P) :
    ‖hilbertOne - hilbertExtension P hP D c hD‖ ^ 2 =
      progressionWeight P P +
      ∑ r : Fin P, if r.val + 1 < P then progressionWeight P (r.val + 1) *
        (1 - ∑ d ∈ D, c d * grid d (r.val + 1)) ^ 2 else 0 := by
  rw [hilbertExtension_error_norm P hP D c hD hdiv]
  have hsplit : ∀ r : Fin P, progressionWeight P (r.val + 1) *
      (1 - extension P D c (r.val + 1)) ^ 2 =
      (if r.val + 1 = P then progressionWeight P P else 0) +
      (if r.val + 1 < P then progressionWeight P (r.val + 1) *
        (1 - ∑ d ∈ D, c d * grid d (r.val + 1)) ^ 2 else 0) := by
    intro r
    by_cases hr : r.val + 1 < P
    · rw [if_pos hr, if_neg (by omega), zero_add, extension_below_period P hP D c hD _ hr]
    · have he : r.val + 1 = P := by omega
      rw [he, extension_terminal P D c hdiv]
      simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  let last : Fin P := ⟨P - 1, by omega⟩
  have he : ∀ r : Fin P, (r.val + 1 = P) ↔ r = last := by
    intro r
    constructor
    · intro hr
      apply Fin.ext
      dsimp [last]
      omega
    · rintro rfl
      dsimp [last]
      omega
  simp_rw [he]
  simp

end RiemannResearch.RH.Pareto.FloorProfileExtension
