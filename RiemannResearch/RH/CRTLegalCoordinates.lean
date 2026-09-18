import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.ConditionalResidueGram
import RiemannResearch.RH.CRTPeriodicEnergy

/-!
Source: the CRT–Pareto exact-head research continuation, 2026-09-18.

Exact normalized residue coordinates for the legal head constraint. This
extends the existing forward balanced-coordinate result in ExactHeadCharges
to a full iff and the independent zero-period-mean moment constraint.
All statements use the actual residueFraction and periodMean definitions.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

/-- Finite Mobius inversion recovers an exact head from its arithmetic charges. -/
theorem exact_head_of_mobiusDifference
    {F : ℕ → ℝ} {Y : ℕ} (hzero : F 0 = 0)
    (hc : ∀ n, 0 < n → n ≤ Y →
      mobiusDifference n F = (ArithmeticFunction.moebius n : ℝ)) :
    ∀ n, 0 < n → n ≤ Y → F n = 1 := by
  let T : ℕ → ℝ := fun k => if k = 0 then 0 else 1
  have heq : ∀ n, n ≤ Y → F n = T n := by
    intro n
    induction n with
    | zero => intro _; simpa [T] using hzero
    | succ n ih =>
      intro hnY
      have hs : (∑ d ∈ (n + 1).divisors, mobiusDifference d F) =
          ∑ d ∈ (n + 1).divisors, mobiusDifference d T := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdp : 0 < d := Nat.pos_of_mem_divisors hd
        have hdN : d ≤ n + 1 :=
          Nat.le_of_dvd (Nat.succ_pos n) (Nat.dvd_of_mem_divisors hd)
        rw [hc d hdp (hdN.trans hnY)]
        symm
        exact mobiusDifference_one d hdp
      rw [sum_mobiusDifference F (n + 1) (Nat.succ_pos n),
        sum_mobiusDifference T (n + 1) (Nat.succ_pos n)] at hs
      simp only [Nat.add_sub_cancel] at hs
      rw [ih (by omega)] at hs
      linarith
  intro n hn hnY
  simpa [T, Nat.ne_of_gt hn] using heq n hnY

theorem exact_head_iff_mobiusDifference
    {F : ℕ → ℝ} {Y : ℕ} (hzero : F 0 = 0) :
    (∀ n, 0 < n → n ≤ Y → F n = 1) ↔
      ∀ n, 0 < n → n ≤ Y →
        mobiusDifference n F = (ArithmeticFunction.moebius n : ℝ) := by
  constructor
  · intro hh n hn hnY
    exact exact_head_mobiusDifference hzero hh hn hnY
  · exact exact_head_of_mobiusDifference hzero

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.CRTBlock
open Pareto ArithmeticCumulative
open ArithmeticCumulative.CesaroResidue
open RiemannResearch.Probability.ConditionalIID

/-- General finite normalized residue coordinates, excluding the invisible
modulus one by explicit hypotheses in the theorems below. -/
def normalizedResidueSynthesis (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ s, c d * residueFraction d n

theorem normalizedResidueSynthesis_unnormalized (s : Finset ℕ) (c : ℕ → ℝ) :
    normalizedResidueSynthesis s c =
      fun n => ∑ d ∈ s, (c d / (d : ℝ)) * Pareto.residue d n := by
  funext n
  unfold normalizedResidueSynthesis
  apply Finset.sum_congr rfl
  intro d _
  unfold residueFraction Pareto.residue
  ring

theorem normalizedResidueSynthesis_zero (s : Finset ℕ) (c : ℕ → ℝ) :
    normalizedResidueSynthesis s c 0 = 0 := by
  simp [normalizedResidueSynthesis, residueFraction]

theorem normalizedResidueSynthesis_one (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    normalizedResidueSynthesis s c 1 = ∑ d ∈ s, c d / (d : ℝ) := by
  unfold normalizedResidueSynthesis
  apply Finset.sum_congr rfl
  intro d hd
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (by have := hs d hd; omega : 1 < d)]
  push_cast
  ring

/-- The actual arithmetic charge extracts a normalized coefficient exactly. -/
theorem normalizedResidueSynthesis_mobiusDifference
    (s : Finset ℕ) (c : ℕ → ℝ) (m : ℕ) (hm : 1 < m) :
    mobiusDifference m (normalizedResidueSynthesis s c) =
      -(if m ∈ s then c m else 0) := by
  classical
  rw [normalizedResidueSynthesis_unnormalized, mobiusDifference_sum]
  simp_rw [mobiusDifference_residue m _ hm]
  by_cases hms : m ∈ s
  · rw [if_pos hms, Finset.sum_eq_single m]
    · simp only [ite_true]
      have hmR : (m : ℝ) ≠ 0 := by positivity
      field_simp
    · intro d hd hdm
      simp [Ne.symm hdm]
    · exact fun h => False.elim (h hms)
  · rw [if_neg hms, neg_zero]
    apply Finset.sum_eq_zero
    intro d hd
    have hmd : m ≠ d := by intro he; subst d; exact hms hd
    simp [hmd]

/-- Exact head interpolation is equivalent to forced low Möbius coefficients
and one reciprocal moment. The coefficient at modulus one is not a variable. -/
theorem normalizedResidueSynthesis_exact_head_iff
    (s : Finset ℕ) (c : ℕ → ℝ) (Y : ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hY : 0 < Y) :
    (∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 1) ↔
      (∑ d ∈ s, c d / (d : ℝ)) = 1 ∧
      ∀ n, 1 < n → n ≤ Y →
        (if n ∈ s then c n else 0) = -(ArithmeticFunction.moebius n : ℝ) := by
  classical
  constructor
  · intro hh
    refine ⟨?_, ?_⟩
    · rw [← normalizedResidueSynthesis_one s c hs]
      exact hh 1 (by omega) hY
    · intro n hn hnY
      have hc := exact_head_mobiusDifference
        (normalizedResidueSynthesis_zero s c) hh (by omega) hnY
      rw [normalizedResidueSynthesis_mobiusDifference s c n hn] at hc
      linarith
  · rintro ⟨hm, hc⟩
    apply exact_head_of_mobiusDifference (normalizedResidueSynthesis_zero s c)
    intro n hn hnY
    by_cases hn1 : n = 1
    · subst n
      have hone : normalizedResidueSynthesis s c 1 = 1 := by
        rw [normalizedResidueSynthesis_one s c hs, hm]
      simpa [mobiusDifference, normalizedResidueSynthesis_zero] using hone
    · have hn2 : 1 < n := by omega
      rw [normalizedResidueSynthesis_mobiusDifference s c n hn2, hc n hn2 hnY]
      ring

theorem normalizedResidueSynthesis_legal
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ d ∈ s, 2 ≤ d) :
    normalizedResidueSynthesis s c ∈ legalSeedSpan (Set.Ici 1) := by
  rw [normalizedResidueSynthesis_unnormalized]
  exact finite_residueCombination_mem_full_legal s (fun d => c d / (d : ℝ))
    (fun d hd => by have := hs d hd; omega)

theorem normalizedResidueSynthesis_periodic
    (s : Finset ℕ) (c : ℕ → ℝ) (Q : ℕ)
    (hdiv : ∀ d ∈ s, d ∣ Q) (n : ℕ) :
    normalizedResidueSynthesis s c (n + Q) = normalizedResidueSynthesis s c n := by
  unfold normalizedResidueSynthesis
  apply Finset.sum_congr rfl
  intro d hd
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd (hdiv d hd)]

/-- The ordinary coefficient moment and reciprocal moment determine the mean. -/
theorem normalizedResidueSynthesis_periodMean
    (s : Finset ℕ) (c : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hs : ∀ d ∈ s, 2 ≤ d) (hdiv : ∀ d ∈ s, d ∣ Q) :
    periodMean (normalizedResidueSynthesis s c) Q =
      ((∑ d ∈ s, c d) - (∑ d ∈ s, c d / (d : ℝ))) / 2 := by
  have hmean : periodMean (normalizedResidueSynthesis s c) Q =
      cesaro (normalizedResidueSynthesis s c) Q := by
    rw [cesaro_eq_cumulative]
    rfl
  rw [hmean]
  change cesaro (fun n => ∑ d ∈ s, c d * residueFraction d n) Q = _
  rw [cesaro_finsetCombination]
  calc
    _ = ∑ d ∈ s, (c d - c d / (d : ℝ)) / 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdp : 0 < d := by have := hs d hd; omega
      have hdivQ : Q / d * d = Q := Nat.div_mul_cancel (hdiv d hd)
      have hk : 0 < Q / d := Nat.div_pos (Nat.le_of_dvd hQ (hdiv d hd)) hdp
      have hces := cesaro_residue_complete_periods d (Q / d) hdp hk
      rw [hdivQ] at hces
      rw [hces]
      have hdR : (d : ℝ) ≠ 0 := by positivity
      field_simp
    _ = _ := by rw [← Finset.sum_div, Finset.sum_sub_distrib]

/-- Complete finite arithmetic feasibility, with both necessary moments. -/
theorem normalizedResidueSynthesis_zeroMean_exact_head_iff
    (s : Finset ℕ) (c : ℕ → ℝ) (Y Q : ℕ) (hY : 0 < Y) (hQ : 0 < Q)
    (hs : ∀ d ∈ s, 2 ≤ d) (hdiv : ∀ d ∈ s, d ∣ Q) :
    ((∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 1) ∧
      periodMean (normalizedResidueSynthesis s c) Q = 0) ↔
      (∑ d ∈ s, c d / (d : ℝ)) = 1 ∧ (∑ d ∈ s, c d) = 1 ∧
      ∀ n, 1 < n → n ≤ Y →
        (if n ∈ s then c n else 0) = -(ArithmeticFunction.moebius n : ℝ) := by
  rw [normalizedResidueSynthesis_exact_head_iff s c Y hs hY,
    normalizedResidueSynthesis_periodMean s c Q hQ hs hdiv]
  constructor
  · rintro ⟨⟨hrec, hlo⟩, hmean⟩
    exact ⟨hrec, by linarith, hlo⟩
  · rintro ⟨hrec, htotal, hlo⟩
    exact ⟨⟨hrec, hlo⟩, by rw [hrec, htotal]; ring⟩

/-- Every low prime is forced into the actual coefficient support and hence
into its common CRT conductor. No asymptotic theorem is used. -/
theorem exact_head_prime_dvd_support_conductor
    (s : Finset ℕ) (c : ℕ → ℝ) (Y Q p : ℕ)
    (hY : 0 < Y) (hs : ∀ d ∈ s, 2 ≤ d) (hdiv : ∀ d ∈ s, d ∣ Q)
    (hh : ∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 1)
    (hp : p.Prime) (hpY : p ≤ Y) : p ∣ Q := by
  have hc := ((normalizedResidueSynthesis_exact_head_iff s c Y hs hY).mp hh).2
    p hp.one_lt hpY
  have hps : p ∈ s := by
    by_contra hn
    rw [if_neg hn] at hc
    have hmu : (ArithmeticFunction.moebius p : ℝ) = -1 := by
      exact_mod_cast ArithmeticFunction.moebius_apply_prime hp
    rw [hmu] at hc
    norm_num at hc
  exact hdiv p hps

/-- The exact ordinary increment keeps all signed divisor coefficients. -/
theorem normalizedResidueSynthesis_difference
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ d ∈ s, 2 ≤ d)
    (n : ℕ) (hn : 0 < n) :
    normalizedResidueSynthesis s c n - normalizedResidueSynthesis s c (n - 1) =
      (∑ d ∈ s, c d / (d : ℝ)) -
        ∑ d ∈ s, if d ∣ n then c d else 0 := by
  rw [normalizedResidueSynthesis_unnormalized]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_sub, residue_difference d n hn]
  have hdR : (d : ℝ) ≠ 0 := by have := hs d hd; positivity
  by_cases hdn : d ∣ n
  · rw [if_pos hdn, if_pos hdn]
    field_simp
  · simp [hdn]

/-- Legal CRT increments cannot be chosen independently inside a gcd class. -/
theorem normalizedResidueSynthesis_difference_gcd_invariant
    (s : Finset ℕ) (c : ℕ → ℝ) (Q : ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hdiv : ∀ d ∈ s, d ∣ Q)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hg : Nat.gcd n Q = Nat.gcd m Q) :
    normalizedResidueSynthesis s c n - normalizedResidueSynthesis s c (n - 1) =
      normalizedResidueSynthesis s c m - normalizedResidueSynthesis s c (m - 1) := by
  rw [normalizedResidueSynthesis_difference s c hs n hn,
    normalizedResidueSynthesis_difference s c hs m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdQ := hdiv d hd
  have he : d ∣ n ↔ d ∣ m := by
    constructor
    · intro hdn
      have hh := Nat.dvd_gcd hdn hdQ
      rw [hg] at hh
      exact dvd_trans hh (Nat.gcd_dvd_left m Q)
    · intro hdm
      have hh := Nat.dvd_gcd hdm hdQ
      rw [← hg] at hh
      exact dvd_trans hh (Nat.gcd_dvd_left n Q)
  simp only [he]

/-- Defect coordinates obey the exact same arithmetic compatibility through
their second differences. The period mean cancels with its sign intact. -/
theorem periodDefect_second_difference (F : ℕ → ℝ) (Q n : ℕ) :
    periodDefect F Q (n + 2) - 2 * periodDefect F Q (n + 1) + periodDefect F Q n =
      F (n + 2) - F (n + 1) := by
  unfold periodDefect cumulative
  rw [show n + 2 = (n + 1) + 1 by omega]
  simp only [Finset.sum_range_succ]
  push_cast
  ring

theorem normalizedResidueSynthesis_defect_gcd_invariant
    (s : Finset ℕ) (c : ℕ → ℝ) (Q : ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hdiv : ∀ d ∈ s, d ∣ Q)
    (n m : ℕ) (hg : Nat.gcd (n + 2) Q = Nat.gcd (m + 2) Q) :
    periodDefect (normalizedResidueSynthesis s c) Q (n + 2) -
        2 * periodDefect (normalizedResidueSynthesis s c) Q (n + 1) +
          periodDefect (normalizedResidueSynthesis s c) Q n =
      periodDefect (normalizedResidueSynthesis s c) Q (m + 2) -
        2 * periodDefect (normalizedResidueSynthesis s c) Q (m + 1) +
          periodDefect (normalizedResidueSynthesis s c) Q m := by
  rw [periodDefect_second_difference, periodDefect_second_difference]
  simpa only [show n + 2 - 1 = n + 1 by omega,
    show m + 2 - 1 = m + 1 by omega] using
    normalizedResidueSynthesis_difference_gcd_invariant s c Q hs hdiv
      (n + 2) (m + 2) (by omega) (by omega) hg

private theorem sum_Icc_two_split (a : ℕ → ℝ) (Y D : ℕ)
    (hY : 0 < Y) (hYD : Y ≤ D) :
    (∑ d ∈ Finset.Icc 2 D, a d) =
      (∑ d ∈ Finset.Icc 2 Y, a d) +
        ∑ d ∈ Finset.Icc (Y + 1) D, a d := by
  have hset : Finset.Icc 2 D =
      Finset.Icc 2 Y ∪ Finset.Icc (Y + 1) D := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 2 Y) (Finset.Icc (Y + 1) D) := by
    apply Finset.disjoint_left.mpr
    intro d hd he
    have := (Finset.mem_Icc.mp hd).2
    have := (Finset.mem_Icc.mp he).1
    omega
  rw [hset, Finset.sum_union hdis]

private theorem sum_Icc_one_split (a : ℕ → ℝ) (Y : ℕ) (hY : 0 < Y) :
    (∑ d ∈ Finset.Icc 1 Y, a d) = a 1 + ∑ d ∈ Finset.Icc 2 Y, a d := by
  have hset : Finset.Icc 1 Y = insert 1 (Finset.Icc 2 Y) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]

/-- The two high-range moment obligations are exact: the unrestricted Mertens
sum and reciprocal Möbius sum occur with their original signs. -/
theorem exact_zeroMean_head_high_moments
    (c : ℕ → ℝ) (Y D Q : ℕ) (hY : 0 < Y) (hYD : Y ≤ D) (hQ : 0 < Q)
    (hdiv : ∀ d ∈ Finset.Icc 2 D, d ∣ Q)
    (hh : ∀ n, 0 < n → n ≤ Y →
      normalizedResidueSynthesis (Finset.Icc 2 D) c n = 1)
    (hm : periodMean (normalizedResidueSynthesis (Finset.Icc 2 D) c) Q = 0) :
    (∑ d ∈ Finset.Icc (Y + 1) D, c d / (d : ℝ)) =
        (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) ∧
      (∑ d ∈ Finset.Icc (Y + 1) D, c d) =
        (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ)) := by
  have hs : ∀ d ∈ Finset.Icc 2 D, 2 ≤ d :=
    fun d hd => (Finset.mem_Icc.mp hd).1
  obtain ⟨hrec, htotal, hlow⟩ :=
    (normalizedResidueSynthesis_zeroMean_exact_head_iff
      (Finset.Icc 2 D) c Y Q hY hQ hs hdiv).mp ⟨hh, hm⟩
  have hc (d : ℕ) (hd : d ∈ Finset.Icc 2 Y) :
      c d = -(ArithmeticFunction.moebius d : ℝ) := by
    have hdp : 1 < d := by have := (Finset.mem_Icc.mp hd).1; omega
    have hdY : d ≤ Y := (Finset.mem_Icc.mp hd).2
    have hdD : d ∈ Finset.Icc 2 D :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, hdY.trans hYD⟩
    simpa only [if_pos hdD] using hlow d hdp hdY
  have hlowRec : (∑ d ∈ Finset.Icc 2 Y, c d / (d : ℝ)) =
      -(∑ d ∈ Finset.Icc 2 Y, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hc d hd]
    ring
  have hlowTotal : (∑ d ∈ Finset.Icc 2 Y, c d) =
      -(∑ d ∈ Finset.Icc 2 Y, (ArithmeticFunction.moebius d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hc
  have hmuRec : (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      1 + ∑ d ∈ Finset.Icc 2 Y,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
    rw [sum_Icc_one_split _ Y hY]
    norm_num
  have hmuTotal : (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ)) =
      1 + ∑ d ∈ Finset.Icc 2 Y, (ArithmeticFunction.moebius d : ℝ) := by
    rw [sum_Icc_one_split _ Y hY]
    norm_num
  rw [sum_Icc_two_split _ Y D hY hYD, hlowRec] at hrec
  rw [sum_Icc_two_split _ Y D hY hYD, hlowTotal] at htotal
  constructor <;> linarith

end RiemannResearch.RH.CRTBlock
