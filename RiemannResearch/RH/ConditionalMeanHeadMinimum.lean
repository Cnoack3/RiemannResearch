import RiemannResearch.RH.ConditionalMeanEnergy
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The actual minimum conditional-mean energy of exact legal heads

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Sections 7 and 10. We prove finite interpolation, define the genuine infimum,
and retain exact energy and tail identities. The RH implication from a uniform
bound is assembled in `ConditionalMeanMinimumCriteria`. No bounded arithmetic
interpolation family is assumed as an axiom.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- Full positive-integer residue dictionary, expressed through the existing legal span. -/
def conditionalHeadClass (N : ℕ) : Set (ℕ → ℝ) :=
  {g | g ∈ legalSeedSpan (Set.Ici 1) ∧ ∀ n, 0 < n → n ≤ N → g n = 1}

private theorem residue_mem_full_legal (d : ℕ) (hd : 0 < d) :
    residue d ∈ legalSeedSpan (Set.Ici 1) := by
  simpa only [dilation_one] using
    (dilation_generator_mem (Set.Ici 1) (a := d) (m := 1)
      (show d ∈ Set.Ici 1 from hd) (by omega))

/-- Unconditional finite interpolation. No norm estimate is built into this statement. -/
theorem exists_full_legal_head (u : ℕ → ℝ) (N : ℕ) :
    ∃ g ∈ legalSeedSpan (Set.Ici 1), ∀ n, 0 < n → n ≤ N → g n = u n := by
  induction N with
  | zero => exact ⟨0, (legalSeedSpan _).zero_mem, by intro n hn hnN; omega⟩
  | succ N ih =>
    obtain ⟨g, hg, hhead⟩ := ih
    let v : ℕ → ℝ := residue (N + 2) - residue (N + 1)
    have hv : v ∈ legalSeedSpan (Set.Ici 1) :=
      (legalSeedSpan _).sub_mem (residue_mem_full_legal _ (by omega))
        (residue_mem_full_legal _ (by omega))
    have hvlow (n : ℕ) (hn : n ≤ N) : v n = 0 := by
      simp [v, residue, Nat.mod_eq_of_lt (show n < N + 2 by omega),
        Nat.mod_eq_of_lt (show n < N + 1 by omega)]
    have hvdiag : v (N + 1) = (N + 1 : ℕ) := by
      simp [v, residue, Nat.mod_eq_of_lt (show N + 1 < N + 2 by omega)]
    let c : ℝ := (u (N + 1) - g (N + 1)) / ((N + 1 : ℕ) : ℝ)
    refine ⟨g + c • v, (legalSeedSpan _).add_mem hg ((legalSeedSpan _).smul_mem c hv), ?_⟩
    intro n hn hnN
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases he : n = N + 1
    · subst n
      rw [hvdiag]
      dsimp [c]
      have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · rw [hvlow n (by omega), mul_zero, add_zero]
      exact hhead n hn (by omega)

theorem conditionalHeadClass_nonempty (N : ℕ) : (conditionalHeadClass N).Nonempty := by
  obtain ⟨g, hg, hh⟩ := exists_full_legal_head (fun _ => 1) N
  exact ⟨g, hg, hh⟩

/-- Actual legal energy values; their nonemptiness is proved above. -/
def conditionalHeadEnergies (N : ℕ) : Set ℝ :=
  conditionalMeanSquare '' conditionalHeadClass N

/-- The unrestricted infimum over genuine globally legal exact heads. -/
def conditionalHeadMinimum (N : ℕ) : ℝ := sInf (conditionalHeadEnergies N)

theorem conditionalHeadEnergies_nonempty (N : ℕ) : (conditionalHeadEnergies N).Nonempty :=
  (conditionalHeadClass_nonempty N).image _

theorem conditionalHeadEnergies_bddBelow (N : ℕ) : BddBelow (conditionalHeadEnergies N) := by
  refine ⟨0, ?_⟩
  rintro x ⟨g, hg, rfl⟩
  exact conditionalMeanSquare_nonneg g

theorem conditionalHeadMinimum_nonneg (N : ℕ) : 0 ≤ conditionalHeadMinimum N := by
  apply le_csInf (conditionalHeadEnergies_nonempty N)
  rintro x ⟨g, hg, rfl⟩
  exact conditionalMeanSquare_nonneg g

theorem conditionalHeadMinimum_le (N : ℕ) {g : ℕ → ℝ}
    (hg : g ∈ conditionalHeadClass N) : conditionalHeadMinimum N ≤ conditionalMeanSquare g :=
  csInf_le (conditionalHeadEnergies_bddBelow N) ⟨g, hg, rfl⟩

/-- Arbitrarily accurate infimum witnesses remain actual finite legal functions. -/
theorem exists_head_energy_lt (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ conditionalHeadClass N, conditionalMeanSquare g < conditionalHeadMinimum N + ε := by
  have hlt : sInf (conditionalHeadEnergies N) < conditionalHeadMinimum N + ε := by
    change conditionalHeadMinimum N < conditionalHeadMinimum N + ε
    linarith
  obtain ⟨x, hx, hxlt⟩ := (csInf_lt_iff (conditionalHeadEnergies_bddBelow N)
    (conditionalHeadEnergies_nonempty N)).mp hlt
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨g, hg, hxlt⟩

theorem conditionalHeadMinimum_mono : Monotone conditionalHeadMinimum := by
  intro N M hNM
  apply le_csInf (conditionalHeadEnergies_nonempty M)
  rintro x ⟨g, hg, rfl⟩
  apply conditionalHeadMinimum_le N
  exact ⟨hg.1, fun n hn hnN => hg.2 n hn (hnN.trans hNM)⟩

/-- Uniform bounds for the infima really supply bounded legal witnesses. -/
theorem bounded_minimum_iff_bounded_legal_heads :
    (∃ C : ℝ, ∀ N, conditionalHeadMinimum N ≤ C) ↔
      ∃ C : ℝ, ∀ N, ∃ g ∈ conditionalHeadClass N, conditionalMeanSquare g ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 1, ?_⟩
    intro N
    obtain ⟨g, hg, he⟩ := exists_head_energy_lt N 1 (by norm_num)
    exact ⟨g, hg, by linarith [hC N]⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro N
    obtain ⟨g, hg, he⟩ := hC N
    exact (conditionalHeadMinimum_le N hg).trans he

/-- Exact mass of the first `N` positive latent endpoints. -/
theorem conditionalWeight_sum_range (N : ℕ) :
    (∑ k ∈ Finset.range N, conditionalWeight k) = (N : ℝ) / ((N : ℝ) + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hq : conditionalWeight N = 2 / (((N : ℝ) + 2) * ((N : ℝ) + 3)) := by
      unfold conditionalWeight mixtureWeight
      push_cast
      ring
    rw [hq]
    push_cast
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
    have h3' : (N : ℝ) + 1 + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem cesaro_eq_one_of_exact_head (N : ℕ) {g : ℕ → ℝ}
    (hhead : ∀ n, 0 < n → n ≤ N → g n = 1)
    (t : ℕ) (ht : 0 < t) (htN : t ≤ N) : cesaro g t = 1 := by
  have h := mean_eq_one_of_head (fun n => (g n : ℂ)) t ht
    (fun n hn hnt => by simp only [hhead n hn (hnt.trans htN), Complex.ofReal_one])
  rw [mean_ofReal] at h
  exact_mod_cast h

/-- Exact head energy plus the actual signed witness's nonnegative tail. -/
theorem conditionalMeanSquare_exact_head_split (N : ℕ) {g : ℕ → ℝ}
    (hg : g ∈ conditionalHeadClass N) :
    conditionalMeanSquare g = (N : ℝ) / ((N : ℝ) + 2) +
      ∑' k : ℕ, conditionalWeight (k + N) * (cesaro g (k + N + 1)) ^ 2 := by
  have hs := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hg.1).sum_add_tsum_nat_add N
  have hhead : (∑ k ∈ Finset.range N, conditionalWeight k * (cesaro g (k + 1)) ^ 2) =
      (N : ℝ) / ((N : ℝ) + 2) := by
    rw [← conditionalWeight_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [cesaro_eq_one_of_exact_head N hg.2 (k + 1) (Nat.succ_pos _)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hk))]
    simp
  rw [hhead] at hs
  exact hs.symm

/-- Every actual legal exact head contains the compulsory head mass. -/
theorem conditionalMeanSquare_ge_head_mass (N : ℕ) {g : ℕ → ℝ}
    (hg : g ∈ conditionalHeadClass N) :
    (N : ℝ) / ((N : ℝ) + 2) ≤ conditionalMeanSquare g := by
  rw [conditionalMeanSquare_exact_head_split N hg]
  exact le_add_of_nonneg_right
    (tsum_nonneg fun k => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))

/-- The exact unconditional lower bound for the genuine legal infimum. -/
theorem conditionalHeadMinimum_ge_head_mass (N : ℕ) :
    (N : ℝ) / ((N : ℝ) + 2) ≤ conditionalHeadMinimum N := by
  apply le_csInf (conditionalHeadEnergies_nonempty N)
  rintro x ⟨g, hg, rfl⟩
  exact conditionalMeanSquare_ge_head_mass N hg

/-- Exact remaining mass after the compulsory head. -/
theorem conditionalWeight_tsum_tail (N : ℕ) :
    (∑' k : ℕ, conditionalWeight (k + N)) = 2 / ((N : ℝ) + 2) := by
  have hs : Summable conditionalWeight := hasSum_mixtureWeight.summable
  have ht := hs.sum_add_tsum_nat_add N
  have hall : (∑' k : ℕ, conditionalWeight k) = 1 := hasSum_mixtureWeight.tsum_eq
  rw [conditionalWeight_sum_range, hall] at ht
  have hid : (N : ℝ) / ((N : ℝ) + 2) + 2 / ((N : ℝ) + 2) = 1 := by
    have hn : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  linarith

/-- Summability is proved before using the total error as an ordinary real series. -/
theorem conditionalMeanError_summable_of_energy {g : ℕ → ℝ}
    (hE : Summable (fun k : ℕ => conditionalWeight k * (cesaro g (k + 1)) ^ 2)) :
    Summable (fun k : ℕ => conditionalWeight k * (1 - cesaro g (k + 1)) ^ 2) := by
  have hq : Summable conditionalWeight := hasSum_mixtureWeight.summable
  apply ((hE.mul_left 2).add (hq.mul_left 2)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))]
  calc
    _ ≤ conditionalWeight k * (2 * (cesaro g (k + 1)) ^ 2 + 2) := by
      apply mul_le_mul_of_nonneg_left _ (conditionalWeight_pos k).le
      nlinarith [sq_nonneg (cesaro g (k + 1) + 1)]
    _ = _ := by ring

theorem conditionalMeanError_exact_head_tail (N : ℕ) {g : ℕ → ℝ}
    (hg : g ∈ conditionalHeadClass N) :
    conditionalMeanError g =
      ∑' k : ℕ, conditionalWeight (k + N) * (1 - cesaro g (k + N + 1)) ^ 2 := by
  have hE := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hg.1
  have hs := (conditionalMeanError_summable_of_energy hE).sum_add_tsum_nat_add N
  have hhead : (∑ k ∈ Finset.range N,
      conditionalWeight k * (1 - cesaro g (k + 1)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [cesaro_eq_one_of_exact_head N hg.2 (k + 1) (Nat.succ_pos _)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hk))]
    ring
  rw [hhead, zero_add] at hs
  exact hs.symm

/-- Near-minimum energy yields small approximation error by controlling
only the two tails. -/
theorem conditionalMeanError_le_exact_head_energy (N : ℕ) {g : ℕ → ℝ}
    (hg : g ∈ conditionalHeadClass N) :
    conditionalMeanError g ≤
      2 * conditionalMeanSquare g + 2 - 4 * ((N : ℝ) / ((N : ℝ) + 2)) := by
  have hE := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hg.1
  have hq : Summable conditionalWeight := hasSum_mixtureWeight.summable
  have hEt : Summable (fun k : ℕ =>
      conditionalWeight (k + N) * (cesaro g (k + N + 1)) ^ 2) :=
    hE.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hqt : Summable (fun k : ℕ => conditionalWeight (k + N)) :=
    hq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hRt : Summable (fun k : ℕ =>
      conditionalWeight (k + N) * (1 - cesaro g (k + N + 1)) ^ 2) :=
    (conditionalMeanError_summable_of_energy hE).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hbound : (∑' k : ℕ,
      conditionalWeight (k + N) * (1 - cesaro g (k + N + 1)) ^ 2) ≤
      ∑' k : ℕ, (2 * (conditionalWeight (k + N) * (cesaro g (k + N + 1)) ^ 2) +
        2 * conditionalWeight (k + N)) := by
    apply Summable.tsum_le_tsum _ hRt ((hEt.mul_left 2).add (hqt.mul_left 2))
    intro k
    calc
      _ ≤ conditionalWeight (k + N) * (2 * (cesaro g (k + N + 1)) ^ 2 + 2) := by
        apply mul_le_mul_of_nonneg_left _ (conditionalWeight_pos _).le
        nlinarith [sq_nonneg (cesaro g (k + N + 1) + 1)]
      _ = _ := by ring
  rw [(hEt.mul_left 2).tsum_add (hqt.mul_left 2), tsum_mul_left, tsum_mul_left,
    ← conditionalMeanError_exact_head_tail N hg] at hbound
  have hsplit := conditionalMeanSquare_exact_head_split N hg
  have hmass := hq.sum_add_tsum_nat_add N
  have hall : (∑' k : ℕ, conditionalWeight k) = 1 := hasSum_mixtureWeight.tsum_eq
  rw [conditionalWeight_sum_range, hall] at hmass
  linarith

/-- The manuscript's explicit `8/(N+2)` error bound for an actual exact
legal witness with conditional-mean energy at most one. -/
theorem conditionalMeanError_le_eight_div_of_head_energy_le_one (N : ℕ) {g : ℕ → ℝ}
    (hg : g ∈ conditionalHeadClass N) (hE : conditionalMeanSquare g ≤ 1) :
    conditionalMeanError g ≤ 8 / ((N : ℝ) + 2) := by
  have h := conditionalMeanError_le_exact_head_energy N hg
  have hid : 4 - 4 * ((N : ℝ) / ((N : ℝ) + 2)) = 8 / ((N : ℝ) + 2) := by
    have hn : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  linarith

end RiemannResearch.RH.Pareto
