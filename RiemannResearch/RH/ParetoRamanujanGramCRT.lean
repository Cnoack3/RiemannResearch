import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.IntegratedRamanujanGram
import RiemannResearch.RH.PrimePowerRamanujanSchur
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete CRT Gram entries and mean-one optimization for Ramanujan packets

Source: user-provided Mixed Conductor CRT research handoff, Section 4.
The weights are the actual Pareto pushforward. The common period can be
chosen separately for each pair of conductors.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra

theorem ramanujanPacketHilbert_inner_eq_crt (q r L : ℕ) (hL : 0 < L)
    (hq : q ∣ L) (hr : r ∣ L) :
    inner ℝ (ramanujanPacketHilbert q) (ramanujanPacketHilbert r) =
      ∑ a : Fin L, progressionWeight L (a.val + 1) *
        (ramanujanPacket q (a.val + 1) * ramanujanPacket r (a.val + 1)) := by
  rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert,
    hilbertSequence_ramanujanPacketHilbert]
  exact periodic_paretoInner_mixed L hL _ _ (ramanujanPacket_abs_le q) (ramanujanPacket_abs_le r)
    (ramanujanPacket_period_of_dvd q L hq) (ramanujanPacket_period_of_dvd r L hr)

theorem ramanujanPacketHilbert_inner_eq_lcm_digamma (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    let L := q.lcm r
    inner ℝ (ramanujanPacketHilbert q) (ramanujanPacketHilbert r) =
      ∑ a : Fin L, (1 / (L : ℝ) *
        ((Complex.digamma (((((a.val + 1 : ℕ) : ℝ) + 1) / (L : ℝ) : ℝ) : ℂ)).re -
         (Complex.digamma ((((a.val + 1 : ℕ) : ℝ) / (L : ℝ) : ℝ) : ℂ)).re)) *
        (ramanujanPacket q (a.val + 1) * ramanujanPacket r (a.val + 1)) := by
  intro L
  have hL : 0 < L := Nat.lcm_pos hq hr
  rw [ramanujanPacketHilbert_inner_eq_crt q r L hL (Nat.dvd_lcm_left q r) (Nat.dvd_lcm_right q r)]
  apply Finset.sum_congr rfl
  intro a _
  rw [progressionWeight_eq_digamma L (a.val + 1) hL (by omega) (by have := a.isLt; omega)]

/-- The inverse-Gram mean-one optimizer and its exact full-error remainder.
A single prime power in the finite window ensures positive source information. -/
theorem ramanujan_meanOne_optimal_error (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hsource : ∃ i : s, IsPrimePow i.val) :
    let source : s → ℝ := fun i => ArithmeticFunction.vonMangoldt i.val
    let b := ramanujanGramSolve s hs source
    let T := ∑ i : s, source i * b i
    let X := finiteSchurCombination (fun i : s => ramanujanPacketHilbert i.val)
    0 < T ∧ inner ℝ (X (fun i => b i / T)) hilbertOne = 1 ∧
      ∀ a, inner ℝ (X a) hilbertOne = 1 →
        ‖hilbertOne - X a‖ ^ 2 = 1 / T - 1 + ‖X a - X (fun i => b i / T)‖ ^ 2 := by
  intro source b T X
  let g := X b
  have hpacket (i : s) : inner ℝ (ramanujanPacketHilbert i.val) hilbertOne = source i := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]
  have hnormal (i : s) : inner ℝ (ramanujanPacketHilbert i.val) g = source i := by
    have h := congrFun (ramanujanGramSolve_normal_equations s hs source) i
    change (∑ j : s, paretoInner (ramanujanPacket i.val) (ramanujanPacket j.val) * b j) =
      source i at h
    change inner ℝ (ramanujanPacketHilbert i.val) (∑ j : s, b j • ramanujanPacketHilbert j.val)
      = source i
    simpa only [inner_sum, real_inner_smul_right, hilbert_inner_weighted,
      hilbertSequence_ramanujanPacketHilbert, mul_comm] using h
  have hxg (a : s → ℝ) : inner ℝ (X a) g = inner ℝ (X a) hilbertOne := by
    change inner ℝ (∑ i : s, a i • ramanujanPacketHilbert i.val) g =
      inner ℝ (∑ i : s, a i • ramanujanPacketHilbert i.val) hilbertOne
    simp only [sum_inner, real_inner_smul_left, hnormal, hpacket]
  have hT : inner ℝ g hilbertOne = T := by
    change inner ℝ (∑ i : s, b i • ramanujanPacketHilbert i.val) hilbertOne = _
    simp only [sum_inner, real_inner_smul_left, hpacket, T, mul_comm]
  have hnorm : ‖g‖ ^ 2 = T := by rw [← real_inner_self_eq_norm_sq, hxg b, hT]
  have hg : g ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hsource
    have hz := hnormal i
    rw [he, inner_zero_right] at hz
    exact (ArithmeticFunction.vonMangoldt_pos_iff.mpr hi).ne' hz.symm
  have hpos : 0 < T := by rw [← hnorm]; exact pow_pos (norm_pos_iff.mpr hg) _
  have hopt : X (fun i => b i / T) = (1 / T) • g := by
    change (∑ i : s, (b i / T) • ramanujanPacketHilbert i.val) =
      (1 / T) • ∑ i : s, b i • ramanujanPacketHilbert i.val
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  refine ⟨hpos, ?_, ?_⟩
  · rw [hopt, real_inner_smul_left, hT, div_mul_cancel₀ _ hpos.ne']
  · intro a ha
    have hg' : inner ℝ (X a) g = 1 := (hxg a).trans ha
    have he : ‖hilbertOne - X a‖ ^ 2 = ‖X a‖ ^ 2 - 1 := by
      rw [norm_sub_sq_real, hilbertOne_norm_sq, real_inner_comm (X a) hilbertOne, ha]
      ring
    rw [he, hopt, norm_sub_sq_real, real_inner_smul_right, hg', norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, hnorm]
    field_simp [hpos.ne']
    <;> ring

end RiemannResearch.RH.Pareto
