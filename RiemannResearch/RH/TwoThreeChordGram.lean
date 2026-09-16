import RiemannResearch.RH.TwoThreePacketRelations
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.AdjacentPacketNormBounds
import RiemannResearch.Analysis.ProjectionChordObservability
/-!
# Exact signed two-seed chord kernels and aligned energy

Source: user-provided argument,
RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md,
Sections 23--24, 29. The source supports the statements and proof strategy.

The finite periodic/digamma formula uses the full infinite Pareto weights.
The aligned-dyadic logarithmic bound is proved via exact dilation and the
existing adjacent-packet bounds. Its explicit constant differs from 160.
The Mellin identity here has Re(s)>1/2: the critical-line Plancherel identity
is separately recorded as an outstanding formalization obligation.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto.AdjacentPacket
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ProjectionChordObservability

theorem digit_period_of_dvd (p m L : ℕ) (hm : 0 < m)
    (h : p*m ∣ L) (k : ℕ) :
    digitSequence p m (k+L) = digitSequence p m k := by
  obtain ⟨q, rfl⟩ := h
  exact periodic_add_mul (p*m) (digitSequence p m) (digitSequence_periodic p m hm) k q

theorem generator_gram_periodic (p q m n L : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n)
    (hL : 0 < L) (hmL : p*m ∣ L) (hnL : q*n ∣ L) :
    inner ℝ (generator p m hp hm) (generator q n hq hn) =
      (m:ℝ)*(n:ℝ) * ∑ r : Fin L, progressionWeight L (r.val+1) *
        (digitSequence p m (r.val+1) * digitSequence q n (r.val+1)) := by
  rw [generator_eq_scaled_digit, generator_eq_scaled_digit,
    real_inner_smul_left, real_inner_smul_right,
    hilbert_inner_weighted, hilbertSequence_digitHilbert, hilbertSequence_digitHilbert,
    periodic_paretoInner_mixed L hL (digitSequence p m) (digitSequence q n)
      (digitSequence_abs_le p m hp) (digitSequence_abs_le q n hq)
      (digit_period_of_dvd p m L hm hmL) (digit_period_of_dvd q n L hn hnL)]
  ring

def chord (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : ThresholdHilbert :=
  generator 3 (2*b) (by omega) (by omega) -
    generator 3 (2*a) (by omega) (by omega)

theorem chord_gram_exact (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    inner ℝ (chord a b ha hb) (chord c d hc hd) =
      inner ℝ (generator 3 (2*b) (by omega) (by omega))
        (generator 3 (2*d) (by omega) (by omega)) -
      inner ℝ (generator 3 (2*b) (by omega) (by omega))
        (generator 3 (2*c) (by omega) (by omega)) -
      inner ℝ (generator 3 (2*a) (by omega) (by omega))
        (generator 3 (2*d) (by omega) (by omega)) +
      inner ℝ (generator 3 (2*a) (by omega) (by omega))
        (generator 3 (2*c) (by omega) (by omega)) :=
  chord_gram _ _ _ _

theorem chord_mean_zero (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    inner ℝ (chord a b ha hb) hilbertOne = 0 := by
  unfold chord generator
  rw [inner_sub_left, hilbert_inner_one, hilbert_inner_one,
    hilbertDilation_mean, hilbertDilation_mean]
  ring

theorem chord_source_correlation (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    inner ℝ (RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne) (chord a b ha hb) =
      -inner ℝ (P.starProjection hilbertOne) (chord a b ha hb) := by
  have hz : inner ℝ hilbertOne (chord a b ha hb) = 0 := by
    rw [real_inner_comm, chord_mean_zero]
  simp only [RiemannResearch.Analysis.ProjectionSourceImprovement.residual, inner_sub_left, hz, zero_sub]

theorem chord_mellin (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (s : ℂ) (hs : (1/2:ℝ) < s.re) (hs1 : s ≠ 1) :
    paretoMellin (chord a b ha hb) s =
      riemannZeta s / s * (1 - (3:ℂ)^(1-s)) *
        (((2*b:ℕ):ℂ)^(1-s) - ((2*a:ℕ):ℂ)^(1-s)) := by
  unfold chord generator
  have hsub (f g : ThresholdHilbert) :
      paretoMellin (f-g) s = paretoMellin f s-paretoMellin g s :=
    (paretoMellinContinuous s hs).map_sub f g
  rw [hsub,
    paretoMellin_generator_zeta 3 (2*b) (by omega) (by omega) s hs hs1,
    paretoMellin_generator_zeta 3 (2*a) (by omega) (by omega) s hs hs1]
  ring

theorem chord_add (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    chord a b ha hb + chord b c hb hc = chord a c ha hc := by
  unfold chord
  abel

theorem generator_gram_lcm (p q m n : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n) :
    inner ℝ (generator p m hp hm) (generator q n hq hn) =
      (m:ℝ)*(n:ℝ) * ∑ r : Fin (Nat.lcm (p*m) (q*n)),
        progressionWeight (Nat.lcm (p*m) (q*n)) (r.val+1) *
        (digitSequence p m (r.val+1) * digitSequence q n (r.val+1)) :=
  generator_gram_periodic p q m n _ hp hq hm hn
    (Nat.lcm_pos (Nat.mul_pos hp hm) (Nat.mul_pos hq hn))
    (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _)

theorem generator_gram_digamma (p q m n L : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n)
    (hL : 0 < L) (hmL : p*m ∣ L) (hnL : q*n ∣ L) :
    inner ℝ (generator p m hp hm) (generator q n hq hn) =
      (m:ℝ)*(n:ℝ) * ∑ r : Fin L,
        (1/(L:ℝ) *
          ((Complex.digamma ((((r.val+1:ℕ):ℝ)+1)/(L:ℝ) : ℂ)).re -
           (Complex.digamma (((r.val+1:ℕ):ℝ)/(L:ℝ) : ℂ)).re)) *
        (digitSequence p m (r.val+1) * digitSequence q n (r.val+1)) := by
  rw [generator_gram_periodic p q m n L hp hq hm hn hL hmL hnL]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [progressionWeight_eq_digamma L (r.val+1) hL (by omega) (by omega)]
  push_cast
  rfl

theorem chord_dilation (L a b : ℕ) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) :
    chord (L*a) (L*b) (Nat.mul_pos hL ha) (Nat.mul_pos hL hb) =
      hilbertDilation L hL (chord a b ha hb) := by
  have hsub (f g : ThresholdHilbert) :
      hilbertDilation L hL (f-g) =
        hilbertDilation L hL f-hilbertDilation L hL g :=
    (hilbertDilationLinear L hL).map_sub f g
  unfold chord generator
  simp only [hsub, hilbertDilation_comp, mul_left_comm]

theorem chord_norm_sq_dilation (L a b : ℕ)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) :
    ‖chord (L*a) (L*b) (Nat.mul_pos hL ha) (Nat.mul_pos hL hb)‖^2 =
      (L:ℝ)*‖chord a b ha hb‖^2 := by
  rw [chord_dilation L a b hL ha hb, hilbertDilation_norm_sq]

theorem unit_chord_log_bound (k : ℕ) (hk : 0 < k) :
    ‖chord k (k+1) hk (by omega)‖^2 ≤
      8*Real.log ((2*k+1:ℕ):ℝ) +
        8*‖digitHilbert 3 1 (by omega) (by omega)‖^2+996 := by
  let x := packet 3 (2*k) (by omega) (by omega)
  let y := packet 3 (2*k+1) (by omega) (by omega)
  have he : chord k (k+1) hk (by omega) = x+y := by
    dsimp [chord, x, y, packet]
    simp only [show 2*(k+1) = 2*k+1+1 by omega]
    abel
  have hnorm : ‖x+y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
    have h := mul_self_le_mul_self (norm_nonneg (x+y)) (norm_add_le x y)
    nlinarith [sq_nonneg (‖x‖-‖y‖)]
  have hx := (abs_le.mp (ternary_packet_log_bound (2*k) (by omega))).2
  have hy := (abs_le.mp (ternary_packet_log_bound (2*k+1) (by omega))).2
  change ‖x‖^2 - _ ≤ _ at hx
  change ‖y‖^2 - _ ≤ _ at hy
  have hl : Real.log ((2*k:ℕ):ℝ) ≤ Real.log ((2*k+1:ℕ):ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ (2*k))
  rw [he]
  nlinarith

theorem aligned_chord_log_bound (L k : ℕ) (hL : 0 < L) (hk : 0 < k) :
    ‖chord (L*k) (L*(k+1)) (Nat.mul_pos hL hk) (by positivity)‖^2 ≤
      (L:ℝ)*(8*Real.log ((2*k+1:ℕ):ℝ) +
        8*‖digitHilbert 3 1 (by omega) (by omega)‖^2+996) := by
  rw [chord_norm_sq_dilation L k (k+1) hL hk (by omega)]
  exact mul_le_mul_of_nonneg_left (unit_chord_log_bound k hk) (Nat.cast_nonneg L)


end RiemannResearch.RH.Pareto.AdjacentPacket
