import RiemannResearch.RH.MixedConductorGramSites
import RiemannResearch.RH.ParetoRamanujanGramCRT
import RiemannResearch.Analysis.ParetoProgressionCertificates
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Tactic.Positivity

/-!
# Opposite signs for two consecutive first-site Gram tests

Stages three and four use the conductors 2 through 4 and 2 through 5, respectively.
Every packet in either dictionary has period dividing 60. The progression
enclosures below include the infinite Pareto tail. The integer tables give
enclosures on a common decimal grid. Each table is checked from the preceding
level before it is used in the Laplace expansion of a determinant.

The quantity enclosed is the first-site score minus one, multiplied by the
positive determinant of the raw Pareto Gram matrix. Its strictly positive
value at stage three and strictly negative value at stage four preclude a
successor induction based on the sign alone.
-/

open scoped BigOperators Matrix
open RiemannResearch RiemannResearch.RH RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary
open RiemannResearch.Analysis.ParetoProgressionCertificates
open RiemannResearch.RH.RamanujanCanonicalOptimizer
open RatInterval
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace RiemannResearch.RH.Pareto.GramStageArithmetic

private def packetValue (q k : ℕ) : ℚ :=
  ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℚ) * (k % d : ℕ)

private theorem packetValue_cast (q k : ℕ) :
    ((packetValue q k : ℚ) : ℝ) = ramanujanPacket q k := by
  simp [packetValue, ramanujanPacket, residue]

private def massGrid : Fin 60 → ℕ :=
  ![50044079, 16709727, 8375417, 5041148, 3373583, 2420341, 1824274, 1426653,
    1148109, 945352, 793127, 675892, 583657, 509760, 449621, 400008,
    358584, 323630, 293853, 268271, 246123, 226814, 209872, 194922,
    181657, 169830, 159236, 149707, 141102, 133303, 126210, 119737,
    113814, 108377, 103374, 98758, 94490, 90533, 86858, 83437,
    80247, 77266, 74476, 71861, 69405, 67095, 64919, 62868,
    60930, 59098, 57363, 55718, 54157, 52675, 51264, 49922,
    48642, 47422, 46257, 45144]

private def massInterval (r : Fin 60) : RatInterval :=
  ⟨((massGrid r : ℚ)-1)/100000000, ((massGrid r : ℚ)+2)/100000000⟩

private theorem massInterval_encloses_progression : ∀ r : Fin 60,
    (massInterval r).lo ≤ (paretoProgressionInterval ((r.val : ℚ)+1) 60 4).lo ∧
    (paretoProgressionInterval ((r.val : ℚ)+1) 60 4).hi ≤ (massInterval r).hi := by
  decide +kernel

private def weightInterval (L r : ℕ) : RatInterval :=
  if L = 60 then massInterval ⟨r % 60, Nat.mod_lt _ (by decide)⟩ else
    paretoProgressionInterval (r+1) L 4

private theorem weightInterval_contains {L : ℕ} (hL : 0 < L) (r : Fin L) :
    (weightInterval L r).Contains (progressionWeight L (r.val+1)) := by
  have h := paretoProgressionInterval_contains ((r : ℚ)+1) (L : ℚ) 4
    (by positivity) (by exact_mod_cast hL) (by decide)
  have h' : (paretoProgressionInterval ((r.val : ℚ)+1) L 4).Contains
      (progressionWeight L (r.val+1)) := by
    simpa only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, ← Nat.cast_succ,
      paretoProgression_eq_progressionWeight] using h
  by_cases h60 : L = 60
  · subst L
    simpa [weightInterval, Nat.mod_eq_of_lt r.isLt] using
      contains_weaken h' (massInterval_encloses_progression r).1 (massInterval_encloses_progression r).2
  · simpa [weightInterval, h60] using h'

private def gramInterval (L q s : ℕ) := RatInterval.sum Finset.univ fun r : Fin L =>
  RatInterval.mul (weightInterval L r.val) (point (packetValue q (r.val+1) * packetValue s (r.val+1)))

private theorem gramInterval_contains {L q s : ℕ} (hL : 0 < L) (hq : q ∣ L) (hs : s ∣ L) :
    (gramInterval L q s).Contains (inner ℝ (ramanujanPacketHilbert q) (ramanujanPacketHilbert s)) := by
  rw [ramanujanPacketHilbert_inner_eq_crt q s L hL hq hs]
  apply contains_sum
  intro r _
  apply contains_mul (weightInterval_contains hL r)
  simpa only [Rat.cast_mul, packetValue_cast] using
    contains_point (packetValue q (r.val+1) * packetValue s (r.val+1))

private def meanInterval (L q : ℕ) := RatInterval.sum Finset.univ fun r : Fin L =>
  RatInterval.mul (weightInterval L r.val) (point (packetValue q (r.val+1)))

private theorem meanInterval_contains {L q : ℕ} (hL : 0 < L) (hq : q ∣ L) :
    (meanInterval L q).Contains (ArithmeticFunction.vonMangoldt q) := by
  rw [← paretoMean_ramanujanPacket,
    periodic_paretoMean L hL (ramanujanPacket q) (ramanujanPacket_abs_le q)
      (ramanujanPacket_period_of_dvd q L hq)]
  apply contains_sum
  intro r _
  apply contains_mul (weightInterval_contains hL r)
  simpa only [packetValue_cast] using contains_point (packetValue q (r.val+1))

private def detInterval : (n : ℕ) → Matrix (Fin n) (Fin n) RatInterval → RatInterval
  | 0, _ => point 1
  | n+1, A => RatInterval.sum Finset.univ fun j : Fin (n+1) =>
    RatInterval.mul (RatInterval.mul (point ((-1 : ℚ)^j.val)) (A 0 j))
      (detInterval n (A.submatrix Fin.succ j.succAbove))

private theorem detInterval_contains {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (I : Matrix (Fin n) (Fin n) RatInterval) (h : ∀ i j, (I i j).Contains (A i j)) :
    (detInterval n I).Contains A.det := by
  induction n with
  | zero => rw [Matrix.det_fin_zero]; simpa [detInterval] using contains_point 1
  | succ n ih =>
    rw [Matrix.det_succ_row_zero]
    apply contains_sum
    intro j _
    apply contains_mul
    · apply contains_mul _ (h 0 j)
      simpa only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using
        contains_point ((-1 : ℚ)^j.val)
    · exact ih _ _ (fun a b => h a.succ (j.succAbove b))

private def sqrtTwoInterval : RatInterval := ⟨14142135/10000000, 14142136/10000000⟩

private theorem sqrtTwoInterval_contains : sqrtTwoInterval.Contains (Real.sqrt 2) := by
  have h := contains_sqrt (contains_point 2) (14142135/10000000) (14142136/10000000)
    (by norm_num) (by norm_num [point]) (by norm_num [point])
  simpa [sqrtTwoInterval] using h

private def meanTable (k : Fin 4) : RatInterval :=
  let v : Fin 4 → ℕ × ℕ :=
    ![(69314670, 69314760), (109861136, 109861316), (69314628, 69314808), (160943607, 160943967)]
  ⟨(v k).1 / (100000000:ℚ), (v k).2 / (100000000:ℚ)⟩

private def gramTable (k j : Fin 4) : RatInterval :=
  let v : Fin 4 → Fin 4 → ℕ × ℕ :=
    ![![(69314670, 69314760), (63785304, 63785394), (25432212, 25432302), (91789994, 91790174)],
      ![(63785304, 63785394), (159262324, 159262624), (82556202, 82556382), (167660132, 167660492)],
      ![(25432212, 25432302), (82556202, 82556382), (138629256, 138629616), (147027096, 147027456)],
      ![(91789994, 91790174), (167660132, 167660492), (147027096, 147027456), (363917425, 363918505)]]
  ⟨(v k j).1 / (100000000:ℚ), (v k j).2 / (100000000:ℚ)⟩

private theorem meanTable_encloses : ∀ k : Fin 4,
  (meanTable k).lo ≤ (meanInterval 60 (k.val+2)).lo ∧ (meanInterval 60 (k.val+2)).hi ≤ (meanTable k).hi := by
  decide +kernel

private theorem gramTable_encloses : ∀ k j : Fin 4,
  (gramTable k j).lo ≤ (gramInterval 60 (k.val+2) (j.val+2)).lo ∧ (gramInterval 60 (k.val+2) (j.val+2)).hi ≤ (gramTable k j).hi := by
  decide +kernel

private def scoreInterval (n : ℕ) : RatInterval :=
  let G : Matrix (Fin n) (Fin n) RatInterval := fun i j => gramTable (Fin.ofNat 4 i.val) (Fin.ofNat 4 j.val)
  let b : Fin n → RatInterval := fun i => meanTable (Fin.ofNat 4 i.val)
  let A := fun i j => RatInterval.add (G i j)
    (RatInterval.mul (b i) (point (packetValue (j.val+2) 1)))
  let C := fun i j => RatInterval.sub (G i j) (RatInterval.mul (b i) (b j))
  RatInterval.sub (RatInterval.add (detInterval n A)
    (RatInterval.mul (RatInterval.sub (point 2) sqrtTwoInterval) (detInterval n C)))
    (RatInterval.mul (point 2) (detInterval n G))

private theorem scoreInterval_contains (n : ℕ) (hn4 : n ≤ 4) (hn : ∀ i : Fin n, i.val+2 ∣ 60) :
    (scoreInterval n).Contains ((siteGram n 1).det + (2-Real.sqrt 2)*(meanPencil n 1).det -
      2*(finitePacketGram n).det) := by
  have htwo : (point 2).Contains (2 : ℝ) := by simpa using contains_point 2
  have hmod (i : Fin n) : (Fin.ofNat 4 i.val).val = i.val := Nat.mod_eq_of_lt (i.isLt.trans_le hn4)
  have hg (i j : Fin n) : (gramTable (Fin.ofNat 4 i.val) (Fin.ofNat 4 j.val)).Contains (finitePacketGram n i j) := by
    have hh := gramTable_encloses (Fin.ofNat 4 i.val) (Fin.ofNat 4 j.val)
    simp only [hmod] at hh
    exact contains_weaken (gramInterval_contains (by decide : 0 < 60) (hn i) (hn j)) hh.1 hh.2
  have hb (i : Fin n) : (meanTable (Fin.ofNat 4 i.val)).Contains (meanVector n i) := by
    have hh := meanTable_encloses (Fin.ofNat 4 i.val)
    simp only [hmod] at hh
    exact contains_weaken (meanInterval_contains (by decide : 0 < 60) (hn i)) hh.1 hh.2
  apply contains_sub
  · apply contains_add
    · apply detInterval_contains
      intro i j
      apply contains_add (hg i j)
      apply contains_mul (hb i)
      simpa [siteVector, packetValue_cast] using contains_point (packetValue (j.val+2) 1)
    · apply contains_mul (contains_sub htwo sqrtTwoInterval_contains)
      apply detInterval_contains
      intro i j
      rw [meanPencil, one_smul]
      exact contains_sub (hg i j) (contains_mul (hb i) (hb j))
  · exact contains_mul htwo (detInterval_contains _ _ fun i j => hg i j)

private theorem stageFour_upper : (scoreInterval 4).hi < 0 := by decide +kernel

private theorem stageThree_lower : 0 < (scoreInterval 3).lo := by decide +kernel

/-- The four-packet determinant falls strictly below the zero-error budget. -/
theorem first_site_stage_four_strict_failure :
    (siteGram 4 1).det + (2 - Real.sqrt 2) * (meanPencil 4 1).det <
      2 * (finitePacketGram 4).det := by
  have h := (scoreInterval_contains 4 (by decide) (by decide)).2
  have hu : (((scoreInterval 4).hi : ℚ) : ℝ) < 0 := by exact_mod_cast stageFour_upper
  linarith

/-- The three-packet determinant exceeds the zero-error budget. -/
theorem first_site_stage_three_strict_slack :
    2 * (finitePacketGram 3).det <
      (siteGram 3 1).det + (2 - Real.sqrt 2) * (meanPencil 3 1).det := by
  have h := (scoreInterval_contains 3 (by decide) (by decide)).1
  have hl : 0 < (((scoreInterval 3).lo : ℚ) : ℝ) := by exact_mod_cast stageThree_lower
  linarith

end RiemannResearch.RH.Pareto.GramStageArithmetic
