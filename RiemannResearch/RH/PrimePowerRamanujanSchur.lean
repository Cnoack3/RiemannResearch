import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur

/-!
# Exact global elimination of zero-mean Ramanujan packets

Source: user's CRT/Ramanujan program, combined with the established
`IntegratedRamanujanHilbert` mean identity and `FiniteHilbertSchur` projection
theorem. The original full Pareto norm is retained. Both complete square
remainders are displayed; no covariance block is discarded.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.LinearAlgebra

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

private theorem packet_inner_one (q : ℕ) :
    inner ℝ (ramanujanPacketHilbert q) hilbertOne = ArithmeticFunction.vonMangoldt q := by
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
    paretoMean_ramanujanPacket]

def mixedConductors (s : Finset ℕ) : Finset ℕ := by
  classical
  exact s.filter (fun q => ¬ IsPrimePow q)

def primeConductors (s : Finset ℕ) : Finset ℕ := by
  classical
  exact s.filter IsPrimePow

def mixedSpace (s : Finset ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (fun q : mixedConductors s => ramanujanPacketHilbert q.val))

instance mixedSpace_finiteDimensional (s : Finset ℕ) :
    FiniteDimensional ℝ (mixedSpace s) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem mixed_packet_inner_one (s : Finset ℕ) (q : mixedConductors s) :
    inner ℝ (ramanujanPacketHilbert q.val) hilbertOne = 0 := by
  classical
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert]
  exact paretoMean_ramanujanPacket_of_not_isPrimePow q.val
    (Finset.mem_filter.mp q.property).2

theorem one_mem_mixed_orthogonal (s : Finset ℕ) :
    hilbertOne ∈ (mixedSpace s)ᗮ := by
  classical
  apply ((mixedSpace s).mem_orthogonal hilbertOne).mpr
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact mixed_packet_inner_one s q
  | zero => simp
  | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
  | smul a x hx ih => simp only [real_inner_smul_left, ih, mul_zero]

def screenedPacket (s : Finset ℕ) (q : ℕ) : ThresholdHilbert :=
  ramanujanPacketHilbert q - (mixedSpace s).starProjection (ramanujanPacketHilbert q)

theorem screenedPacket_inner_one (s : Finset ℕ) (q : ℕ) :
    inner ℝ (screenedPacket s q) hilbertOne = ArithmeticFunction.vonMangoldt q := by
  have hz := ((mixedSpace s).mem_orthogonal hilbertOne).mp
    (one_mem_mixed_orthogonal s) _
    ((mixedSpace s).starProjection_apply_mem (ramanujanPacketHilbert q))
  simp only [screenedPacket, inner_sub_left, packet_inner_one, hz, sub_zero]

theorem screenedPacket_gram (s : Finset ℕ) (q r : ℕ) :
    inner ℝ (screenedPacket s q) (screenedPacket s r) =
      inner ℝ (ramanujanPacketHilbert q) (ramanujanPacketHilbert r) -
        inner ℝ ((mixedSpace s).starProjection (ramanujanPacketHilbert q))
          ((mixedSpace s).starProjection (ramanujanPacketHilbert r)) :=
  inner_residualized_eq_schur (mixedSpace s) _ _

/-- The entire mixed-conductor block is minimized exactly by c=-P_C p. -/
theorem mixed_elimination (s : Finset ℕ) (p c : ThresholdHilbert)
    (hc : c ∈ mixedSpace s) :
    ‖hilbertOne - p - c‖ ^ 2 =
      ‖hilbertOne - (p - (mixedSpace s).starProjection p)‖ ^ 2 +
        ‖(mixedSpace s).starProjection p + c‖ ^ 2 := by
  let K := mixedSpace s
  have ha : hilbertOne - (p - K.starProjection p) ∈ Kᗮ :=
    K.orthogonal.sub_mem (one_mem_mixed_orthogonal s)
      (Submodule.sub_starProjection_mem_orthogonal p)
  have hb : K.starProjection p + c ∈ K :=
    K.add_mem (K.starProjection_apply_mem p) hc
  have hab : inner ℝ (hilbertOne - (p - K.starProjection p))
      (K.starProjection p + c) = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).mp ha _ hb
  have he : hilbertOne - p - c =
      (hilbertOne - (p - K.starProjection p)) - (K.starProjection p + c) := by abel
  rw [he, norm_sub_sq_real, hab]
  ring

def primeCombination (s : Finset ℕ) (a : primeConductors s → ℝ) : ThresholdHilbert :=
  finiteSchurCombination (fun q : primeConductors s => ramanujanPacketHilbert q.val) a

theorem screened_combination (s : Finset ℕ) (a : primeConductors s → ℝ) :
    finiteSchurCombination (fun q : primeConductors s => screenedPacket s q.val) a =
      primeCombination s a - (mixedSpace s).starProjection (primeCombination s a) := by
  simp only [finiteSchurCombination, primeCombination, screenedPacket,
    smul_sub, Finset.sum_sub_distrib, map_sum, map_smul]

/-- One prime-power system, after screening against all mixed conductors,
attains the exact original minimum, with BOTH complete square remainders. -/
theorem exists_exact_global_elimination (s : Finset ℕ) :
    ∃ b : primeConductors s → ℝ,
      (∀ i : primeConductors s, inner ℝ (screenedPacket s i.val)
        (finiteSchurCombination (fun q : primeConductors s => screenedPacket s q.val) b) =
          ArithmeticFunction.vonMangoldt i.val) ∧
      ∀ (a : primeConductors s → ℝ) (c : ThresholdHilbert), c ∈ mixedSpace s →
        ‖hilbertOne - primeCombination s a - c‖ ^ 2 =
          1 - (∑ i, b i * ArithmeticFunction.vonMangoldt i.val) +
          ‖finiteSchurCombination (fun q : primeConductors s => screenedPacket s q.val) a -
            finiteSchurCombination (fun q : primeConductors s => screenedPacket s q.val) b‖ ^ 2 +
          ‖(mixedSpace s).starProjection (primeCombination s a) + c‖ ^ 2 := by
  obtain ⟨b, hb, hmin⟩ := finiteSchur_exists_exact_minimum hilbertOne
    (fun q : primeConductors s => screenedPacket s q.val)
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [screenedPacket_inner_one] using hb i
  · intro a c hc
    rw [mixed_elimination s _ _ hc, ← screened_combination s a]
    have he := hmin a
    simp only [finiteSchurResidual, hilbertOne_norm_sq, screenedPacket_inner_one] at he
    rw [he]

end RiemannResearch.RH.Pareto.PrimePowerSchur
