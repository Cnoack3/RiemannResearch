import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.IntegratedRamanujanMarkedArithmetic
import RiemannResearch.RH.IntegerDPPResidueProbability
import RiemannResearch.Analysis.FiniteGramBasisInvariance

/-!
# Exact finite residue/packet basis bridge

Source: user-provided Ramanujan change-of-basis and q_N calculation,
22 September 2026. The argument supplies the statements and proof strategy.
The packets are the existing genuine Hilbert packets, and `qN` below is
the existing DPP occupation probability.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

def rawResidueAtom (i : ℕ) : ThresholdHilbert :=
  ((i + 2 : ℕ) : ℝ) • residueAtom i

theorem rawResidueAtom_sequence (i k : ℕ) :
    hilbertSequence (rawResidueAtom i) k = residue (i + 2) k := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [rawResidueAtom, map_smul, smul_eq_mul,
    anchoredEvaluationCLM_apply, residueAtom, normalizedResidueHilbert_sequence]
  change ((i + 2 : ℕ) : ℝ) *
    (((k % (i + 2) : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ)) =
      ((k % (i + 2) : ℕ) : ℝ)
  have hi : ((i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hi]

theorem ramanujanPacketHilbert_eq_divisor_sum (q : ℕ) (_hq : 1 < q) :
    ramanujanPacketHilbert q =
      ∑ d ∈ q.divisors.filter (fun d => 1 < d),
        (ArithmeticFunction.moebius (q / d) : ℝ) • rawResidueAtom (d - 2) := by
  apply hilbertSequence_injective
  funext k
  rw [hilbertSequence_ramanujanPacketHilbert, ← anchoredEvaluationCLM_apply]
  simp only [map_sum, map_smul, smul_eq_mul,
    anchoredEvaluationCLM_apply, rawResidueAtom_sequence]
  unfold ramanujanPacket
  symm
  calc
    _ = ∑ d ∈ q.divisors.filter (fun d => 1 < d),
        (ArithmeticFunction.moebius (q / d) : ℝ) * residue d k := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [show d - 2 + 2 = d by have := (Finset.mem_filter.mp hd).2; omega]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      have hdpos := Nat.pos_of_mem_divisors hd
      have hd1 : d = 1 := by
        have hh : ¬ 1 < d := by
          intro h
          exact hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
        omega
      simp [hd1, residue, Nat.mod_one]

theorem rawResidueAtom_eq_packet_divisor_sum (q : ℕ) (hq : 1 < q) :
    rawResidueAtom (q - 2) =
      ∑ d ∈ q.divisors.filter (fun d => 1 < d), ramanujanPacketHilbert d := by
  apply hilbertSequence_injective
  funext k
  rw [rawResidueAtom_sequence, show q - 2 + 2 = q by omega,
    ← anchoredEvaluationCLM_apply]
  simp only [map_sum, anchoredEvaluationCLM_apply,
    hilbertSequence_ramanujanPacketHilbert]
  rw [← ramanujanPacket_divisor_sum q k (by omega)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hdpos := Nat.pos_of_mem_divisors hd
  have hd1 : d = 1 := by
    have hh : ¬ 1 < d := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
    omega
  simp [hd1, ramanujanPacket, residue, Nat.mod_one]

theorem finitePacket_independent (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  by_contra hz
  push Not at hz
  obtain ⟨i, hi⟩ := hz
  let t : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let m : Fin n := t.max' ht
  have hmt : m ∈ t := Finset.max'_mem t ht
  have ham : a m ≠ 0 := (Finset.mem_filter.mp hmt).2
  have hh := congrArg (mobiusDifferenceCLM (m.val + 2)) ha
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hh
  have hs : (∑ j : Fin n, a j * mobiusDifferenceCLM (m.val + 2)
      (ramanujanPacketHilbert (j.val + 2))) =
      a m * (-((m.val + 2 : ℕ) : ℝ)) := by
    rw [Finset.sum_eq_single m]
    · rw [mobiusDifferenceCLM_ramanujanPacketHilbert _ _ (by omega) (by omega)]
      simp
    · intro j hj hjm
      by_cases haj : a j = 0
      · simp [haj]
      have hjt : j ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haj⟩
      have hjmle : j ≤ m := Finset.le_max' t j hjt
      have hnd : ¬ m.val + 2 ∣ j.val + 2 := by
        intro hd
        have hle := Nat.le_of_dvd (by omega : 0 < j.val + 2) hd
        have he : j = m := Fin.ext (by exact le_antisymm hjmle (by omega))
        exact hjm he
      rw [mobiusDifferenceCLM_ramanujanPacketHilbert _ _ (by omega) (by omega)]
      simp [hnd]
    · intro h
      exact (h (Finset.mem_univ m)).elim
  rw [hs] at hh
  exact (mul_ne_zero ham (neg_ne_zero.mpr (by positivity))) hh

theorem finitePacket_span_eq (n : ℕ) :
    Submodule.span ℝ (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) =
      Submodule.span ℝ (Set.range (fun i : Fin n => residueAtom i.val)) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ramanujanPacketHilbert (i.val + 2) ∈
      Submodule.span ℝ (Set.range (fun j : Fin n => residueAtom j.val))
    rw [ramanujanPacketHilbert_eq_divisor_sum (i.val + 2) (by omega)]
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.smul_mem
    unfold rawResidueAtom
    apply Submodule.smul_mem
    have hd2 := (Finset.mem_filter.mp hd).2
    have hdle : d ≤ i.val + 2 :=
      Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
    exact Submodule.subset_span ⟨⟨d - 2, by omega⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change residueAtom i.val ∈ Submodule.span ℝ
      (Set.range (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)))
    let S := Submodule.span ℝ
      (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)))
    have hraw : rawResidueAtom i.val ∈ S := by
      have he := rawResidueAtom_eq_packet_divisor_sum (i.val + 2) (by omega)
      rw [Nat.add_sub_cancel] at he
      rw [he]
      apply S.sum_mem
      intro d hd
      have hd2 := (Finset.mem_filter.mp hd).2
      have hdle : d ≤ i.val + 2 :=
        Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
      change ramanujanPacketHilbert d ∈ Submodule.span ℝ
        (Set.range (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)))
      exact Submodule.subset_span ⟨⟨d - 2, by omega⟩,
        by dsimp only; congr 1; omega⟩
    have hh := S.smul_mem (((i.val + 2 : ℕ) : ℝ)⁻¹) hraw
    simpa only [rawResidueAtom, smul_smul,
      inv_mul_cancel₀ (by positivity : ((i.val + 2 : ℕ) : ℝ) ≠ 0), one_smul] using hh

def packetHeadSource (n : ℕ) (i : Fin n) : ℝ :=
  -(ArithmeticFunction.moebius (i.val + 2) : ℝ)

theorem packetHeadSource_eq_evaluation (n : ℕ) (i : Fin n) :
    packetHeadSource n i =
      anchoredEvaluationCLM 1 (ramanujanPacketHilbert (i.val + 2)) := by
  rw [anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_at_one_moebius _ (by omega)]
  rfl

theorem fullCapacity_eq_packetCapacity (n : ℕ) :
    fullCapacity n = capacity (finitePacket_independent n) (packetHeadSource n) := by
  have h := capacity_evaluation_eq_of_span_eq
    (finiteAtom_independent n) (finitePacket_independent n)
    (anchoredEvaluationCLM 1).toLinearMap (finitePacket_span_eq n).symm
  change capacity (finiteAtom_independent n) (reciprocalSource n) = _
  convert h using 1
  · congr 1
    funext i
    exact (residueAtom_evaluation i.val).symm
  · congr 1
    funext i
    exact packetHeadSource_eq_evaluation n i

theorem qN_eq_packetCapacity (n : ℕ) :
    IntegerDPP.qN n = progressionWeight (IntegerDPP.residueModulus n) 1 *
      capacity (finitePacket_independent n) (packetHeadSource n) := by
  rw [IntegerDPP.qN_eq_fullCapacity, fullCapacity_eq_packetCapacity]

/-- The genuine Hilbert Gram matrix of the existing integrated packets. -/
def finitePacketGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gramMatrix (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))

theorem finitePacketGram_apply (n : ℕ) (i j : Fin n) :
    finitePacketGram n i j =
      paretoInner (ramanujanPacket (i.val + 2)) (ramanujanPacket (j.val + 2)) := by
  change inner ℝ (ramanujanPacketHilbert (i.val + 2))
    (ramanujanPacketHilbert (j.val + 2)) = _
  rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert,
    hilbertSequence_ramanujanPacketHilbert]

def finiteMoebiusSource (n : ℕ) (i : Fin n) : ℝ :=
  (ArithmeticFunction.moebius (i.val + 2) : ℝ)

theorem packetCapacity_eq_inverseGram (n : ℕ) :
    capacity (finitePacket_independent n) (packetHeadSource n) =
      dotProduct (packetHeadSource n)
        ((finitePacketGram n)⁻¹.mulVec (packetHeadSource n)) := by
  rw [finitePacketGram, gramMatrix_inverseSource (finitePacket_independent n)]
  unfold capacity dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The original DPP probability, expressed in the actual packet basis. -/
theorem qN_eq_packetInverseGram (n : ℕ) :
    IntegerDPP.qN n = progressionWeight (IntegerDPP.residueModulus n) 1 *
      dotProduct (finiteMoebiusSource n)
        ((finitePacketGram n)⁻¹.mulVec (finiteMoebiusSource n)) := by
  rw [qN_eq_packetCapacity, packetCapacity_eq_inverseGram]
  congr 1
  simp only [packetHeadSource, finiteMoebiusSource, Matrix.mulVec, dotProduct,
    mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]

/-- The original reciprocal-source Gram quadratic equals the marked
Ramanujan quadratic by the proved finite change of basis. -/
theorem residue_inverseGram_eq_packetInverseGram (n : ℕ) :
    dotProduct (reciprocalSource n) ((IntegerDPP.fullGram n)⁻¹.mulVec (reciprocalSource n)) =
      dotProduct (finiteMoebiusSource n)
        ((finitePacketGram n)⁻¹.mulVec (finiteMoebiusSource n)) := by
  have hw : progressionWeight (IntegerDPP.residueModulus n) 1 ≠ 0 :=
    ne_of_gt (progressionWeight_pos _ _ (IntegerDPP.residueModulus_pos n) (by omega))
  apply mul_left_cancel₀ hw
  exact (IntegerDPP.qN_eq_inverseGram n).symm.trans (qN_eq_packetInverseGram n)

theorem qN_div_progressionWeight_eq_packetInverseGram (n : ℕ) :
    IntegerDPP.qN n / progressionWeight (IntegerDPP.residueModulus n) 1 =
      dotProduct (finiteMoebiusSource n)
        ((finitePacketGram n)⁻¹.mulVec (finiteMoebiusSource n)) := by
  have hw : progressionWeight (IntegerDPP.residueModulus n) 1 ≠ 0 :=
    ne_of_gt (progressionWeight_pos _ _ (IntegerDPP.residueModulus_pos n) (by omega))
  apply (div_eq_iff hw).2
  rw [qN_eq_packetInverseGram]
  ring

end RiemannResearch.RH.Pareto
