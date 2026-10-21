/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QPrimePowerHeadClosure
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QSquarefreeCapacity
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Removing constants from prime-anchored logarithmic approximants

Source: the user's compensated Möbius/factorial research agenda, 21 October
2026, for the anchored dictionary. The three-site functional below extracts
the adjoined constant and annihilates every anchored legal atom. The complete
Q norm and actual target are retained. Target membership and uniform energy
budgets remain explicit hypotheses, and no arithmetic provider is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference ArithmeticCumulative

/-- All squarefree legal conductors divisible by the chosen base. -/
def anchoredSpan (p : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (qResidue '' {d : ℕ | 2 ≤ d ∧ Squarefree d ∧ p ∣ d})

def anchoredWithConstants (p : ℕ) : Submodule ℝ QHilbert :=
  anchoredSpan p ⊔ Submodule.span ℝ {qOne}

/-- The exact three-site constant charge. -/
def anchoredCharge (p : ℕ) : QHilbert →ₗ[ℝ] ℝ where
  toFun f := qSequence f 1 - qDifference f (p + 1)
  map_add' f g := by
    rw [qDifference_add]
    have h := congrFun (qSequenceLinear.map_add f g) 1
    change qSequence (f + g) 1 = qSequence f 1 + qSequence g 1 at h
    rw [h]
    ring
  map_smul' c f := by
    rw [qDifference_smul]
    have h := congrFun (qSequenceLinear.map_smul c f) 1
    change qSequence (c • f) 1 = c * qSequence f 1 at h
    rw [h]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

theorem anchoredCharge_continuous (p : ℕ) : Continuous (anchoredCharge p) :=
  (continuous_qSequence 1).sub (continuous_qDifference (p + 1))

theorem anchoredCharge_qOne (p : ℕ) (hp : 1 < p) :
    anchoredCharge p qOne = 1 := by
  change qSequence qOne 1 - qDifference qOne (p + 1) = 1
  rw [qDifference_qOne (p + 1) (by omega), qSequence_qOne]
  simp [qOneSequence]

theorem anchoredCharge_qResidue (p d : ℕ) (hp : 1 < p)
    (hd : 2 ≤ d) (hpd : p ∣ d) : anchoredCharge p (qResidue d) = 0 := by
  have hnd : ¬ d ∣ p + 1 := by
    intro h
    have hmod := Nat.mod_eq_zero_of_dvd (dvd_trans hpd h)
    simp [Nat.mod_eq_of_lt hp] at hmod
  change qSequence (qResidue d) 1 -
    (qSequence (qResidue d) (p + 1) - qSequence (qResidue d) (p + 1 - 1)) = 0
  simp only [qSequence_qResidue]
  rw [residueFraction_difference d (p + 1) hd (by omega), if_neg hnd]
  simp [residueFraction, Nat.mod_eq_of_lt (by omega : 1 < d)]

theorem anchoredCharge_zero_on_span (p : ℕ) (hp : 1 < p)
    {f : QHilbert} (hf : f ∈ anchoredSpan p) : anchoredCharge p f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨d, hd, rfl⟩ := hf
      exact anchoredCharge_qResidue p d hp hd.1 hd.2.2
  | zero => exact map_zero _
  | add f g hf hg ihf ihg => rw [map_add, ihf, ihg, add_zero]
  | smul c f hf ih => rw [map_smul, ih, smul_zero]

theorem anchoredSpan_le_squarefreeSpan (p : ℕ) :
    anchoredSpan p ≤ qSquarefreeCRTSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, rfl⟩
  exact Submodule.subset_span ⟨⟨d, hd.1, hd.2.1⟩, rfl⟩

theorem anchoredCharge_qTarget (p : ℕ) (hp : 1 < p) :
    anchoredCharge p (qTarget p hp) = 0 := by
  have hlogp : (Nat.log p p : ℝ) = 1 := by
    have h := paretoTarget_sequence_rec p hp p
    simp only [paretoTarget_sequence] at h
    simpa [Nat.div_self (by omega : 0 < p)] using h
  have hdiv : (p + 1) / p = 1 := by
    rw [Nat.add_comm p 1, Nat.add_div_right 1 (by omega : 0 < p)]
    simp [Nat.div_eq_of_lt hp]
  have hlogp1 : (Nat.log p (p + 1) : ℝ) = 1 := by
    have h := paretoTarget_sequence_rec p hp (p + 1)
    simp only [paretoTarget_sequence, hdiv] at h
    simpa using h
  change qSequence (qTarget p hp) 1 -
    (qSequence (qTarget p hp) (p + 1) - qSequence (qTarget p hp) (p + 1 - 1)) = 0
  simp only [qTarget_sequence, Nat.add_sub_cancel, hlogp, hlogp1]
  simp

/-- The three physical sites recover the actual adjoined constant exactly. -/
theorem anchoredCharge_add_constant (p : ℕ) (hp : 1 < p)
    {f : QHilbert} (hf : f ∈ anchoredSpan p) (c : ℝ) :
    anchoredCharge p (f + c • qOne) = c := by
  simp [map_add, map_smul, anchoredCharge_zero_on_span p hp hf,
    anchoredCharge_qOne p hp, smul_eq_mul]

/-- Once the head reaches p+1, exact target interpolation forces the
adjoined constant to be literally zero. No limiting argument is needed. -/
theorem anchored_constant_zero_of_exact_head (p : ℕ) (hp : 1 < p)
    {f : QHilbert} (hf : f ∈ anchoredSpan p) (c : ℝ)
    (hhead : ∀ n : ℕ, 0 < n → n ≤ p + 1 →
      qSequence (f + c • qOne) n = (Nat.log p n : ℝ)) : c = 0 := by
  have hcharge : anchoredCharge p (f + c • qOne) =
      anchoredCharge p (qTarget p hp) := by
    change qSequence (f + c • qOne) 1 -
      (qSequence (f + c • qOne) (p + 1) -
        qSequence (f + c • qOne) (p + 1 - 1)) =
      qSequence (qTarget p hp) 1 -
        (qSequence (qTarget p hp) (p + 1) -
          qSequence (qTarget p hp) (p + 1 - 1))
    simp only [Nat.add_sub_cancel, qTarget_sequence]
    rw [hhead 1 (by omega) (by omega), hhead (p + 1) (by omega) le_rfl,
      hhead p (by omega) (by omega)]
  rw [anchoredCharge_add_constant p hp hf c, anchoredCharge_qTarget p hp] at hcharge
  exact hcharge

theorem anchoredWithConstants_exact_head_mem_span (p : ℕ) (hp : 1 < p)
    {g : QHilbert} (hg : g ∈ anchoredWithConstants p)
    (hhead : ∀ n : ℕ, 0 < n → n ≤ p + 1 →
      qSequence g n = (Nat.log p n : ℝ)) : g ∈ anchoredSpan p := by
  obtain ⟨f, hf, z, hz, rfl⟩ := Submodule.mem_sup.mp hg
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc := anchored_constant_zero_of_exact_head p hp hf c hhead
  simpa [hc] using hf

/-- Constants are removed by an actual continuous three-site projection. -/
theorem mem_anchoredClosure_of_mem_withConstants_of_charge_zero
    (p : ℕ) (hp : 1 < p) {f : QHilbert}
    (hf : f ∈ (anchoredWithConstants p).topologicalClosure)
    (hcharge : anchoredCharge p f = 0) :
    f ∈ (anchoredSpan p).topologicalClosure := by
  let P : QHilbert → QHilbert := fun x => x - anchoredCharge p x • qOne
  have hP : Continuous P :=
    continuous_id.sub ((anchoredCharge_continuous p).smul continuous_const)
  have hbase : ∀ x ∈ anchoredWithConstants p, P x ∈ anchoredSpan p := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have he : P (y + c • qOne) = y := by
      simp [P, map_add, map_smul, anchoredCharge_zero_on_span p hp hy,
        anchoredCharge_qOne p hp, smul_eq_mul]
    rw [he]
    exact hy
  have hclosed : IsClosed {x : QHilbert | P x ∈ (anchoredSpan p).topologicalClosure} :=
    (anchoredSpan p).isClosed_topologicalClosure.preimage hP
  have hmap : (anchoredWithConstants p : Set QHilbert) ⊆
      {x : QHilbert | P x ∈ (anchoredSpan p).topologicalClosure} := by
    intro x hx
    change P x ∈ (anchoredSpan p).topologicalClosure
    exact (anchoredSpan p).le_topologicalClosure (hbase x hx)
  have hout : P f ∈ (anchoredSpan p).topologicalClosure := by
    have hfset : f ∈ closure (anchoredWithConstants p : Set QHilbert) := hf
    exact (closure_minimal hmap hclosed) hfset
  have hPf : P f = f := by simp only [P, hcharge, zero_smul, sub_zero]
  rw [hPf] at hout
  exact hout

/-- A single anchored target, even with constants allowed, suffices for RH.
The closure membership is the unresolved substantive input. -/
theorem riemannHypothesis_of_qTarget_mem_anchoredWithConstants
    (p : ℕ) (hp : 1 < p)
    (hf : qTarget p hp ∈ (anchoredWithConstants p).topologicalClosure) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_qTarget_mem p hp
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact (Submodule.topologicalClosure_mono (anchoredSpan_le_squarefreeSpan p))
    (mem_anchoredClosure_of_mem_withConstants_of_charge_zero p hp hf
      (anchoredCharge_qTarget p hp))

/-- The full-energy budget remains explicit. Constants and all composite
squarefree anchored conductors are allowed in the finite dictionary. -/
theorem riemannHypothesis_of_bounded_anchored_exact_heads
    (p : ℕ) (hp : 1 < p)
    (h : ∃ B : ℝ, ∀ M : ℕ, ∃ g : QHilbert, g ∈ anchoredWithConstants p ∧
      (∀ n, 0 < n → n ≤ M → qSequence g n = (Nat.log p n : ℝ)) ∧
      ‖g‖ ^ 2 ≤ B) : RiemannHypothesis := by
  apply riemannHypothesis_of_qTarget_mem_anchoredWithConstants p hp
  apply (QExactHeadAverages.mem_closure_iff_bounded_target_heads
    (anchoredWithConstants p) (qTarget p hp)).mpr
  simpa only [qTarget_sequence] using h

end RiemannResearch.RH.PrimePowerTarget
