import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.RamanujanPacketDilation
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Mixed-conductor screening under integer dilation

Section 2 of the user-provided Mixed Conductor CRT Research Handoff supplies the setup.
The complete Pareto mixed subspace is dilation invariant. The induced action
on a screened prime-power packet shifts the exponent by the corresponding
valuation. The residue pairings of a mixed annihilator are coprime-additive.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

private theorem not_isPrimePow_mul_of_coprime {a b : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hcop : a.Coprime b) : ¬ IsPrimePow (a * b) := by
  intro hab
  obtain ⟨p, k, hp, _, he⟩ := (isPrimePow_nat_iff _).mp hab
  have ha' : a ∣ p ^ k := by rw [he]; exact dvd_mul_right a b
  have hb' : b ∣ p ^ k := by rw [he]; exact dvd_mul_left b a
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp ha'
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hb'
  have hi0 : i ≠ 0 := by intro h; simp [h] at hi; omega
  have hj0 : j ≠ 0 := by intro h; simp [h] at hj; omega
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop
    (hi.symm ▸ dvd_pow_self p hi0) (hj.symm ▸ dvd_pow_self p hj0))

theorem hilbertDilation_mem_mixedClosure (m : ℕ) (hm : 0 < m)
    {x : ThresholdHilbert} (hx : x ∈ mixedClosure) :
    hilbertDilation m hm x ∈ mixedClosure := by
  let D := hilbertDilationContinuous m hm
  have hle : mixedClosure ≤ mixedClosure.comap D.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro N
      apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      obtain ⟨hq, hmix⟩ := Finset.mem_filter.mp q.property
      have hq' : 1 < q.val := by have := (Finset.mem_Icc.mp hq).1; omega
      change hilbertDilation m hm (ramanujanPacketHilbert q.val) ∈ mixedClosure
      rw [hilbertDilation_ramanujanPacket_divisors m q.val hm hq']
      apply mixedClosure.sum_mem
      intro d hd
      have hd' := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
      apply mixed_packet_mem_closure
      · exact hq'.trans_le (Nat.le_mul_of_pos_right _ hd')
      · intro hp
        exact hmix (hp.dvd (dvd_mul_right q.val d) (by omega))
    · exact (show IsClosed (mixedClosure : Set ThresholdHilbert) from
        isClosed_closure).preimage D.continuous
  exact hle hx

private theorem fullScreening_eq_zero_of_mem {x : ThresholdHilbert} (hx : x ∈ mixedClosure) :
    fullScreening x = 0 := by
  change x - mixedClosure.starProjection x = 0
  rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

/-- Full screening implements the quotient action after an arbitrary
positive-integer dilation. -/
theorem fullScreening_dilation_fullScreening (m : ℕ) (hm : 0 < m) (x : ThresholdHilbert) :
    fullScreening (hilbertDilation m hm (fullScreening x)) =
      fullScreening (hilbertDilation m hm x) := by
  change fullScreening ((hilbertDilationContinuous m hm) (x - mixedClosure.starProjection x)) = _
  rw [map_sub, map_sub, hilbertDilationContinuous_apply, hilbertDilationContinuous_apply,
    fullScreening_eq_zero_of_mem
      (hilbertDilation_mem_mixedClosure m hm (mixedClosure.starProjection_apply_mem x)), sub_zero]

theorem hilbertDilation_packet_sub_eq_coprime_divisors (m q : ℕ)
    (hm : 0 < m) (hq : 1 < q) (hc : q.Coprime m) :
    hilbertDilation m hm (ramanujanPacketHilbert q) - ramanujanPacketHilbert q =
      ∑ d ∈ m.divisors.erase 1, ramanujanPacketHilbert (q * d) := by
  have hs : m.divisors.filter (fun d => q.Coprime (m / d)) = m.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact hc.of_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
  rw [hilbertDilation_ramanujanPacket_divisors m q hm hq, hs]
  have h := Finset.sum_erase_add m.divisors (fun d => ramanujanPacketHilbert (q * d))
    (Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩)
  simp only [mul_one] at h
  rw [← h, add_sub_cancel_right]

theorem hilbertDilation_packet_sub_mem_mixedClosure_of_coprime (m q : ℕ)
    (hm : 0 < m) (hq : 1 < q) (hc : q.Coprime m) :
    hilbertDilation m hm (ramanujanPacketHilbert q) - ramanujanPacketHilbert q ∈ mixedClosure := by
  rw [hilbertDilation_packet_sub_eq_coprime_divisors m q hm hq hc]
  apply mixedClosure.sum_mem
  intro d hd
  obtain ⟨hd1, hdmem⟩ := Finset.mem_erase.mp hd
  have hdpos := Nat.pos_of_mem_divisors hdmem
  exact mixed_packet_mem_closure (q * d) (hq.trans_le (Nat.le_mul_of_pos_right _ hdpos))
    (not_isPrimePow_mul_of_coprime hq (by omega)
      (hc.of_dvd_right (Nat.dvd_of_mem_divisors hdmem)))

theorem fullScreening_dilation_packet_of_coprime (m q : ℕ)
    (hm : 0 < m) (hq : 1 < q) (hc : q.Coprime m) :
    fullScreening (hilbertDilation m hm (ramanujanPacketHilbert q)) =
      limitScreenedPacket q := by
  have he := fullScreening_eq_zero_of_mem
    (hilbertDilation_packet_sub_mem_mixedClosure_of_coprime m q hm hq hc)
  rw [map_sub, fullScreening_packet] at he
  exact sub_eq_zero.mp he

private theorem hilbertDilation_prime_pow_packet (p a k : ℕ)
    (hp : p.Prime) (hk : 0 < k) :
    hilbertDilation (p ^ a) (pow_pos hp.pos a) (ramanujanPacketHilbert (p ^ k)) =
      ramanujanPacketHilbert (p ^ (k + a)) := by
  induction a with
  | zero => simp only [pow_zero, add_zero, hilbertDilation_one]
  | succ a ih =>
    have hi := congrArg hilbertSequence ih
    simp only [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert] at hi
    apply hilbertSequence_injective
    simp only [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert]
    rw [pow_succ' p a, ← dilation_comp, hi, Nat.add_succ, pow_succ']
    funext n
    exact (ramanujanPacket_mul_prime_of_dvd p (p ^ (k + a)) n hp
      (Nat.one_lt_pow (by omega) hp.one_lt) (dvd_pow_self p (by omega))).symm

/-- The action on the prime-power class retains exactly the valuation of the
dilation parameter at that prime. -/
theorem fullScreening_dilation_primePow (m p k : ℕ)
    (hm : 0 < m) (hp : p.Prime) (hk : 0 < k) :
    fullScreening (hilbertDilation m hm (limitScreenedPacket (p ^ k))) =
      limitScreenedPacket (p ^ (k + m.factorization p)) := by
  let a := m.factorization p
  let r := m / p ^ a
  have hr : 0 < r := Nat.ordCompl_pos p hm.ne'
  have he : r * p ^ a = m := (Nat.mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self m p)
  have hcop : p.Coprime r := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hm.ne')
  rw [← fullScreening_packet, fullScreening_dilation_fullScreening]
  calc
    _ = fullScreening (hilbertDilation r hr
        (hilbertDilation (p ^ a) (pow_pos hp.pos a) (ramanujanPacketHilbert (p ^ k)))) := by
      rw [hilbertDilation_comp]
      apply congrArg fullScreening
      apply hilbertSequence_injective
      simp only [hilbertDilation_sequence, he]
    _ = _ := by
      rw [hilbertDilation_prime_pow_packet p a k hp hk]
      exact fullScreening_dilation_packet_of_coprime r _ hr
        (Nat.one_lt_pow (by omega) hp.one_lt) (hcop.pow_left _)

/-- In the screened space coprime raw residues add. -/
theorem fullScreening_rawResidue_mul_of_coprime (a b : ℕ)
    (ha : 1 < a) (hb : 1 < b) (hc : a.Coprime b) :
    fullScreening (rawResidueAtom (a * b - 2)) =
      fullScreening (rawResidueAtom (a - 2)) + fullScreening (rawResidueAtom (b - 2)) := by
  have hab : 1 < a * b := ha.trans_le (Nat.le_mul_of_pos_right _ (by omega))
  have hres : hilbertDilation a (by omega) (rawResidueAtom (b - 2)) =
      rawResidueAtom (a * b - 2) - rawResidueAtom (a - 2) := by
    apply hilbertSequence_injective
    funext n
    rw [hilbertDilation_sequence]
    have hB : hilbertSequence (rawResidueAtom (b - 2)) = residue b := by
      funext j
      rw [rawResidueAtom_sequence, show b - 2 + 2 = b by omega]
    rw [hB, residue_mul_floor, ← anchoredEvaluationCLM_apply, map_sub,
      anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply, rawResidueAtom_sequence,
      rawResidueAtom_sequence, show a * b - 2 + 2 = a * b by omega,
      show a - 2 + 2 = a by omega]
  have he : fullScreening (hilbertDilation a (by omega) (rawResidueAtom (b - 2))) =
      fullScreening (rawResidueAtom (b - 2)) := by
    rw [rawResidueAtom_eq_packet_divisor_sum b hb]
    change fullScreening (hilbertDilationContinuous a (by omega) (∑ d ∈ _, _)) =
      fullScreening (∑ d ∈ _, _)
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd, hd1⟩ := Finset.mem_filter.mp hd
    rw [hilbertDilationContinuous_apply, fullScreening_dilation_packet_of_coprime a d
      (by omega) hd1 (hc.symm.of_dvd_left (Nat.dvd_of_mem_divisors hd)), fullScreening_packet]
  rw [hres, map_sub] at he
  exact sub_eq_iff_eq_add'.mp he

/-- Annihilators of mixed conductors give coprime-additive pairings on residues. -/
theorem mixed_orthogonal_rawResidue_mul_of_coprime {x : ThresholdHilbert}
    (hx : x ∈ mixedClosureᗮ) (a b : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : a.Coprime b) :
    inner ℝ (rawResidueAtom (a * b - 2)) x =
      inner ℝ (rawResidueAtom (a - 2)) x + inner ℝ (rawResidueAtom (b - 2)) x := by
  have hs (z : ThresholdHilbert) : inner ℝ (fullScreening z) x = inner ℝ z x := by
    change inner ℝ (z - mixedClosure.starProjection z) x = _
    rw [inner_sub_left, (Submodule.mem_orthogonal _ _).mp hx _
      (mixedClosure.starProjection_apply_mem z), sub_zero]
  rw [← hs (rawResidueAtom (a * b - 2)), fullScreening_rawResidue_mul_of_coprime a b ha hb hc,
    inner_add_left, hs, hs]


theorem mixed_packet_mul_of_coprime_mem_window {a b M : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : a.Coprime b) (hM : a * b ≤ M) :
    ramanujanPacketHilbert (a * b) ∈ mixedSpace (Finset.Icc 2 M) := by
  have hab : 1 < a * b := ha.trans_le (Nat.le_mul_of_pos_right _ (by omega))
  exact Submodule.subset_span ⟨⟨a * b, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, hM⟩, not_isPrimePow_mul_of_coprime ha hb hc⟩⟩, rfl⟩

/-- The algebraic space generated by coprime dilation differences of
prime-power packets. -/
def coprimeDilationSpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {x | ∃ (p k r : ℕ) (hr : 0 < r), p.Prime ∧ 0 < k ∧ p.Coprime r ∧
    x = hilbertDilation r hr (ramanujanPacketHilbert (p ^ k)) -
      ramanujanPacketHilbert (p ^ k)}

private theorem mixed_packet_mem_coprimeDilationSpan (q : ℕ)
    (hq : 1 < q) (hmix : ¬ IsPrimePow q) :
    ramanujanPacketHilbert q ∈ coprimeDilationSpan := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : q ≠ 1)
    let k := q.factorization p
    let r := q / p ^ k
    have hq0 : q ≠ 0 := by omega
    have hk : 0 < k := Nat.Prime.factorization_pos_of_dvd hp hq0 hpd
    have hr : 0 < r := Nat.ordCompl_pos p hq0
    have hc : p.Coprime r := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hq0)
    have he : p ^ k * r = q := Nat.ordProj_mul_ordCompl_eq_self q p
    have hpk : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    have hr1 : r ≠ 1 := by
      intro h
      exact hmix ((isPrimePow_nat_iff q).mpr ⟨p, k, hp, hk, by simpa only [h, mul_one] using he⟩)
    let F := r.divisors.erase 1
    have htop : r ∈ F := Finset.mem_erase.mpr
      ⟨hr1, Nat.mem_divisors.mpr ⟨dvd_rfl, hr.ne'⟩⟩
    have hg : hilbertDilation r hr (ramanujanPacketHilbert (p ^ k)) -
        ramanujanPacketHilbert (p ^ k) ∈ coprimeDilationSpan :=
      Submodule.subset_span ⟨p, k, r, hr, hp, hk, hc, rfl⟩
    rw [hilbertDilation_packet_sub_eq_coprime_divisors r (p ^ k) hr hpk (hc.pow_left k)] at hg
    have hrest : ∑ d ∈ F.erase r, ramanujanPacketHilbert (p ^ k * d) ∈ coprimeDilationSpan := by
      apply coprimeDilationSpan.sum_mem
      intro d hd
      obtain ⟨hdr, hd'⟩ := Finset.mem_erase.mp hd
      obtain ⟨hd1, hdmem⟩ := Finset.mem_erase.mp hd'
      have hdvd := Nat.dvd_of_mem_divisors hdmem
      have hdpos := Nat.pos_of_mem_divisors hdmem
      have hdlt : d < r := lt_of_le_of_ne (Nat.le_of_dvd hr hdvd) hdr
      have hlt : p ^ k * d < q := he ▸ Nat.mul_lt_mul_of_pos_left hdlt (pow_pos hp.pos _)
      exact ih _ hlt (hpk.trans_le (Nat.le_mul_of_pos_right _ hdpos))
        (not_isPrimePow_mul_of_coprime hpk (by omega) ((hc.pow_left k).of_dvd_right hdvd))
    have ht := Finset.sum_erase_add F (fun d => ramanujanPacketHilbert (p ^ k * d)) htop
    rw [he] at ht
    change (∑ d ∈ F, ramanujanPacketHilbert (p ^ k * d)) ∈ coprimeDilationSpan at hg
    rw [← ht] at hg
    simpa only [add_sub_cancel_left] using coprimeDilationSpan.sub_mem hg hrest

theorem coprimeDilationSpan_closure_eq_mixedClosure :
    coprimeDilationSpan.topologicalClosure = mixedClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨p, k, r, hr, hp, hk, hc, rfl⟩
      exact hilbertDilation_packet_sub_mem_mixedClosure_of_coprime r (p ^ k) hr
        (Nat.one_lt_pow hk.ne' hp.one_lt) (hc.pow_left k)
    · exact isClosed_closure
  · unfold mixedClosure
    apply Submodule.topologicalClosure_mono
    apply iSup_le
    intro N
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    obtain ⟨hq, hmix⟩ := Finset.mem_filter.mp q.property
    exact mixed_packet_mem_coprimeDilationSpan q.val
      (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hq).1) hmix

theorem mem_mixedClosure_orthogonal_iff_coprime_dilation (h : ThresholdHilbert) :
    h ∈ mixedClosureᗮ ↔
      ∀ (p k r : ℕ) (hr : 0 < r), p.Prime → 0 < k → p.Coprime r →
        inner ℝ (hilbertDilation r hr (ramanujanPacketHilbert (p ^ k))) h =
          inner ℝ (ramanujanPacketHilbert (p ^ k)) h := by
  constructor
  · intro hh p k r hr hp hk hc
    have he := (mixedClosure.mem_orthogonal _).mp hh _
      (hilbertDilation_packet_sub_mem_mixedClosure_of_coprime r (p ^ k) hr
        (Nat.one_lt_pow hk.ne' hp.one_lt) (hc.pow_left k))
    exact sub_eq_zero.mp (by simpa only [inner_sub_left] using he)
  · intro hh
    apply (mixedClosure.mem_orthogonal h).mpr
    have hle : (mixedClosure : Set ThresholdHilbert) ⊆ {x | inner ℝ x h = 0} := by
      rw [← coprimeDilationSpan_closure_eq_mixedClosure]
      apply closure_minimal _ (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
      intro x hx
      change x ∈ coprimeDilationSpan at hx
      change inner ℝ x h = 0
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, k, r, hr, hp, hk, hc, rfl⟩ := hx
        rw [inner_sub_left, hh p k r hr hp hk hc, sub_self]
      | zero => simp
      | add x y _ _ ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
      | smul a x _ ih => rw [real_inner_smul_left, ih, mul_zero]
    exact fun x hx => hle hx

end RiemannResearch.RH.Pareto.PrimePowerSchur
