import RiemannResearch.RH.QPrimeCRTCarries
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.FiniteGramBlockTrace
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Representative-independent complete Q carry blocks

Source: user-provided `CRT Carries and Squarefree Residual Exhaustion`,
19 October 2026, Sections 2 and 5. The literal floor-carry realization is
the existing `QPrimeCRTCarries.carryVector_sequence`; it is not re-assumed.
The span theorem below permits every old divisor, including composite ones.

This file does not prove an asymptotic score lower bound or RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCarryScreenedBlock
open ZetaTwoHilbert
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι]

def screen (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection] :
    QHilbert →ₗ[ℝ] QHilbert :=
  LinearMap.id - W.starProjection.toLinearMap

theorem screen_apply (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (f : QHilbert) : screen W f = f - W.starProjection f := rfl

theorem screen_mem (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (f : QHilbert) (hf : f ∈ W) : screen W f = 0 := by
  rw [screen_apply, Submodule.starProjection_eq_self_iff.mpr hf, sub_self]

/-- Orthogonal screening retains an exact nonnegative energy remainder. -/
theorem screen_energy (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (f : QHilbert) :
    ‖screen W f‖ ^ 2 = ‖f‖ ^ 2 - ‖W.starProjection f‖ ^ 2 := by
  have h := (W.mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal f)
    (W.starProjection f) (W.starProjection_apply_mem f)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [screen_apply, norm_sub_sq_real]
  have hc : inner ℝ f (W.starProjection f) = inner ℝ (W.starProjection f) f :=
    real_inner_comm _ _
  rw [hc]
  linarith

theorem screen_energy_le (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (f : QHilbert) : ‖screen W f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [screen_energy]
  exact sub_le_self _ (sq_nonneg _)

/-- For a certified CRT table, the existing carryVector is exactly its
literal integer floor carry. Once screened, its representative disappears. -/
theorem screen_carryVector (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (d : ℕ) (p : ι → ℕ) (a : ι → ℤ)
    (hp : ∀ i, qResidue (p i) ∈ W) :
    screen W (QPrimeCRTCarries.carryVector d p a) =
      -(screen W (qResidue d)) := by
  simp only [QPrimeCRTCarries.carryVector, map_sub, map_sum, map_smul,
    screen_mem W _ (hp _), smul_zero, Finset.sum_const_zero, zero_sub]

theorem screened_representative_invariance (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (d : ℕ) (p : ι → ℕ) (a b : ι → ℤ)
    (hp : ∀ i, qResidue (p i) ∈ W) :
    screen W (QPrimeCRTCarries.carryVector d p a) =
      screen W (QPrimeCRTCarries.carryVector d p b) := by
  rw [screen_carryVector W d p a hp, screen_carryVector W d p b hp]

/-- Both signs cancel in the actual complete-Q Gram entry. -/
theorem screened_gram (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (d e : ℕ) (p q : ι → ℕ) (a b : ι → ℤ)
    (hp : ∀ i, qResidue (p i) ∈ W) (hq : ∀ i, qResidue (q i) ∈ W) :
    inner ℝ (screen W (QPrimeCRTCarries.carryVector d p a))
      (screen W (QPrimeCRTCarries.carryVector e q b)) =
      inner ℝ (screen W (qResidue d)) (screen W (qResidue e)) := by
  rw [screen_carryVector W d p a hp, screen_carryVector W e q b hq]
  simp only [inner_neg_left, inner_neg_right, neg_neg]

theorem screened_score (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (r : QHilbert) (d : ℕ)
    (p : ι → ℕ) (a : ι → ℤ) (hp : ∀ i, qResidue (p i) ∈ W) :
    inner ℝ r (screen W (QPrimeCRTCarries.carryVector d p a)) =
      -inner ℝ r (screen W (qResidue d)) := by
  rw [screen_carryVector W d p a hp, inner_neg_right]

/-- The two-coordinate real carry. For integer CRT coefficients its
pointwise realization is the floor carry supplied by QPrimeCRTCarries. -/
def pairVector (p d : ℕ) (a b : ℝ) : QHilbert :=
  a • qResidue p + b • qResidue d - qResidue (p*d)

theorem pairVector_sequence (p d : ℕ) (a b : ℝ) (n : ℕ) :
    qSequence (pairVector p d a b) n =
      a * ArithmeticCumulative.residueFraction p n +
      b * ArithmeticCumulative.residueFraction d n -
      ArithmeticCumulative.residueFraction (p*d) n := by
  change qSequenceLinear
    (a • qResidue p + b • qResidue d - qResidue (p*d)) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change a * qSequence (qResidue p) n + b * qSequence (qResidue d) n -
    qSequence (qResidue (p*d)) n = _
  simp only [qSequence_qResidue]

theorem screen_pairVector (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (p d : ℕ) (a b : ℝ)
    (hp : qResidue p ∈ W) (hd : qResidue d ∈ W) :
    screen W (pairVector p d a b) = -screen W (qResidue (p*d)) := by
  simp only [pairVector, map_sub, map_add, map_smul,
    screen_mem W _ hp, screen_mem W _ hd, smul_zero, add_zero, zero_sub]

/-- The raw representative may be large, while the screened energy has
the small conductor bound of the single composite atom. -/
theorem screened_pair_energy_bound (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (p d : ℕ) (a b : ℝ)
    (hp : qResidue p ∈ W) (hd : qResidue d ∈ W) (hpd : 2 ≤ p * d) :
    ‖screen W (pairVector p d a b)‖ ^ 2 ≤
      2 / (ZetaTwoProbability.zetaTwo * ((p*d : ℕ) : ℝ)) := by
  rw [screen_pairVector W p d a b hp hd, norm_neg]
  exact (screen_energy_le W (qResidue (p*d))).trans
    (ZetaTwoHilbert.qResidue_norm_sq_le_two_div (p*d) hpd)

/-- An unconditional upper bound for the complete new-prime Gram trace.
The finite family d can be the entire old divisor dictionary. -/
theorem complete_trace_bound (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (p : ℕ) (d : ι → ℕ) (a b : ι → ℝ)
    (hp : qResidue p ∈ W) (hd : ∀ i, qResidue (d i) ∈ W)
    (hp2 : 2 ≤ p) (hd2 : ∀ i, 2 ≤ d i) :
    (∑ i, ‖screen W (pairVector p (d i) (a i) (b i))‖ ^ 2) ≤
      (2 / (ZetaTwoProbability.zetaTwo * (p : ℝ))) *
        ∑ i, 1 / (d i : ℝ) := by
  calc
    _ ≤ ∑ i, 2 / (ZetaTwoProbability.zetaTwo * ((p*d i : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply screened_pair_energy_bound W p (d i) (a i) (b i) hp (hd i)
      exact hp2.trans (Nat.le_mul_of_pos_right p (by have := hd2 i; omega))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

omit [Fintype ι] in
/-- Simultaneous changes of every CRT representative leave the entire
screened family unchanged. -/
theorem screen_pair_family (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (p : ℕ) (d : ι → ℕ) (a b a' b' : ι → ℝ)
    (hp : qResidue p ∈ W) (hd : ∀ i, qResidue (d i) ∈ W) :
    (fun i => screen W (pairVector p (d i) (a i) (b i))) =
      (fun i => screen W (pairVector p (d i) (a' i) (b' i))) := by
  funext i
  rw [screen_pairVector W p (d i) _ _ hp (hd i),
    screen_pairVector W p (d i) _ _ hp (hd i)]

omit [Fintype ι] in
/-- All old divisor directions can occur in d: there is no restriction
to singleton prime support. This is the exact change of block coordinates. -/
theorem pair_block_span (W : Submodule ℝ QHilbert) (p : ℕ)
    (d : ι → ℕ) (a b : ι → ℝ)
    (hp : qResidue p ∈ W) (hd : ∀ i, qResidue (d i) ∈ W) :
    W ⊔ Submodule.span ℝ (Set.range (fun i => pairVector p (d i) (a i) (b i))) =
      W ⊔ Submodule.span ℝ (Set.range (fun i => qResidue (p * d i))) := by
  let U := Submodule.span ℝ (Set.range (fun i => qResidue (p * d i)))
  let V := Submodule.span ℝ (Set.range (fun i => pairVector p (d i) (a i) (b i)))
  change W ⊔ V = W ⊔ U
  have hWU : W ≤ W ⊔ U := le_sup_left
  have hU : U ≤ W ⊔ U := le_sup_right
  have hWV : W ≤ W ⊔ V := le_sup_left
  have hV : V ≤ W ⊔ V := le_sup_right
  apply le_antisymm
  · refine sup_le hWU (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    change a i • qResidue p + b i • qResidue (d i) - qResidue (p * d i) ∈ W ⊔ U
    exact (W ⊔ U).sub_mem
      ((W ⊔ U).add_mem ((W ⊔ U).smul_mem _ (hWU hp))
        ((W ⊔ U).smul_mem _ (hWU (hd i))))
      (hU (Submodule.subset_span ⟨i, rfl⟩))
  · refine sup_le hWV (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    change qResidue (p * d i) ∈ W ⊔ V
    have he : qResidue (p * d i) =
        a i • qResidue p + b i • qResidue (d i) - pairVector p (d i) (a i) (b i) := by
      unfold pairVector
      abel
    rw [he]
    exact (W ⊔ V).sub_mem
      ((W ⊔ V).add_mem ((W ⊔ V).smul_mem _ (hWV hp))
        ((W ⊔ V).smul_mem _ (hWV (hd i))))
      (hV (Submodule.subset_span ⟨i, rfl⟩))

/-- Every nontrivial old divisor occurs, with no bound on prime support. -/
abbrev BlockIndex (L : ℕ) := ↥(L.divisors.filter (fun d => 1 < d))

def extendedOldStage (L p : ℕ) : Submodule ℝ QHilbert :=
  QSquarefreeLatticePackets.divisorStage L ⊔
    Submodule.span ℝ {qResidue p}

def fullBlock (L p : ℕ) (a b : BlockIndex L → ℝ) : BlockIndex L → QHilbert :=
  fun d => pairVector p d.val (a d) (b d)

private theorem prime_mem_extended (L p : ℕ) :
    qResidue p ∈ extendedOldStage L p := by
  unfold extendedOldStage
  exact (show Submodule.span ℝ {qResidue p} ≤
    QSquarefreeLatticePackets.divisorStage L ⊔ Submodule.span ℝ {qResidue p}
    from le_sup_right) (Submodule.subset_span (by simp))

private theorem divisor_mem_extended (L p : ℕ) (d : BlockIndex L) :
    qResidue d.val ∈ extendedOldStage L p := by
  unfold extendedOldStage
  apply (show QSquarefreeLatticePackets.divisorStage L ≤
    QSquarefreeLatticePackets.divisorStage L ⊔ Submodule.span ℝ {qResidue p}
    from le_sup_left)
  exact Submodule.subset_span
    ⟨d.val, (Nat.mem_divisors.mp (Finset.mem_filter.mp d.property).1).1, rfl⟩

/-- Complete new-prime block, stated in the actual old divisor dictionary. -/
theorem fullBlock_span (L p : ℕ) (a b : BlockIndex L → ℝ) :
    extendedOldStage L p ⊔ Submodule.span ℝ (Set.range (fullBlock L p a b)) =
      extendedOldStage L p ⊔ Submodule.span ℝ
        (Set.range (fun d : BlockIndex L => qResidue (p * d.val))) := by
  exact pair_block_span (extendedOldStage L p) p (fun d : BlockIndex L => d.val)
    a b (prime_mem_extended L p) (divisor_mem_extended L p)

/-- Prime adjunction exhausts exactly the enlarged divisor stage.
For squarefree L and a fresh prime p, this includes all squarefree
conductors at the new stage, not just the old primes. -/
theorem raw_prime_block_stage (L p : ℕ) (hL : 0 < L) (hp : p.Prime) :
    extendedOldStage L p ⊔ Submodule.span ℝ
      (Set.range (fun d : BlockIndex L => qResidue (p * d.val))) =
        QSquarefreeLatticePackets.divisorStage (p * L) := by
  have hOld : QSquarefreeLatticePackets.divisorStage L ≤
      QSquarefreeLatticePackets.divisorStage (p * L) :=
    QSquarefreeLatticePackets.divisorStage_mono (dvd_mul_left L p)
  have hprime : qResidue p ∈ QSquarefreeLatticePackets.divisorStage (p * L) :=
    Submodule.subset_span ⟨p, dvd_mul_right p L, rfl⟩
  let U := Submodule.span ℝ
    (Set.range (fun d : BlockIndex L => qResidue (p * d.val)))
  have hExt : extendedOldStage L p ≤ QSquarefreeLatticePackets.divisorStage (p * L) := by
    unfold extendedOldStage
    refine sup_le hOld (Submodule.span_le.mpr ?_)
    intro x hx
    have he : x = qResidue p := Set.mem_singleton_iff.mp hx
    subst x
    exact hprime
  have hExtSup : extendedOldStage L p ≤ extendedOldStage L p ⊔ U := le_sup_left
  have hUSup : U ≤ extendedOldStage L p ⊔ U := le_sup_right
  change extendedOldStage L p ⊔ U = QSquarefreeLatticePackets.divisorStage (p * L)
  apply le_antisymm
  · refine sup_le hExt (Submodule.span_le.mpr ?_)
    rintro _ ⟨d, rfl⟩
    apply Submodule.subset_span
    refine ⟨p * d.val, Nat.mul_dvd_mul_left p ?_, rfl⟩
    exact (Nat.mem_divisors.mp (Finset.mem_filter.mp d.property).1).1
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    change qResidue d ∈ extendedOldStage L p ⊔ U
    by_cases hpd : p ∣ d
    · obtain ⟨e, he⟩ := hpd
      have heL : e ∣ L := by
        obtain ⟨k, hk⟩ := hd
        refine ⟨k, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        simpa only [he, Nat.mul_assoc] using hk
      by_cases he1 : e = 1
      · have heq : d = p := by simpa [he1] using he
        rw [heq]
        exact hExtSup (prime_mem_extended L p)
      · have hepos : 0 < e := Nat.pos_of_dvd_of_pos heL hL
        have hegt : 1 < e := by omega
        let i : BlockIndex L := ⟨e, Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨heL, ne_of_gt hL⟩, hegt⟩⟩
        apply hUSup
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        change qResidue (p * e) = qResidue d
        rw [he]
    · have hc : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
      have hdL : d ∣ L := hc.dvd_mul_left.mp hd
      apply hExtSup
      unfold extendedOldStage
      apply (show QSquarefreeLatticePackets.divisorStage L ≤
        QSquarefreeLatticePackets.divisorStage L ⊔ Submodule.span ℝ {qResidue p}
        from le_sup_left)
      exact Submodule.subset_span ⟨d, hdL, rfl⟩

theorem full_prime_block_stage (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (a b : BlockIndex L → ℝ) :
    extendedOldStage L p ⊔ Submodule.span ℝ (Set.range (fullBlock L p a b)) =
      QSquarefreeLatticePackets.divisorStage (p * L) := by
  rw [fullBlock_span, raw_prime_block_stage L p hL hp]

/-- Application of the full-block trace bound to actual screened Q carries.
Independence and the trace estimate are explicit finite hypotheses. -/
theorem carry_block_score_bound (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (p : ℕ) (d : ι → ℕ) (a b : ι → ℝ)
    (r : QHilbert)
    (hz : LinearIndependent ℝ
      (fun i => screen W (pairVector p (d i) (a i) (b i))))
    (T : ℝ) (hT : 0 < T)
    (htrace : (∑ i, ‖screen W (pairVector p (d i) (a i) (b i))‖ ^ 2) ≤ T) :
    (∑ i, (inner ℝ (screen W (pairVector p (d i) (a i) (b i))) r) ^ 2) / T ≤
      blockGain hz r :=
  blockGain_lower_of_trace_bound hz r T hT htrace

end RiemannResearch.RH.QCarryScreenedBlock
