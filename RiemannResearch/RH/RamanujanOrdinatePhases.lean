import RiemannResearch.Analysis.ActualOrdinateAngularLaw
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
# Ramanujan sums as strong limits of additive zeta-ordinate phases

The classical divisor formula in ParetoPacketGreenGram is identified with
the reduced-residue character sum by geometric summation and Möbius inversion.
One cofinal sequence per residue then works for all physical indices and
every summable positive weight simultaneously, in particular for P and Q.

Sources: Montgomery--Vaughan, *Multiplicative Number Theory I*, Theorem 4.1
(character and divisor formulas); Hlawka (1975) for the classical angular
equidistribution input. Its precise Lean density hypothesis is displayed.
-/
noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis RiemannResearch.Analysis.ActualZeroOrdinate

/-- Reduced residues with one representative in [0,q). -/
def reducedResidues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => a.Coprime q)

def residueAngle (q a : ℕ) : ℝ := 2 * Real.pi * a / q

private def root (q : ℕ) := Complex.exp (2 * Real.pi * Complex.I / q)

private theorem root_pow_exp (q a : ℕ) :
    root q ^ a = Complex.exp (2 * Real.pi * Complex.I * ((a:ℂ) / q)) := by
  rw [root, ← Complex.exp_nat_mul]
  congr 1
  ring

private theorem root_pow_phase (q a n : ℕ) :
    (root q ^ a)^n = ZeroOrdinate.phase n (residueAngle q a) := by
  simp only [root, ← Complex.exp_nat_mul, ZeroOrdinate.phase, residueAngle]
  congr 1
  push_cast
  ring

private theorem sum_nthRoots_pow (q n : ℕ) (hq : 0 < q) :
    (∑ z ∈ Polynomial.nthRootsFinset q (1:ℂ), z^n) =
      if q ∣ n then (q:ℂ) else 0 := by
  classical
  have hζ : IsPrimitiveRoot (root q) q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hr : Polynomial.nthRootsFinset q (1:ℂ) = (Finset.range q).image (fun i => root q ^ i) := by
    unfold Polynomial.nthRootsFinset
    rw [hζ.nthRoots_eq (α:=(1:ℂ)) (one_pow q)]
    simp
    ext z
    simp [Multiset.mem_map]
  rw [hr,Finset.sum_image (fun i hi j hj hij =>
    hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij)]
  have hswitch (i : ℕ) : (root q ^ i)^n = (root q ^ n)^i := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  simp_rw [hswitch]
  by_cases hd : q ∣ n
  · simp [hd,(hζ.pow_eq_one_iff_dvd n).mpr hd]
  · rw [if_neg hd]
    have hpow : (root q ^ n)^q = 1 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul,hζ.pow_eq_one,one_pow]
    have h := geom_sum_mul (root q ^ n) q
    rw [hpow,sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (fun e => hd (hζ.dvd_of_pow_eq_one n e)))

/-- Arithmetic Fourier identity, valid for arbitrary positive conductor. -/
theorem ramanujanSum_eq_primitive_powers (q n : ℕ) (hq : 0 < q) :
    (ramanujanSum q n : ℂ) = ∑ z ∈ primitiveRoots q ℂ, z^n := by
  classical
  let f (d : ℕ) := ∑ z ∈ primitiveRoots d ℂ, z^n
  let g (d : ℕ) : ℂ := if d ∣ n then d else 0
  have h (k : ℕ) (hk : 0 < k) : ∑ d ∈ k.divisors, f d = g k := by
    rw [show g k = ∑ z ∈ Polynomial.nthRootsFinset k (1:ℂ), z^n from
      (sum_nthRoots_pow k n hk).symm, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
      Finset.sum_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij)]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f:=f) (g:=g)).mp h q hq
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℂ) * g b)] at hi
  change (ramanujanSum q n : ℂ) = f q
  rw [← hi]
  unfold ramanujanSum
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n <;> simp [g,hdn]

theorem ramanujanSum_eq_reduced_phases (q n : ℕ) (hq : 0 < q) :
    (ramanujanSum q n : ℂ) =
      ∑ a ∈ reducedResidues q, ZeroOrdinate.phase n (residueAngle q a) := by
  classical
  have hζ : IsPrimitiveRoot (root q) q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hset : primitiveRoots q ℂ = (reducedResidues q).image (fun a => root q ^ a) := by
    ext z
    rw [mem_primitiveRoots hq, Complex.isPrimitiveRoot_iff _ _ hq.ne',Finset.mem_image]
    constructor
    · rintro ⟨i,hi,hc,he⟩
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hc⟩,(root_pow_exp q i).trans he⟩
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨hlt,hc⟩ := Finset.mem_filter.mp hi
      exact ⟨i,Finset.mem_range.mp hlt,hc,(root_pow_exp q i).symm⟩
  have hinj : ∀ i ∈ reducedResidues q, ∀ j ∈ reducedResidues q,
      (fun a : ℕ => root q ^ a) i = (fun a : ℕ => root q ^ a) j → i = j := by
    intro i hi j hj hij
    exact hζ.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
  rw [ramanujanSum_eq_primitive_powers q n hq, hset, Finset.sum_image hinj]
  exact Finset.sum_congr rfl (fun i _ => root_pow_phase q i n)

def ordinatePhasePacket (q : ℕ) (ρ : ℕ → ℕ → ℂ) (j n : ℕ) : ℂ :=
  ∑ a ∈ reducedResidues q, ZeroOrdinate.phase n (ρ a j).im

/-- The complete squared L² error on physical coordinates for a weight w. -/
def ordinatePacketError (w : ℕ → ℝ) (q : ℕ) (ρ : ℕ → ℕ → ℂ) (j : ℕ) : ℝ :=
  ∑' n, w n * ‖ordinatePhasePacket q ρ j n - (ramanujanSum q n : ℂ)‖^2

private theorem packet_norm_le (s : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) :
    ‖∑ a ∈ s, ZeroOrdinate.phase n (t a)‖ ≤ (s.card : ℝ) := by
  simpa using (_root_.norm_sum_le s (fun a => ZeroOrdinate.phase n (t a)))

private theorem tendsto_weighted_sq_error {F : ℕ → ℕ → ℂ} {g : ℕ → ℂ} {B : ℝ}
    (hpoint : ∀ n, Tendsto (fun j => F j n) atTop (𝓝 (g n)))
    (hbound : ∀ j n, ‖F j n - g n‖ ≤ B) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) :
    Tendsto (fun j => ∑' n, w n * ‖F j n - g n‖ ^ 2) atTop (𝓝 0) := by
  have hpt (n : ℕ) : Tendsto (fun j => w n * ‖F j n - g n‖ ^ 2) atTop (𝓝 (0:ℝ)) := by
    simpa using (((hpoint n).sub_const (g n)).norm.pow 2).const_mul (w n)
  have hdom (j n : ℕ) : ‖w n * ‖F j n - g n‖ ^ 2‖ ≤ w n * B ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound j n) 2) (hw n)
  simpa using tendsto_tsum_of_dominated_convergence
    (hsum.mul_right (B ^ 2)) hpt (Eventually.of_forall hdom)

/-- The choice is independent of both n and the weight w. Summability is
used only after the exact equality for the finite character sum. -/
theorem exists_ordinate_ramanujan_approximation (q : ℕ) (hq : 0 < q)
    (hs : FixedStripConcentration) :
    ∃ ρ : ℕ → ℕ → ℂ,
      (∀ a j, IsNontrivialZero (ρ a j) ∧ 0 < (ρ a j).im) ∧
      (∀ a, Tendsto (fun j => (ρ a j).im) atTop atTop) ∧
      (∀ n, Tendsto (fun j => ordinatePhasePacket q ρ j n) atTop (𝓝 (ramanujanSum q n : ℂ))) ∧
      ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → Summable w →
        Tendsto (ordinatePacketError w q ρ) atTop (𝓝 0) := by
  choose ρ hzero hhigh hphase using
    fun a => exists_ordinate_sequence_all_harmonics hs (residueAngle q a)
  have hpoint (n : ℕ) : Tendsto (fun j => ordinatePhasePacket q ρ j n) atTop
      (𝓝 (ramanujanSum q n : ℂ)) := by
    rw [ramanujanSum_eq_reduced_phases q n hq]
    simpa [ordinatePhasePacket] using
      tendsto_finsetSum (reducedResidues q) (fun a _ => hphase a (n:ℤ))
  refine ⟨ρ,hzero,hhigh,hpoint,?_⟩
  intro w hw hsum
  let B : ℝ := 2 * (reducedResidues q).card
  have hbound (j n : ℕ) : ‖ordinatePhasePacket q ρ j n - (ramanujanSum q n : ℂ)‖ ≤ B := by
    rw [ramanujanSum_eq_reduced_phases q n hq]
    exact (norm_sub_le _ _).trans (by
      dsimp [B,ordinatePhasePacket]
      linarith [packet_norm_le (reducedResidues q) (fun a => (ρ a j).im) n,
        packet_norm_le (reducedResidues q) (residueAngle q) n])
  change Tendsto (fun j => ∑' n, w n *
    ‖ordinatePhasePacket q ρ j n - (ramanujanSum q n : ℂ)‖^2) atTop (𝓝 0)
  exact tendsto_weighted_sq_error hpoint hbound w hw hsum

/-- The same actual zeros and the same packet index work for P and Q. -/
theorem exists_ordinate_ramanujan_P_and_Q (q : ℕ) (hq : 0 < q)
    (hs : FixedStripConcentration) :
    ∃ ρ : ℕ → ℕ → ℂ, (∀ a j, IsNontrivialZero (ρ a j) ∧ 0 < (ρ a j).im) ∧
      (∀ a, Tendsto (fun j => (ρ a j).im) atTop atTop) ∧
      Tendsto (ordinatePacketError positiveWeight q ρ) atTop (𝓝 0) ∧
      Tendsto (ordinatePacketError ZetaTwoHilbert.positiveQWeight q ρ) atTop (𝓝 0) := by
  obtain ⟨ρ,hz,hh,_,hw⟩ := exists_ordinate_ramanujan_approximation q hq hs
  exact ⟨ρ,hz,hh,hw _ positiveWeight_nonneg positiveWeight_summable,
    hw _ ZetaTwoHilbert.positiveQWeight_nonneg ZetaTwoHilbert.positiveQWeight_summable⟩

/-- The same ordinate supplies all characters of each divisor of a fixed period. -/
def stageOrdinatePacket (L q : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  ∑ a ∈ reducedResidues q, ZeroOrdinate.phase (((L / q) * a * n : ℕ) : ℝ) t

private theorem stage_phase_eq {L q : ℕ} (hL : 0 < L) (hq : 0 < q) (hd : q ∣ L)
    (a n : ℕ) :
    ZeroOrdinate.phase (((L / q) * a * n : ℕ) : ℝ) (residueAngle L 1) =
      ZeroOrdinate.phase n (residueAngle q a) := by
  have hc : ((L / q : ℕ) : ℂ) * (q : ℂ) = (L : ℂ) := by exact_mod_cast Nat.div_mul_cancel hd
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hlC : ((L / q : ℕ) : ℂ) ≠ 0 := by
    intro hx
    exact hLC (by simpa only [hx, zero_mul] using hc.symm)
  unfold ZeroOrdinate.phase residueAngle
  congr 1
  push_cast
  rw [← hc]
  field_simp [hqC, hlC] <;> ring

/-- At a fixed CRT period L, one sequence of actual zeta zeros works for every
divisor q of L, every reduced residue, every harmonic, and every summable weight. -/
theorem exists_common_ordinate_ramanujan_of_dvd (L : ℕ) (hL : 0 < L)
    (hs : FixedStripConcentration) :
    ∃ ρ : ℕ → ℂ, (∀ j, IsNontrivialZero (ρ j) ∧ 0 < (ρ j).im) ∧
      Tendsto (fun j => (ρ j).im) atTop atTop ∧
      ∀ q : ℕ, 0 < q → q ∣ L →
        (∀ a n : ℕ, Tendsto (fun j =>
          ZeroOrdinate.phase (((L / q) * a * n : ℕ) : ℝ) (ρ j).im) atTop
          (𝓝 (ZeroOrdinate.phase n (residueAngle q a)))) ∧
        (∀ n, Tendsto (fun j => stageOrdinatePacket L q (ρ j).im n) atTop
          (𝓝 (ramanujanSum q n : ℂ))) ∧
        ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → Summable w →
          Tendsto (fun j => ∑' n, w n *
            ‖stageOrdinatePacket L q (ρ j).im n - (ramanujanSum q n : ℂ)‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨ρ, hz, hh, hphase⟩ := exists_ordinate_sequence_all_harmonics hs (residueAngle L 1)
  refine ⟨ρ, hz, hh, ?_⟩
  intro q hq hd
  have ha (a n : ℕ) : Tendsto (fun j =>
      ZeroOrdinate.phase (((L / q) * a * n : ℕ) : ℝ) (ρ j).im) atTop
      (𝓝 (ZeroOrdinate.phase n (residueAngle q a))) := by
    rw [← stage_phase_eq hL hq hd a n]
    simpa only [Int.cast_natCast] using hphase ((((L / q) * a * n : ℕ) : ℤ))
  have hpoint (n : ℕ) : Tendsto (fun j => stageOrdinatePacket L q (ρ j).im n) atTop
      (𝓝 (ramanujanSum q n : ℂ)) := by
    rw [ramanujanSum_eq_reduced_phases q n hq]
    exact tendsto_finsetSum (reducedResidues q) (fun a _ => ha a n)
  refine ⟨ha, hpoint, ?_⟩
  intro w hw hsum
  refine tendsto_weighted_sq_error (B := 2 * (reducedResidues q).card) hpoint ?_ w hw hsum
  intro j n
  have hleft : ‖stageOrdinatePacket L q (ρ j).im n‖ ≤ ((reducedResidues q).card : ℝ) := by
    simpa [stageOrdinatePacket] using _root_.norm_sum_le (reducedResidues q)
      (fun a => ZeroOrdinate.phase (((L / q) * a * n : ℕ) : ℝ) (ρ j).im)
  rw [ramanujanSum_eq_reduced_phases q n hq]
  exact (norm_sub_le _ _).trans (by
    linarith [packet_norm_le (reducedResidues q) (residueAngle q) n])

/-- A common sequence of Mellin phases cannot recover a nontrivial additive
character on all positive indices: its value at one is fixed. -/
theorem not_mellin_limit_nontrivial_additive {z : ℂ} (hz : z ≠ 1) :
    ¬ ∃ γ : ℕ → ℝ, ∀ n : ℕ, 0 < n → Tendsto
      (fun j => (n:ℂ)^((γ j:ℂ)*Complex.I)) atTop (𝓝 (z^n)) := by
  rintro ⟨γ,h⟩
  have he : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 z) := by simpa using h 1 (by decide)
  exact hz (tendsto_nhds_unique he tendsto_const_nhds)

end RiemannResearch.RH.Pareto
