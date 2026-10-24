import RiemannResearch.RH.ParetoAtomMellinSignature
import RiemannResearch.RH.ParetoBoundedMellin
import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic Mellin signatures of the genuine Ramanujan packets

Source: user-requested fourth Ramanujan development, October 2026.
The exact finite signed divisor identities use the project's genuine Mobius
function, complex powers, and pole-removed conductor zeta function. Bounded
physical packet sequences give the full positive half-plane of ordinary
integral convergence. The conductor identities retain the point s = 1;
only the separate zeta-factorized form excludes that point.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.RamanujanMellinSignature
open Pareto Pareto.CoefficientStabilization ParetoAtomMellinSignature
open ZetaConductorRegularization

def packetArithmeticSymbol (q : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ q.divisors.filter (fun d => 1 < d),
    (ArithmeticFunction.moebius (q / d) : ℂ) * (d : ℂ) *
      (1 / (d : ℂ) - (d : ℂ) ^ (-s))

def packetConductorSignature (q : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ q.divisors.filter (fun d => 1 < d),
    (ArithmeticFunction.moebius (q / d) : ℂ) * (d : ℂ) * conductorZeta d s

def packetArithmeticSum (n : ℕ) (a : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∑ i : Fin n, (a i : ℂ) * packetArithmeticSymbol (i.val + 2) s

def packetConductorSum (n : ℕ) (a : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∑ i : Fin n, (a i : ℂ) * packetConductorSignature (i.val + 2) s

/-- The removable point retains the exact signed logarithmic conductor sum. -/
theorem packetConductorSignature_one (q : ℕ) :
    packetConductorSignature q 1 =
      ∑ d ∈ q.divisors.filter (fun d => 1 < d),
        (ArithmeticFunction.moebius (q / d) : ℂ) * (Real.log d : ℂ) := by
  classical
  unfold packetConductorSignature
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by have := (Finset.mem_filter.mp hd).2; omega
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  rw [conductorZeta_one]
  field_simp [hd0] <;> ring

/-- The removable packet value is its complete von Mangoldt mean, for every conductor. -/
theorem packetConductorSignature_one_eq_vonMangoldt (q : ℕ) :
    packetConductorSignature q 1 = (ArithmeticFunction.vonMangoldt q : ℂ) := by
  classical
  rw [packetConductorSignature_one]
  by_cases hq : q = 0
  · subst q
    simp
  have hr : (∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q / d) : ℝ) * Real.log (d : ℝ)) =
      ArithmeticFunction.vonMangoldt q :=
    (mobius_inversion (fun d => ArithmeticFunction.vonMangoldt d)
      (fun d => Real.log (d : ℝ))).mp
      (by intro n hn; exact ArithmeticFunction.vonMangoldt_sum) q (Nat.pos_of_ne_zero hq)
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast] at hc
  apply Eq.trans ?_ hc
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hdpos := Nat.pos_of_mem_divisors hd
  have hd1 : d = 1 := by
    have hle : ¬ 1 < d := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
    omega
  simp [hd1]

/-- The full signed synthesis source at one is its actual von Mangoldt mean. -/
theorem packetConductorSum_one (n : ℕ) (a : Fin n → ℝ) :
    packetConductorSum n a 1 =
      ((∑ i : Fin n, a i * ArithmeticFunction.vonMangoldt (i.val + 2) : ℝ) : ℂ) := by
  simp only [packetConductorSum, packetConductorSignature_one_eq_vonMangoldt,
    Complex.ofReal_sum, Complex.ofReal_mul]

private theorem physical_smul (a : ℝ) (f : ThresholdHilbert) (k : ℕ) :
    hilbertSequence (a • f) k = a * hilbertSequence f k := by
  change hilbertSequenceLinear (a • f) k = _
  rw [map_smul]
  rfl

private theorem rawResidueAtom_mellin_conductor (i : ℕ) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (rawResidueAtom i) s =
      ((i + 2 : ℕ) : ℂ) * conductorZeta (i + 2) s / s := by
  rw [rawResidueAtom, paretoMellin_smul, residueAtom,
    paretoMellin_normalizedResidue_conductor (i + 2) (by omega) s hs]
  change (((i + 2 : ℕ) : ℝ) : ℂ) * (conductorZeta (i + 2) s / s) = _
  rw [Complex.ofReal_natCast]
  ring

/-- The actual packet integral has its regularized arithmetic signature at every Re(s)>0. -/
theorem paretoMellin_packet_conductor (q : ℕ) (hq : 1 < q)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (ramanujanPacketHilbert q) s = packetConductorSignature q s / s := by
  classical
  have hb : ∀ d ∈ q.divisors.filter (fun d => 1 < d), ∀ k,
      |hilbertSequence ((ArithmeticFunction.moebius (q / d) : ℝ) •
        rawResidueAtom (d - 2)) k| ≤
      |(ArithmeticFunction.moebius (q / d) : ℝ)| * (d : ℝ) := by
    intro d hd k
    have hd2 : 1 < d := (Finset.mem_filter.mp hd).2
    have he : d - 2 + 2 = d := by omega
    rw [physical_smul, abs_mul, rawResidueAtom_sequence, he]
    exact mul_le_mul_of_nonneg_left (residue_abs_le d k (by omega)) (abs_nonneg _)
  rw [ramanujanPacketHilbert_eq_divisor_sum q hq,
    paretoMellin_finset_sum_of_bounded _ _
      (fun d => |(ArithmeticFunction.moebius (q / d) : ℝ)| * (d : ℝ)) hb s hs,
    packetConductorSignature, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 : 1 < d := (Finset.mem_filter.mp hd).2
  have he : d - 2 + 2 = d := by omega
  rw [paretoMellin_smul, rawResidueAtom_mellin_conductor _ s hs, he]
  change (((ArithmeticFunction.moebius (q / d) : ℝ) : ℂ)) *
    ((d : ℂ) * conductorZeta d s / s) = _
  rw [Complex.ofReal_intCast]
  ring

/-- The finite arithmetic factorization itself needs no half-plane restriction. -/
theorem packetConductorSignature_eq_zeta (q : ℕ) (s : ℂ) (hs1 : s ≠ 1) :
    packetConductorSignature q s = riemannZeta s * packetArithmeticSymbol q s := by
  classical
  rw [packetConductorSignature, packetArithmeticSymbol, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by have := (Finset.mem_filter.mp hd).2; omega
  rw [conductorZeta_of_ne_one d hs1, conductorSymbol_eq_cpow d hdpos]
  ring

theorem paretoMellin_packet_zeta (q : ℕ) (hq : 1 < q)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    paretoMellin (ramanujanPacketHilbert q) s =
      riemannZeta s / s * packetArithmeticSymbol q s := by
  rw [paretoMellin_packet_conductor q hq s hs, packetConductorSignature_eq_zeta q s hs1]
  ring

/-- Complete bounded synthesis transforms term by term, including the removable point. -/
theorem paretoMellin_packetSynthesis_conductor (n : ℕ) (a : Fin n → ℝ)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a) s =
      packetConductorSum n a s / s := by
  classical
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ k,
      |hilbertSequence (a i • ramanujanPacketHilbert (i.val + 2)) k| ≤
      |a i| * (∑ d ∈ (i.val + 2).divisors,
        |(ArithmeticFunction.moebius ((i.val + 2) / d) : ℝ)| * (d : ℝ)) := by
    intro i _ k
    rw [physical_smul, hilbertSequence_ramanujanPacketHilbert, abs_mul]
    exact mul_le_mul_of_nonneg_left (ramanujanPacket_abs_le (i.val + 2) k) (abs_nonneg _)
  change paretoMellin (∑ i : Fin n, a i • ramanujanPacketHilbert (i.val + 2)) s = _
  rw [paretoMellin_finset_sum_of_bounded Finset.univ _
      (fun i => |a i| * (∑ d ∈ (i.val + 2).divisors,
        |(ArithmeticFunction.moebius ((i.val + 2) / d) : ℝ)| * (d : ℝ))) hb s hs,
    packetConductorSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [paretoMellin_smul, paretoMellin_packet_conductor (i.val + 2) (by omega) s hs]
  change (a i : ℂ) * (packetConductorSignature (i.val + 2) s / s) = _
  ring

theorem packetConductorSum_eq_zeta (n : ℕ) (a : Fin n → ℝ)
    (s : ℂ) (hs1 : s ≠ 1) :
    packetConductorSum n a s = riemannZeta s * packetArithmeticSum n a s := by
  classical
  rw [packetConductorSum, packetArithmeticSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [packetConductorSignature_eq_zeta (i.val + 2) s hs1]
  ring

theorem paretoMellin_packetSynthesis_zeta (n : ℕ) (a : Fin n → ℝ)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    paretoMellin (Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a) s =
      riemannZeta s / s * packetArithmeticSum n a s := by
  rw [paretoMellin_packetSynthesis_conductor n a s hs, packetConductorSum_eq_zeta n a s hs1]
  ring

end RiemannResearch.RH.RamanujanMellinSignature
