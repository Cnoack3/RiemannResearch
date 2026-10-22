import RiemannResearch.Analysis.MellinNormalizedResidue
import RiemannResearch.RH.CanonicalMobiusWeightedEndpoint
import RiemannResearch.RH.ParetoMellinFunctional

/-!
# Möbius combinations and their actual Mellin transforms

Statement provenance: Manzur, Noor, Quintero, arXiv:2606.16097 (2026),
https://arxiv.org/html/2606.16097v1 . The raw generators follow that paper;
the boundary correction is the project's canonical Möbius family.
The value at s=1 is supplied by the removable Mellin representation.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

/-- The paper's generator, using its removable value at s=1. -/
def hardyMobiusGenerator (d : ℕ) (s : ℂ) : ℂ :=
  if hd : 0 < d then -paretoMellin (normalizedResidueHilbert d hd) s else 0

theorem hardyMobiusGenerator_eq_zeta (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    hardyMobiusGenerator d s =
      ((d : ℂ) ^ (-s) - 1 / (d : ℂ)) * riemannZeta s / s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hi := normalizedResidue_mellin_zeta d hd s hs hs1
  rw [hardyMobiusGenerator, dif_pos hd]
  apply (eq_div_iff hs0).mpr
  linear_combination -hi

theorem normalizedResidue_mellin_eq_neg_hardyMobiusGenerator
    (d : ℕ) (hd : 0 < d) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (normalizedResidueHilbert d hd) s = -hardyMobiusGenerator d s := by
  simp [hardyMobiusGenerator, hd]

/-- The uncorrected finite Möbius combination in the actual Pareto Hilbert space. -/
def rawMobiusHilbert (N : ℕ) : ThresholdHilbert :=
  -(∑ d ∈ (Finset.Icc 1 N).attach,
    (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
      normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1)

def rawHardyMobiusSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℂ) * hardyMobiusGenerator d s

def correctedHardyMobiusSum (N : ℕ) (s : ℂ) : ℂ :=
  rawHardyMobiusSum N s -
    (((N + 1 : ℕ) : ℂ) * (mobiusReciprocalSum N : ℂ)) *
      hardyMobiusGenerator (N + 1) s

theorem canonicalMobiusHilbert_eq_raw_add (N : ℕ) :
    canonicalMobiusHilbert N = rawMobiusHilbert N +
      (((N + 1 : ℕ) : ℝ) * mobiusReciprocalSum N) •
        normalizedResidueHilbert (N + 1) (Nat.succ_pos _) := rfl

theorem rawMobiusHilbert_mellin (N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (rawMobiusHilbert N) s = rawHardyMobiusSum N s := by
  change (paretoMellinContinuous s hs) (rawMobiusHilbert N) = _
  unfold rawMobiusHilbert
  rw [map_neg, map_sum]
  simp only [map_smul]
  change -(∑ d ∈ (Finset.Icc 1 N).attach,
    (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
      paretoMellin (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1) s) = _
  simp_rw [normalizedResidue_mellin_eq_neg_hardyMobiusGenerator _ _ s (by linarith)]
  simp only [Complex.real_smul, Complex.ofReal_intCast, mul_neg, Finset.sum_neg_distrib, neg_neg]
  exact Finset.sum_attach (Finset.Icc 1 N)
    (fun d => (ArithmeticFunction.moebius d : ℂ) * hardyMobiusGenerator d s)

theorem canonicalMobiusHilbert_mellin (N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (canonicalMobiusHilbert N) s = correctedHardyMobiusSum N s := by
  rw [canonicalMobiusHilbert_eq_raw_add, paretoMellin_add _ _ s hs,
    rawMobiusHilbert_mellin N s hs, paretoMellin_smul,
    normalizedResidue_mellin_eq_neg_hardyMobiusGenerator _ _ s (by linarith)]
  simp only [correctedHardyMobiusSum, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_natCast, mul_neg, sub_eq_add_neg]

theorem canonicalMobiusResidual_mellin (N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertOne - canonicalMobiusHilbert N) s =
      1 / s - correctedHardyMobiusSum N s := by
  change (paretoMellinContinuous s hs) (hilbertOne - canonicalMobiusHilbert N) = _
  rw [map_sub]
  exact congrArg₂ (· - ·) (paretoMellin_one s hs)
    (canonicalMobiusHilbert_mellin N s hs)

end RiemannResearch.RH.Pareto
