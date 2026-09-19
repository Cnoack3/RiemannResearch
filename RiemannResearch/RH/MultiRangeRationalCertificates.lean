import RiemannResearch.RH.MultiRangeCertificateConvergence

/-! Exact rational arithmetic for Section 7 of the multi-range research note.
Finite energies and pairings retain signed products before any tail bound.
All equalities below identify rational calculations with the real objectives.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative Probability.ConditionalIID Analysis.Cesaro

def rationalResidue (d n : ℕ) : ℚ := (n % d : ℕ) / (d : ℚ)
def rationalCesaro (F : ℕ → ℚ) (t : ℕ) : ℚ :=
  (∑ n ∈ Finset.Icc 1 t, F n) / (t : ℚ)
def rationalConditionalWeight (k : ℕ) : ℚ :=
  2 / (((k+1 : ℕ) : ℚ)+1) / (((k+1 : ℕ) : ℚ)+2)
def rationalPrefixPairing (F G : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N,
    rationalConditionalWeight k * rationalCesaro F (k+1) * rationalCesaro G (k+1)
def rationalPrefixEnergy (F : ℕ → ℚ) (N : ℕ) : ℚ := rationalPrefixPairing F F N

def rationalDivisorAnchor (A d n : ℕ) : ℚ :=
  (A : ℚ)/(d : ℚ)*rationalResidue A n-rationalResidue d n

def rationalCanonicalMobiusHead (Y n : ℕ) : ℚ :=
  -(∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℚ) * rationalResidue d n) +
    ((Y+1 : ℕ) : ℚ) *
      (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℚ)/(d : ℚ)) *
        rationalResidue (Y+1) n

def rationalCorrectedMobiusHead (Y : ℕ) (s : Finset ℕ) (x : ℕ → ℚ) (n : ℕ) : ℚ :=
  rationalCanonicalMobiusHead Y n + ∑ d ∈ s, x d * rationalDivisorAnchor (Y+1) d n

@[simp] theorem rationalResidue_cast (d n : ℕ) :
    (rationalResidue d n : ℝ) = residueFraction d n := by
  simp [rationalResidue, residueFraction]

@[simp] theorem rationalCesaro_cast (F : ℕ → ℚ) (t : ℕ) :
    (rationalCesaro F t : ℝ) = cesaro (fun n => (F n : ℝ)) t := by
  simp [rationalCesaro, cesaro]

@[simp] theorem rationalConditionalWeight_cast (k : ℕ) :
    (rationalConditionalWeight k : ℝ) = conditionalWeight k := by
  simp [rationalConditionalWeight, conditionalWeight, mixtureWeight, div_div]

@[simp] theorem rationalPrefixPairing_cast (F G : ℕ → ℚ) (N : ℕ) :
    (rationalPrefixPairing F G N : ℝ) =
      ∑ k ∈ Finset.range N, conditionalWeight k *
        cesaro (fun n => (F n : ℝ)) (k+1) * cesaro (fun n => (G n : ℝ)) (k+1) := by
  simp [rationalPrefixPairing]

@[simp] theorem rationalPrefixEnergy_cast (F : ℕ → ℚ) (N : ℕ) :
    (rationalPrefixEnergy F N : ℝ) = conditionalMeanPrefix (fun n => (F n : ℝ)) N := by
  simp [rationalPrefixEnergy, rationalPrefixPairing_cast, conditionalMeanPrefix, pow_two,
    mul_assoc]

@[simp] theorem rationalDivisorAnchor_cast (A d n : ℕ) :
    (rationalDivisorAnchor A d n : ℝ) = divisorAnchorDirection A d n := by
  simp [rationalDivisorAnchor, divisorAnchorDirection]

@[simp] theorem rationalCanonicalMobiusHead_cast (Y n : ℕ) :
    (rationalCanonicalMobiusHead Y n : ℝ) = canonicalMobiusHead Y n := by
  simp [rationalCanonicalMobiusHead, canonicalMobiusHead, mobiusReciprocalSum]

@[simp] theorem rationalCorrectedMobiusHead_cast (Y : ℕ) (s : Finset ℕ)
    (x : ℕ → ℚ) (n : ℕ) :
    (rationalCorrectedMobiusHead Y s x n : ℝ) =
      correctedMobiusHead Y s (fun d => (x d : ℝ)) n := by
  simp [rationalCorrectedMobiusHead, correctedMobiusHead, divisorRangeCorrection]

/-- The actual finite Gram and source entries are exact rational numbers. -/
theorem divisorAnchor_prefix_entries_rational (Y d e N : ℕ) :
    (∃ q : ℚ, (q : ℝ) = ∑ k ∈ Finset.range N, conditionalWeight k *
      cesaro (divisorAnchorDirection (Y+1) d) (k+1) *
        cesaro (divisorAnchorDirection (Y+1) e) (k+1)) ∧
    (∃ q : ℚ, (q : ℝ) = ∑ k ∈ Finset.range N, conditionalWeight k *
      cesaro (canonicalMobiusHead Y) (k+1) *
        cesaro (divisorAnchorDirection (Y+1) d) (k+1)) := by
  constructor
  · refine ⟨rationalPrefixPairing (rationalDivisorAnchor (Y+1) d)
      (rationalDivisorAnchor (Y+1) e) N, ?_⟩
    simp
  · refine ⟨rationalPrefixPairing (rationalCanonicalMobiusHead Y)
      (rationalDivisorAnchor (Y+1) d) N, ?_⟩
    simp

end RiemannResearch.RH.Pareto
