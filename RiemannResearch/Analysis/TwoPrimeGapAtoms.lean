import RiemannResearch.Analysis.TwoPrimeCompactCollision

/-!
# Exact fixed-height gap atoms from compact Fourier tests

Polarization with a translated copy of the sample reads the multiplicity of
each prescribed signed difference, including zero. Together with the
two-prime collision reconstruction this gives inversion on the finite
physical pair measure and every test supported on its finite difference set.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Classical
namespace RiemannResearch.Analysis.TwoPrimeCompactCollision
open OrdinateCollisionCertificate
variable {ι : Type*} [Fintype ι]

def gapAtom (y : ι → ℝ) (s : ℝ) : ℕ :=
  ∑ i, ∑ j, if y i - y j = s then 1 else 0

def shiftedUnion (y : ι → ℝ) (s : ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim y (fun j => y j + s)

theorem shiftedUnion_collision (y : ι → ℝ) (s : ℝ) :
    occurrenceCollision (shiftedUnion y s) = 2 * occurrenceCollision y + 2 * gapAtom y s := by
  classical
  have hr : (∑ i, ∑ j, if y i + s = y j then (1 : ℕ) else 0) =
      gapAtom y s := by
    rw [Finset.sum_comm]
    simp only [gapAtom, sub_eq_iff_eq_add, eq_comm (a := _ + s), add_comm s]
  simp only [occurrenceCollision, shiftedUnion, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, add_left_inj, Finset.sum_add_distrib]
  let c := occurrenceCollision y
  let d := ∑ i, ∑ j, if y i = y j + s then (1 : ℕ) else 0
  let e := ∑ i, ∑ j, if y i + s = y j then (1 : ℕ) else 0
  change (c + e) + (d + c) = 2*c + 2*gapAtom y s
  have hd : d = gapAtom y s := by simp only [d, gapAtom, sub_eq_iff_eq_add, add_comm s]
  change e = gapAtom y s at hr
  omega

/-- Inverting at any signed difference uses squared Fourier amplitudes of the
original sample and a translated copy. The same formula includes the zero atom. -/
theorem compact_polarization_tendsto_gapAtom (y : ι → ℝ) (s : ℝ) :
    Tendsto (fun M => (compactEnergy (shiftedUnion y s) M - 2 * compactEnergy y M)/2)
      atTop (𝓝 (gapAtom y s : ℝ)) := by
  have h := ((compactEnergy_tendsto (shiftedUnion y s)).sub
    ((compactEnergy_tendsto y).const_mul 2)).div_const 2
  rw [shiftedUnion_collision] at h
  push_cast at h
  have he : (((2 : ℝ) * occurrenceCollision y + 2 * gapAtom y s) -
      2 * occurrenceCollision y) / 2 = (gapAtom y s : ℝ) := by ring
  simpa only [he] using h

/-- Translation of every occurrence changes the trace by a common unit phase. -/
theorem occurrenceAmplitude_translate (y : ι → ℝ) (s u : ℝ) :
    occurrenceAmplitude (fun i => y i + s) u = occurrencePhase u s * occurrenceAmplitude y u := by
  simp only [occurrenceAmplitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [occurrencePhase, occurrencePhase, occurrencePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem shiftedUnion_amplitude (y : ι → ℝ) (s u : ℝ) :
    occurrenceAmplitude (shiftedUnion y s) u =
    (1 + occurrencePhase u s) * occurrenceAmplitude y u := by
  have h := occurrenceAmplitude_translate y s u
  simp only [occurrenceAmplitude] at h ⊢
  simp only [shiftedUnion, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_mul, one_mul, h]

/-- The two compact energies in polarization can be computed from the same
modulus-squared trace. This translated union needs no additional zero data. -/
theorem shiftedUnion_trace_normSq (y : ι → ℝ) (s u : ℝ) :
    Complex.normSq (occurrenceAmplitude (shiftedUnion y s) u) =
      Complex.normSq (1 + occurrencePhase u s) * Complex.normSq (occurrenceAmplitude y u) := by
  rw [shiftedUnion_amplitude, Complex.normSq_mul]

theorem shifted_factor_normSq (s u : ℝ) :
    Complex.normSq (1 + occurrencePhase u s) = 2 + 2 * Real.cos (u*s) := by
  rw [Complex.normSq_add, Complex.normSq_one, occurrencePhase,
    Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp only [one_pow, one_mul, Complex.conj_re, Complex.exp_ofReal_mul_I_re]
  ring

/-- The inverse cosine transform of the compact product Fejér average
at a fixed difference. Only the squared amplitudes of the original
sample enter this expression. -/
theorem compact_cosine_reconstructs_gap (y : ι → ℝ) (s : ℝ) :
    Tendsto (fun M : ℕ =>
      (∑ a : Fin (M+1) × Fin (M+1), ∑ b : Fin (M+1) × Fin (M+1),
        Real.cos ((wordFrequency a-wordFrequency b)*s) *
          Complex.normSq (occurrenceAmplitude y (wordFrequency a-wordFrequency b))) /
        ((M+1 : ℕ) : ℝ)^4) atTop (𝓝 (gapAtom y s : ℝ)) := by
  have hid (M : ℕ) :
      (compactEnergy (shiftedUnion y s) M - 2 * compactEnergy y M)/2 =
      (∑ a : Fin (M+1) × Fin (M+1), ∑ b : Fin (M+1) × Fin (M+1),
        Real.cos ((wordFrequency a-wordFrequency b)*s) *
          Complex.normSq (occurrenceAmplitude y (wordFrequency a-wordFrequency b))) /
        ((M+1 : ℕ) : ℝ)^4 := by
    simp only [compactEnergy_eq_fourier, shiftedUnion_trace_normSq, shifted_factor_normSq,
      add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  simpa only [← hid] using compact_polarization_tendsto_gapAtom y s

/-- Summing the reconstructed atoms on a finite set pairs any real test with
the complete contribution from differences in that set. The set may be the
entire finite difference support or just its strictly positive part. -/
theorem sum_weighted_gapAtoms (y : ι → ℝ) (S : Finset ℝ) (f : ℝ → ℝ) :
    (∑ s ∈ S, f s * (gapAtom y s : ℝ)) =
      ∑ i, ∑ j, if y i-y j ∈ S then f (y i-y j) else 0 := by
  classical
  simp only [gapAtom, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [Finset.sum_ite_eq]

theorem compact_polarization_tendsto_weighted_test (y : ι → ℝ) (S : Finset ℝ) (f : ℝ → ℝ) :
    Tendsto (fun M => ∑ s ∈ S, f s *
      ((compactEnergy (shiftedUnion y s) M - 2 * compactEnergy y M) / 2)) atTop
      (𝓝 (∑ i, ∑ j, if y i-y j ∈ S then f (y i-y j) else 0)) := by
  rw [← sum_weighted_gapAtoms y S f]
  exact tendsto_finsetSum _ fun s _ => (compact_polarization_tendsto_gapAtom y s).const_mul (f s)

end RiemannResearch.Analysis.TwoPrimeCompactCollision
