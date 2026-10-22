import RiemannResearch.Analysis.WeightedSamplingSchur
import RiemannResearch.Analysis.HigherPowerErrorTransfer

/-!
# Balanced sampling with positive weighted arithmetic rows

All finite transfers are unconditional. Actual zero-sum envelopes, weighted
arithmetic rows, and logarithmic moments are separate visible hypotheses.
The weight can be `n^(-1/2)`: no stronger unweighted arithmetic row estimate
is substituted for the weighted one.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic

variable {ι : Type*}

/-- Combine a positive weighted Schur envelope and a separate dense budget. -/
theorem form_comparison_positive_weighted_row_envelope (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (C D : ι → ι → ℝ)
    (w : ι → ℝ) (c K H : ℝ) (hc : 0 ≤ c)
    (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, C i j = C j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, C i j * w j) ≤ K * w i)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ c * (C i j + D i j))
    (hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * D i j) ≤
      H * coefficientEnergy s a) :
    ‖form s S a - form s B a‖ ≤ c * (K + H) * coefficientEnergy s a := by
  have hlinear := weighted_symmetric_schur_budget s a C w K hC hsym hw hrow
  have hterm : ∀ i j,
      ‖a i‖ * ‖a j‖ * (c * (C i j + D i j)) =
        c * (‖a i‖ * ‖a j‖ * C i j) +
        c * (‖a i‖ * ‖a j‖ * D i j) := by
    intros
    ring
  calc
    ‖form s S a - form s B a‖ ≤
        ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖S i j - B i j‖ :=
      form_comparison_weighted s S B a
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (c * (C i j + D i j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hentry i hi j hj) (by positivity)
    _ = c * ((∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * C i j) +
        (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * D i j)) := by
      simp_rw [hterm, Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]
      ring
    _ ≤ c * (K * coefficientEnergy s a + H * coefficientEnergy s a) :=
      mul_le_mul_of_nonneg_left (add_le_add hlinear hdense) hc
    _ = _ := by ring

/-- Higher-power transfer using the actual positive weighted arithmetic row.
The dense weighted error is retained as a separate hypothesis. -/
theorem power_kernel_form_comparison_positive_weighted (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (E : ι → ι → ℝ)
    (w : ι → ℝ) (q : ℕ) (hq : 2 ≤ q) (K H : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ E i j)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymE : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s,
      (∑ j ∈ s, (‖B i j‖ ^ (q - 1) * E i j) * w j) ≤ K * w i)
    (hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j ^ q) ≤
      H * coefficientEnergy s a) :
    ‖form s (fun i j => (‖S i j‖ ^ q : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ q : ℂ)) a‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (q - 2)) * (K + H) * coefficientEnergy s a := by
  apply form_comparison_positive_weighted_row_envelope s _ _ a
    (fun i j => ‖B i j‖ ^ (q - 1) * E i j) (fun i j => E i j ^ q)
    w ((q : ℝ) * (2 : ℝ) ^ (q - 2)) K H
  · positivity
  · intro i hi j hj
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (hE i hi j hj)
  · intro i hi j hj
    rw [hsymB i hi j hj, hsymE i hi j hj]
  · exact hw
  · exact hrow
  · intro i hi j hj
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using
      RiemannResearch.ZeroSampling.norm_higher_power_error_transfer
        (S i j) (B i j) (hE i hi j hj) q hq (herror i hi j hj)
  · exact hdense

/-- A supplied `2*q` moment controls the dense part of the weighted theorem. -/
theorem power_kernel_positive_weighted_of_moment (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (E : ι → ι → ℝ)
    (w : ι → ℝ) (q : ℕ) (hq : 2 ≤ q) (K M : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ E i j)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymE : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s,
      (∑ j ∈ s, (‖B i j‖ ^ (q - 1) * E i j) * w j) ≤ K * w i)
    (hmoment : (∑ i ∈ s, ∑ j ∈ s, E i j ^ (2 * q)) ≤ M) :
    ‖form s (fun i j => (‖S i j‖ ^ q : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ q : ℂ)) a‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (q - 2)) * (K + Real.sqrt M) *
        coefficientEnergy s a := by
  apply power_kernel_form_comparison_positive_weighted s S B a E w q hq K
    (Real.sqrt M) hE herror hsymB hsymE hw hrow
  apply weighted_envelope_hilbertSchmidt_bound s a (fun i j => E i j ^ q) M
  · intro i hi j hj
    exact pow_nonneg (hE i hi j hj) _
  · simpa only [← pow_mul, Nat.mul_comm q 2] using hmoment

/-- Structured logarithmic higher-power transfer with the correct weighted
arithmetic row budgets. Setting `q=2*r` gives balanced `2*r`-ordinate sampling. -/
theorem structured_power_kernel_positive_weighted (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (A : ι → ι → ℝ)
    (w : ι → ℝ) (q : ℕ) (hq : 2 ≤ q) (d L η K_A K_0 M : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ d / L * A i j + η)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymA : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrowA : ∀ i ∈ s,
      (∑ j ∈ s, (‖B i j‖ ^ (q - 1) * A i j) * w j) ≤ K_A * w i)
    (hrow0 : ∀ i ∈ s,
      (∑ j ∈ s, ‖B i j‖ ^ (q - 1) * w j) ≤ K_0 * w i)
    (hmoment : (∑ i ∈ s, ∑ j ∈ s, A i j ^ (2 * q)) ≤ M) :
    ‖form s (fun i j => (‖S i j‖ ^ q : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ q : ℂ)) a‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (q - 2)) *
        (d / L * K_A + η * K_0 + (2 : ℝ) ^ (q - 1) *
          ((d / L) ^ q * Real.sqrt M + (s.card : ℝ) * η ^ q)) *
        coefficientEnergy s a := by
  let α : ℝ := d / L
  let E : ι → ι → ℝ := fun i j => α * A i j + η
  let f : ℝ := (2 : ℝ) ^ (q - 1)
  have hα : 0 ≤ α := div_nonneg hd hL.le
  have hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j := by
    intro i hi j hj
    exact add_nonneg (mul_nonneg hα (hA i hi j hj)) hη
  have hrow : ∀ i ∈ s,
      (∑ j ∈ s, (‖B i j‖ ^ (q - 1) * E i j) * w j) ≤
        (α * K_A + η * K_0) * w i := by
    intro i hi
    calc
      (∑ j ∈ s, (‖B i j‖ ^ (q - 1) * E i j) * w j) =
          α * (∑ j ∈ s, (‖B i j‖ ^ (q - 1) * A i j) * w j) +
          η * (∑ j ∈ s, ‖B i j‖ ^ (q - 1) * w j) := by
        dsimp [E]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ α * (K_A * w i) + η * (K_0 * w i) :=
        add_le_add (mul_le_mul_of_nonneg_left (hrowA i hi) hα)
          (mul_le_mul_of_nonneg_left (hrow0 i hi) hη)
      _ = _ := by ring
  have hmoment' : (∑ i ∈ s, ∑ j ∈ s, (A i j ^ q) ^ 2) ≤ M := by
    simpa only [← pow_mul, Nat.mul_comm q 2] using hmoment
  have hweightedA := weighted_envelope_hilbertSchmidt_bound s a
    (fun i j => A i j ^ q) M
    (fun i hi j hj => pow_nonneg (hA i hi j hj) _) hmoment'
  have hones : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (1 : ℝ)) ≤
      (s.card : ℝ) * coefficientEnergy s a := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    calc
      _ = (∑ i ∈ s, ‖a i‖) ^ 2 := by
        simp only [mul_one, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := hcs
  have hp : ∀ i ∈ s, ∀ j ∈ s,
      E i j ^ q ≤ f * (α ^ q * A i j ^ q + η ^ q) := by
    intro i hi j hj
    simpa only [E, f, mul_pow] using
      RiemannResearch.ZeroSampling.add_pow_le_two_pow_pred
        (mul_nonneg hα (hA i hi j hj)) hη q (by omega)
  have hterm : ∀ i j,
      ‖a i‖ * ‖a j‖ * (f * (α ^ q * A i j ^ q + η ^ q)) =
        f * α ^ q * (‖a i‖ * ‖a j‖ * A i j ^ q) +
        f * η ^ q * (‖a i‖ * ‖a j‖ * (1 : ℝ)) := by
    intros
    ring
  have hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j ^ q) ≤
      f * (α ^ q * Real.sqrt M + (s.card : ℝ) * η ^ q) *
        coefficientEnergy s a := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j ^ q) ≤
          ∑ i ∈ s, ∑ j ∈ s,
            ‖a i‖ * ‖a j‖ * (f * (α ^ q * A i j ^ q + η ^ q)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hp i hi j hj) (by positivity)
      _ = f * α ^ q * (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * A i j ^ q) +
          f * η ^ q * (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (1 : ℝ)) := by
        simp_rw [hterm, Finset.sum_add_distrib]
        simp only [← Finset.mul_sum]
      _ ≤ f * α ^ q * (Real.sqrt M * coefficientEnergy s a) +
          f * η ^ q * ((s.card : ℝ) * coefficientEnergy s a) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hweightedA (by dsimp [f]; positivity))
          (mul_le_mul_of_nonneg_left hones (by dsimp [f]; positivity))
      _ = _ := by ring
  have hresult := power_kernel_form_comparison_positive_weighted s S B a E w q hq
    (α * K_A + η * K_0)
    (f * (α ^ q * Real.sqrt M + (s.card : ℝ) * η ^ q))
    hE herror hsymB
    (fun i hi j hj => by dsimp [E]; rw [hsymA i hi j hj]) hw hrow hdense
  simpa only [α, f] using hresult

end RiemannResearch.Analysis.ZeroSamplingQuadratic
