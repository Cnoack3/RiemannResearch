import RiemannResearch.Analysis.HigherPowerErrorTransfer
import RiemannResearch.Analysis.ZeroSamplingErrorTransfer
import RiemannResearch.Analysis.ZeroSamplingHilbertSchmidt

/-!
# Balanced sampling: arithmetic rows and dense moment budgets

These are finite transfer theorems for complex Fourier matrices.  Their entry
estimates, arithmetic row budgets, and logarithmic moment budgets are explicit
hypotheses.  No zeta-zero estimate, independence premise, or RH is postulated.
In particular, an entrywise norm envelope never requires aligned complex errors.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic

variable {ι : Type*}

/-- The coefficient-weighted Schur bound for a symmetric real envelope. -/
theorem weighted_symmetric_row_budget (s : Finset ι) (a : ι → ℂ)
    (E : ι → ι → ℝ) (K : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, E i j ≤ K) :
    (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j) ≤
      K * coefficientEnergy s a := by
  let L : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ ^ 2 * E i j
  let M : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a j‖ ^ 2 * E i j
  have hLM : M = L := by
    dsimp [L, M]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have hL : L ≤ K * coefficientEnergy s a := by
    calc
      L = ∑ i ∈ s, ‖a i‖ ^ 2 * (∑ j ∈ s, E i j) := by
        simp only [L, Finset.mul_sum]
      _ ≤ ∑ i ∈ s, ‖a i‖ ^ 2 * K := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = K * coefficientEnergy s a := by
        simp only [coefficientEnergy, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j) ≤
        ∑ i ∈ s, ∑ j ∈ s,
          ((‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2) * E i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hE i hi j hj)
      nlinarith [sq_nonneg (‖a i‖ - ‖a j‖)]
    _ = (L + M) / 2 := by
      have hterm : ∀ i j,
          ((‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2) * E i j =
            (‖a i‖ ^ 2 * E i j) / 2 + (‖a j‖ ^ 2 * E i j) / 2 := by
        intros
        ring
      simp_rw [hterm, Finset.sum_add_distrib]
      simp only [← Finset.sum_div]
      dsimp [L, M]
      ring
    _ = L := by rw [hLM]; ring
    _ ≤ K * coefficientEnergy s a := hL

/-- A symmetric arithmetic row bound and an independent dense weighted budget
can be added before taking any uniform coefficient estimate. -/
theorem form_comparison_row_weighted_envelope (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (C D : ι → ι → ℝ)
    (c K H : ℝ) (hc : 0 ≤ c)
    (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, C i j = C j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, C i j ≤ K)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ c * (C i j + D i j))
    (hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * D i j) ≤
      H * coefficientEnergy s a) :
    ‖form s S a - form s B a‖ ≤ c * (K + H) * coefficientEnergy s a := by
  have hlinear := weighted_symmetric_row_budget s a C K hC hsym hrow
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
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖a i‖ * ‖a j‖ * (c * (C i j + D i j)) := by
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
    _ = c * (K + H) * coefficientEnergy s a := by ring

/-- Scalar higher-power error transfer combined with an arithmetic row budget.
The dense weighted error remains explicit for subsequent moment estimates. -/
theorem power_kernel_form_comparison_weighted (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (E : ι → ι → ℝ)
    (q : ℕ) (hq : 2 ≤ q) (K H : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ E i j)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymE : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ^ (q - 1) * E i j ≤ K)
    (hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j ^ q) ≤
      H * coefficientEnergy s a) :
    ‖form s (fun i j => (‖S i j‖ ^ q : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ q : ℂ)) a‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (q - 2)) * (K + H) * coefficientEnergy s a := by
  apply form_comparison_row_weighted_envelope s _ _ a
    (fun i j => ‖B i j‖ ^ (q - 1) * E i j) (fun i j => E i j ^ q)
    ((q : ℝ) * (2 : ℝ) ^ (q - 2)) K H
  · positivity
  · intro i hi j hj
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (hE i hi j hj)
  · intro i hi j hj
    rw [hsymB i hi j hj, hsymE i hi j hj]
  · exact hrow
  · intro i hi j hj
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using
      RiemannResearch.ZeroSampling.norm_higher_power_error_transfer
        (S i j) (B i j) (hE i hi j hj) q hq (herror i hi j hj)
  · exact hdense

/-- A nonnegative dense moment envelope requires no alignment with the complex
sampling error.  Its moment is the exact `2*q` moment of the entry envelope. -/
theorem power_kernel_form_comparison_of_moment (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (E : ι → ι → ℝ)
    (q : ℕ) (hq : 2 ≤ q) (K M : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ E i j)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymE : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ^ (q - 1) * E i j ≤ K)
    (hmoment : (∑ i ∈ s, ∑ j ∈ s, E i j ^ (2 * q)) ≤ M) :
    ‖form s (fun i j => (‖S i j‖ ^ q : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ q : ℂ)) a‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (q - 2)) * (K + Real.sqrt M) *
        coefficientEnergy s a := by
  apply power_kernel_form_comparison_weighted s S B a E q hq K (Real.sqrt M)
    hE herror hsymB hsymE hrow
  apply weighted_envelope_hilbertSchmidt_bound s a (fun i j => E i j ^ q) M
  · intro i hi j hj
    exact pow_nonneg (hE i hi j hj) _
  · simpa only [← pow_mul, Nat.mul_comm q 2] using hmoment

/-- Structured balanced covariance.  `A` can be the squared logarithmic ratio;
its arithmetic row budgets and `2*q` moment are supplied separately.  Setting
`q=2*r` gives the precise finite transfer used by the balanced convolution law. -/
theorem structured_power_kernel_form_comparison (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (A : ι → ι → ℝ)
    (q : ℕ) (hq : 2 ≤ q) (d L η K_A K_0 M : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ d / L * A i j + η)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymA : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hrowA : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ^ (q - 1) * A i j ≤ K_A)
    (hrow0 : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ^ (q - 1) ≤ K_0)
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
  have hrow : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ^ (q - 1) * E i j ≤
      α * K_A + η * K_0 := by
    intro i hi
    calc
      (∑ j ∈ s, ‖B i j‖ ^ (q - 1) * E i j) =
          α * (∑ j ∈ s, ‖B i j‖ ^ (q - 1) * A i j) +
          η * (∑ j ∈ s, ‖B i j‖ ^ (q - 1)) := by
        dsimp [E]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ α * K_A + η * K_0 :=
        add_le_add (mul_le_mul_of_nonneg_left (hrowA i hi) hα)
          (mul_le_mul_of_nonneg_left (hrow0 i hi) hη)
  have hmoment' : (∑ i ∈ s, ∑ j ∈ s, (A i j ^ q) ^ 2) ≤ M := by
    simpa only [← pow_mul, Nat.mul_comm q 2] using hmoment
  have hweightedA := weighted_envelope_hilbertSchmidt_bound s a
    (fun i j => A i j ^ q) M
    (fun i hi j hj => pow_nonneg (hA i hi j hj) _) hmoment'
  have hones : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (1 : ℝ)) ≤
      (s.card : ℝ) * coefficientEnergy s a := by
    apply weighted_symmetric_row_budget s a (fun _ _ => (1 : ℝ)) (s.card : ℝ)
    · intros; norm_num
    · intros; rfl
    · intro i hi
      simp
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
      _ = f * (α ^ q * Real.sqrt M + (s.card : ℝ) * η ^ q) *
          coefficientEnergy s a := by ring
  have hresult := power_kernel_form_comparison_weighted s S B a E q hq
    (α * K_A + η * K_0)
    (f * (α ^ q * Real.sqrt M + (s.card : ℝ) * η ^ q))
    hE herror hsymB
    (fun i hi j hj => by dsimp [E]; rw [hsymA i hi j hj]) hrow hdense
  simpa only [α, f] using hresult

/-- The pair specialization retains the sharp linear coefficient from the
exact square perturbation.  Its dense remainder has coefficient two rather
than the larger coefficient obtained from the generic higher-power bound. -/
theorem structured_square_kernel_form_comparison (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (A : ι → ι → ℝ)
    (d L η K_A K_0 M₄ : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ d / L * A i j + η)
    (hsymB : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hsymA : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hrowA : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ * A i j ≤ K_A)
    (hrow0 : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ≤ K_0)
    (hmoment : (∑ i ∈ s, ∑ j ∈ s, A i j ^ 4) ≤ M₄) :
    ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
      (2 * (d / L) * K_A + 2 * η * K_0 +
        2 * (d / L) ^ 2 * Real.sqrt M₄ + 2 * (s.card : ℝ) * η ^ 2) *
        coefficientEnergy s a := by
  let α : ℝ := d / L
  let E : ι → ι → ℝ := fun i j => α * A i j + η
  let C : ι → ι → ℝ := fun i j => 2 * ‖B i j‖ * E i j
  have hα : 0 ≤ α := div_nonneg hd hL.le
  have hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j := by
    intro i hi j hj
    exact add_nonneg (mul_nonneg hα (hA i hi j hj)) hη
  have hrow : ∀ i ∈ s, ∑ j ∈ s, C i j ≤
      2 * α * K_A + 2 * η * K_0 := by
    intro i hi
    calc
      (∑ j ∈ s, C i j) =
          2 * α * (∑ j ∈ s, ‖B i j‖ * A i j) +
          2 * η * (∑ j ∈ s, ‖B i j‖) := by
        dsimp [C, E]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ 2 * α * K_A + 2 * η * K_0 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hrowA i hi) (by positivity))
          (mul_le_mul_of_nonneg_left (hrow0 i hi) (by positivity))
  have hmoment' : (∑ i ∈ s, ∑ j ∈ s, (A i j ^ 2) ^ 2) ≤ M₄ := by
    simpa only [← pow_mul] using hmoment
  have hweightedA := weighted_envelope_hilbertSchmidt_bound s a
    (fun i j => A i j ^ 2) M₄
    (fun i hi j hj => sq_nonneg _) hmoment'
  have hones : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (1 : ℝ)) ≤
      (s.card : ℝ) * coefficientEnergy s a := by
    apply weighted_symmetric_row_budget s a (fun _ _ => (1 : ℝ)) (s.card : ℝ)
    · intros; norm_num
    · intros; rfl
    · intro i hi
      simp
  have hp : ∀ i j, E i j ^ 2 ≤ 2 * α ^ 2 * A i j ^ 2 + 2 * η ^ 2 := by
    intro i j
    dsimp [E]
    nlinarith [sq_nonneg (α * A i j - η)]
  have hterm : ∀ i j,
      ‖a i‖ * ‖a j‖ * (2 * α ^ 2 * A i j ^ 2 + 2 * η ^ 2) =
        2 * α ^ 2 * (‖a i‖ * ‖a j‖ * A i j ^ 2) +
        2 * η ^ 2 * (‖a i‖ * ‖a j‖ * (1 : ℝ)) := by
    intros
    ring
  have hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j ^ 2) ≤
      (2 * α ^ 2 * Real.sqrt M₄ + 2 * (s.card : ℝ) * η ^ 2) *
        coefficientEnergy s a := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j ^ 2) ≤
          ∑ i ∈ s, ∑ j ∈ s,
            ‖a i‖ * ‖a j‖ * (2 * α ^ 2 * A i j ^ 2 + 2 * η ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hp i j) (by positivity)
      _ = 2 * α ^ 2 * (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * A i j ^ 2) +
          2 * η ^ 2 * (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (1 : ℝ)) := by
        simp_rw [hterm, Finset.sum_add_distrib]
        simp only [← Finset.mul_sum]
      _ ≤ 2 * α ^ 2 * (Real.sqrt M₄ * coefficientEnergy s a) +
          2 * η ^ 2 * ((s.card : ℝ) * coefficientEnergy s a) :=
        add_le_add (mul_le_mul_of_nonneg_left hweightedA (by positivity))
          (mul_le_mul_of_nonneg_left hones (by positivity))
      _ = (2 * α ^ 2 * Real.sqrt M₄ + 2 * (s.card : ℝ) * η ^ 2) *
          coefficientEnergy s a := by ring
  have hresult := form_comparison_row_weighted_envelope s
    (fun i j => (‖S i j‖ ^ 2 : ℂ))
    (fun i j => (‖B i j‖ ^ 2 : ℂ)) a C (fun i j => E i j ^ 2)
    1 (2 * α * K_A + 2 * η * K_0)
    (2 * α ^ 2 * Real.sqrt M₄ + 2 * (s.card : ℝ) * η ^ 2)
    (by norm_num)
    (fun i hi j hj => by
      dsimp [C]
      exact mul_nonneg (by positivity) (hE i hi j hj))
    (fun i hi j hj => by
      dsimp [C, E]
      rw [hsymB i hi j hj, hsymA i hi j hj]) hrow
    (fun i hi j hj => by
      simpa only [C, one_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_square_sub_le_of_error (S i j) (B i j) (E i j)
          (hE i hi j hj) (herror i hi j hj)) hdense
  simpa only [one_mul, α, add_assoc] using hresult

end RiemannResearch.Analysis.ZeroSamplingQuadratic
