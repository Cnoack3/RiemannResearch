import RiemannResearch.Analysis.CesaroHilbertAdjoint
import RiemannResearch.Analysis.MellinCesaroHilbert
import RiemannResearch.Analysis.MellinCesaroSummability

/-!
# Bundled conditional Mellin functionals on real and complex J

Source: user-provided Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md,
Section 5; detailed construction in ConditionalMellinFunctionalProof.md.

The complexified functional is the actual Riesz map associated with the
square-summable vector conj(b_s)/sqrt(q). Its operator norm is exactly sqrt(D_s).
Restriction along the real-coordinate isometry gives the real J-to-complex
functional. No equality is claimed for the latter's real operator norm.

-/
noncomputable section
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative RH.Pareto Probability.ConditionalIID

/-- The genuine complexification of the square-root-q realization of J. -/
abbrev ConditionalComplexHilbert := lp (fun _ : ℕ => ℂ) 2

/-- Physical complex J coordinates; coordinate zero is anchored. -/
def conditionalComplexSequence (g : ConditionalComplexHilbert) : ℕ → ℂ
  | 0 => 0
  | k + 1 => g k / (Real.sqrt (conditionalWeight k) : ℂ)

theorem conditionalComplex_norm_sq (g : ConditionalComplexHilbert) :
    ‖g‖ ^ 2 = ∑' k : ℕ, ‖g k‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  congr 1
  funext k
  exact real_inner_self_eq_norm_sq (g k)

/-- The normalized coordinates of the actual complex Riesz vector. -/
def conditionalMellinDualCoordinate (s : ℂ) (k : ℕ) : ℂ :=
  star (mellinSecond s (k + 1)) / (Real.sqrt (conditionalWeight k) : ℂ)

theorem conditionalMellinDualCoordinate_norm_sq (s : ℂ) (k : ℕ) :
    ‖conditionalMellinDualCoordinate s k‖ ^ 2 =
      ‖mellinSecond s (k + 1)‖ ^ 2 / conditionalWeight k := by
  simp only [conditionalMellinDualCoordinate, norm_div, norm_star,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (conditionalWeight_pos k).le]

/-- Dual summability constructs a genuine Hilbert vector, without an axiom. -/
def conditionalMellinDualVector (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ConditionalComplexHilbert :=
  ⟨conditionalMellinDualCoordinate s, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      conditionalMellinDualCoordinate_norm_sq] using mellinSecond_dual_summable s hs⟩

@[simp] theorem conditionalMellinDualVector_apply (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (k : ℕ) :
    conditionalMellinDualVector s hs k = conditionalMellinDualCoordinate s k := rfl

theorem conditionalMellinDualVector_norm_sq (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖conditionalMellinDualVector s hs‖ ^ 2 = conditionalMellinDualSquare s := by
  rw [conditionalComplex_norm_sq]
  simp only [conditionalMellinDualVector_apply,
    conditionalMellinDualCoordinate_norm_sq, conditionalMellinDualSquare]

theorem conditionalMellinDualVector_norm (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖conditionalMellinDualVector s hs‖ = Real.sqrt (conditionalMellinDualSquare s) := by
  have h := conditionalMellinDualVector_norm_sq s hs
  have hD := conditionalMellinDualSquare_nonneg s
  have hsq := Real.sq_sqrt hD
  nlinarith [norm_nonneg (conditionalMellinDualVector s hs),
    Real.sqrt_nonneg (conditionalMellinDualSquare s)]

/-- The actual complex-linear bounded functional Lambda_s on the complexified J. -/
def conditionalComplexMellinFunctional (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ConditionalComplexHilbert →L[ℂ] ℂ :=
  innerSL ℂ (conditionalMellinDualVector s hs)

/-- The Riesz functional is exactly the requested full signed coefficient series. -/
theorem conditionalComplexMellinFunctional_apply (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (g : ConditionalComplexHilbert) :
    conditionalComplexMellinFunctional s hs g =
      ∑' k : ℕ, mellinSecond s (k + 1) * conditionalComplexSequence g (k + 1) := by
  change inner ℂ (conditionalMellinDualVector s hs) g = _
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp [RCLike.inner_apply', conditionalMellinDualVector_apply,
    conditionalMellinDualCoordinate, conditionalComplexSequence,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Physical complex coordinates have the exact q-weighted square norm. -/
theorem conditionalComplexSequence_square (g : ConditionalComplexHilbert) (k : ℕ) :
    conditionalWeight k * ‖conditionalComplexSequence g (k + 1)‖ ^ 2 = ‖g k‖ ^ 2 := by
  simp only [conditionalComplexSequence, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (conditionalWeight_pos k).le]
  field_simp [(conditionalWeight_pos k).ne']

/-- The displayed signed series has genuine summability for every complex J vector. -/
theorem conditionalComplexMellin_summable (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (g : ConditionalComplexHilbert) :
    Summable (fun k : ℕ =>
      mellinSecond s (k + 1) * conditionalComplexSequence g (k + 1)) := by
  have hg : Summable (fun k : ℕ => ‖g k‖ ^ 2) := by
    have h := Memℓp.summable (show 0 < (2 : ENNReal).toReal by norm_num) g.property
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  apply WeightedPairing.summable_pairing conditionalWeight conditionalWeight_pos
    (fun k => mellinSecond s (k + 1))
    (fun k => conditionalComplexSequence g (k + 1)) (mellinSecond_dual_summable s hs)
  simpa only [conditionalComplexSequence_square] using hg

/-- The exact operator norm belongs to the complex-linear functional. -/
theorem conditionalComplexMellinFunctional_norm (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖conditionalComplexMellinFunctional s hs‖ = Real.sqrt (conditionalMellinDualSquare s) := by
  let r := conditionalMellinDualVector s hs
  have hr : ‖r‖ = Real.sqrt (conditionalMellinDualSquare s) :=
    conditionalMellinDualVector_norm s hs
  apply le_antisymm
  · apply (conditionalComplexMellinFunctional s hs).opNorm_le_bound (Real.sqrt_nonneg _)
    intro g
    change ‖inner ℂ r g‖ ≤ _
    simpa only [hr] using norm_inner_le_norm r g
  · have heval : ‖conditionalComplexMellinFunctional s hs r‖ = ‖r‖ ^ 2 := by
      change ‖inner ℂ r r‖ = _
      rw [inner_self_eq_norm_sq_to_K, norm_pow]
      change ‖(‖r‖ : ℂ)‖ ^ 2 = ‖r‖ ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg r)]
    have hb := (conditionalComplexMellinFunctional s hs).le_opNorm r
    rw [heval, hr] at hb
    by_cases hz : Real.sqrt (conditionalMellinDualSquare s) = 0
    · simpa only [hz] using norm_nonneg (conditionalComplexMellinFunctional s hs)
    · have hp : 0 < Real.sqrt (conditionalMellinDualSquare s) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hp).mp
      simpa only [pow_two, mul_comm] using hb

/-- Coordinatewise inclusion of the already constructed real J into its complexification. -/
def conditionalComplexOfReal (g : ThresholdHilbert) : ConditionalComplexHilbert :=
  ⟨fun k => (g k : ℂ), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] using hilbert_coordinate_square_summable g⟩

theorem conditionalComplexOfReal_norm (g : ThresholdHilbert) :
    ‖conditionalComplexOfReal g‖ = ‖g‖ := by
  have hs : ‖conditionalComplexOfReal g‖ ^ 2 = ‖g‖ ^ 2 := by
    rw [conditionalComplex_norm_sq, hilbert_norm_sq]
    apply tsum_congr
    intro k
    change ‖(g k : ℂ)‖ ^ 2 = (g k) ^ 2
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (conditionalComplexOfReal g), norm_nonneg g]

def conditionalComplexOfRealLinear : ThresholdHilbert →ₗ[ℝ] ConditionalComplexHilbert where
  toFun := conditionalComplexOfReal
  map_add' f g := by
    apply Subtype.ext
    funext k
    simp [conditionalComplexOfReal, lp.coeFn_add, Pi.add_apply]
  map_smul' c g := by
    apply Subtype.ext
    funext k
    simp [conditionalComplexOfReal, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul]

/-- A bundled real-linear isometric inclusion (bound one), with no identification assumption. -/
def conditionalComplexOfRealContinuous : ThresholdHilbert →L[ℝ] ConditionalComplexHilbert :=
  conditionalComplexOfRealLinear.mkContinuous 1 (fun g => by
    change ‖conditionalComplexOfReal g‖ ≤ 1 * ‖g‖
    simpa only [one_mul] using (conditionalComplexOfReal_norm g).le)

theorem conditionalComplexOfReal_sequence (g : ThresholdHilbert) (k : ℕ) :
    conditionalComplexSequence (conditionalComplexOfReal g) (k + 1) =
      (conditionalSequence g (k + 1) : ℂ) := by
  simp [conditionalComplexSequence, conditionalComplexOfReal,
    conditionalSequence, conditionalWeight, Complex.ofReal_div]

/-- Lambda_s on the actual real J model; its scalar field is explicitly real. -/
def conditionalMellinFunctional (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ThresholdHilbert →L[ℝ] ℂ :=
  ((conditionalComplexMellinFunctional s hs).restrictScalars ℝ).comp
    conditionalComplexOfRealContinuous

theorem conditionalMellinFunctional_apply (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (g : ThresholdHilbert) :
    conditionalMellinFunctional s hs g =
      ∑' k : ℕ, mellinSecond s (k + 1) * (conditionalSequence g (k + 1) : ℂ) := by
  change conditionalComplexMellinFunctional s hs (conditionalComplexOfReal g) = _
  rw [conditionalComplexMellinFunctional_apply]
  simp only [conditionalComplexOfReal_sequence]

/-- The real restriction has the valid dual norm upper bound. -/
theorem conditionalMellinFunctional_norm_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖conditionalMellinFunctional s hs‖ ≤ Real.sqrt (conditionalMellinDualSquare s) := by
  apply (conditionalMellinFunctional s hs).opNorm_le_bound (Real.sqrt_nonneg _)
  intro g
  change ‖conditionalComplexMellinFunctional s hs (conditionalComplexOfReal g)‖ ≤ _
  have h := (conditionalComplexMellinFunctional s hs).le_opNorm (conditionalComplexOfReal g)
  simpa only [conditionalComplexMellinFunctional_norm, conditionalComplexOfReal_norm] using h

/-- The bundled functional recovers the exact Mellin value on every actual Cesaro image. -/
theorem conditionalMellinFunctional_cesaroOperator (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (f : ThresholdHilbert) :
    conditionalMellinFunctional s hs (cesaroOperator f) = s * paretoMellin f s := by
  rw [conditionalMellinFunctional_apply]
  simp_rw [conditionalSequence_cesaroOperator, ← mean_ofReal]
  exact cesaro_mellin_pairing_hilbert f s hs

/-- The actual J constant has functional value one. -/
theorem conditionalMellinFunctional_one (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    conditionalMellinFunctional s hs conditionalOne = 1 := by
  rw [conditionalOne, conditionalMellinFunctional_cesaroOperator, paretoMellin_one s hs]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  field_simp [hs0]

/-- The same image identity for the complex-linear functional on embedded real vectors. -/
theorem conditionalComplexMellinFunctional_cesaroOperator (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (f : ThresholdHilbert) :
    conditionalComplexMellinFunctional s hs (conditionalComplexOfReal (cesaroOperator f)) =
      s * paretoMellin f s := by
  change conditionalMellinFunctional s hs (cesaroOperator f) = _
  exact conditionalMellinFunctional_cesaroOperator s hs f

theorem conditionalComplexMellinFunctional_one (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    conditionalComplexMellinFunctional s hs (conditionalComplexOfReal conditionalOne) = 1 := by
  change conditionalMellinFunctional s hs conditionalOne = _
  exact conditionalMellinFunctional_one s hs

end RiemannResearch.Analysis.Cesaro
