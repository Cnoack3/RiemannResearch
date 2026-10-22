import RiemannResearch.RH.ParetoShapeMellinEnergy

/-!
# The exact critical-line threshold for Pareto shape

The normalized Pareto cell mass decreases with the shape parameter. This
comparison proves that the critical Mellin certificate has finite energy
exactly below shape one, including after every finite truncation. No zeta-zero
or Riemann-hypothesis assumption enters the energy statements.
-/

noncomputable section
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ShapeCapacity

/-- Normalizing the Pareto cell mass by the shape gives a decreasing function
of the shape on every cell starting at or above one. -/
theorem shapeCellWeight_div_antitone (a : ℝ) (ha : 1 ≤ a) :
    AntitoneOn (fun α => shapeCellWeight α a / α) (Set.Ioi 0) := by
  intro α hα β hβ hαβ
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  change shapeCellWeight β a / β ≤ shapeCellWeight α a / α
  rw [← shapeCellWeight_integral β a hβ ha0,
    ← shapeCellWeight_integral α a hα ha0]
  have hint (r : ℝ) :
      IntervalIntegrable (fun x : ℝ => x ^ r) volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [uIcc_of_le (by linarith)] at hx
    exact (ha0.trans_le hx.1).ne'
  apply intervalIntegral.integral_mono_on (by linarith) (hint _) (hint _)
  intro x hx
  exact Real.rpow_le_rpow_of_exponent_le (ha.trans hx.1) (by linarith)

/-- Higher Pareto shapes have larger dual cell energy after multiplication
by the shape. This applies to every complex Mellin parameter. -/
theorem shapeMellinCellEnergy_mul_mono (α β a : ℝ) (s : ℂ)
    (hα : 0 < α) (hαβ : α ≤ β) (ha : 1 ≤ a) :
    α * shapeMellinCellEnergy α s a ≤
      β * shapeMellinCellEnergy β s a := by
  have hβ : 0 < β := hα.trans_le hαβ
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hwα := shapeCellWeight_pos α a hα ha0
  have hwβ := shapeCellWeight_pos β a hβ ha0
  have hc := shapeCellWeight_div_antitone a ha hα hβ hαβ
  have hc' : shapeCellWeight β a * α ≤ shapeCellWeight α a * β :=
    (div_le_div_iff₀ hβ hα).mp hc
  unfold shapeMellinCellEnergy
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_div_iff₀ hwα hwβ).2
  nlinarith only [mul_le_mul_of_nonneg_left hc'
    (sq_nonneg ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖)]

/-- Finite Mellin energy at a larger shape implies finite energy at every
smaller positive shape. -/
theorem shapeMellinEnergy_summable_of_le (α β a : ℝ) (s : ℂ)
    (hα : 0 < α) (hαβ : α ≤ β) (ha : 1 ≤ a)
    (hs : Summable (fun n : ℕ => shapeMellinCellEnergy β s ((n : ℝ) + a))) :
    Summable (fun n : ℕ => shapeMellinCellEnergy α s ((n : ℝ) + a)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  apply Summable.of_nonneg_of_le
    (fun n => shapeMellinCellEnergy_nonneg α s _ hα (by positivity))
    (fun n => ?_)
    ((hs.mul_left β).div_const α)
  apply (le_div_iff₀ hα).2
  simpa only [mul_comm] using
    shapeMellinCellEnergy_mul_mono α β ((n : ℝ) + a) s hα hαβ
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)

/-- Every shape at or above one has divergent critical-line energy. -/
theorem criticalShapeMellinEnergy_not_summable_of_one_le (α t : ℝ)
    (hα : 1 ≤ α) :
    ¬ Summable (fun n : ℕ =>
      shapeMellinCellEnergy α (MellinFrequency.criticalPoint t) ((n : ℝ) + 1)) := by
  intro hs
  exact criticalShapeMellinEnergy_not_summable t
    (shapeMellinEnergy_summable_of_le 1 α 1 (MellinFrequency.criticalPoint t)
      (by norm_num) hα (by norm_num) hs)

/-- Exact threshold: the actual critical-line Mellin cell energies are
summable precisely for the positive Pareto shapes below one. -/
theorem criticalShapeMellinEnergy_summable_iff (α t : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ =>
      shapeMellinCellEnergy α (MellinFrequency.criticalPoint t) ((n : ℝ) + 1)) ↔
      α < 1 := by
  constructor
  · intro hs
    by_contra h
    exact criticalShapeMellinEnergy_not_summable_of_one_le α t (le_of_not_gt h) hs
  · intro h
    apply shapeMellinEnergy_summable α (MellinFrequency.criticalPoint t) 1 hα
    · simpa only [MellinFrequency.criticalPoint_re,
        show 2 * (1 / 2 : ℝ) = 1 by norm_num] using h
    · norm_num

/-- A finite deletion cannot change the sharp threshold. -/
theorem criticalShapeMellinShiftEnergy_summable_iff (α t : ℝ) (hα : 0 < α)
    (k : ℕ) :
    Summable (fun n : ℕ =>
      shapeMellinCellEnergy α (MellinFrequency.criticalPoint t)
        (((n + k : ℕ) : ℝ) + 1)) ↔ α < 1 := by
  exact (summable_nat_add_iff k).trans (criticalShapeMellinEnergy_summable_iff α t hα)

/-- Division by the nonzero critical parameter changes no summability
threshold, for any finite starting cutoff. -/
theorem criticalNormalizedShiftEnergy_summable_iff (α t : ℝ) (hα : 0 < α)
    (k : ℕ) :
    Summable (fun n : ℕ =>
      ‖mellinCellCertificate (MellinFrequency.criticalPoint t)
        (((n + k : ℕ) : ℝ) + 1)‖ ^ 2 /
        shapeCellWeight α (((n + k : ℕ) : ℝ) + 1)) ↔ α < 1 := by
  simp_rw [normalized_cell_energy_eq]
  rw [summable_div_const_iff
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (MellinFrequency.criticalPoint_ne_zero t)))]
  exact criticalShapeMellinShiftEnergy_summable_iff α t hα k

end RiemannResearch.RH.Pareto.ShapeCapacity

/-!
# Exact Mellin-certificate threshold at every positive real part

Reverse triangle and a positive unit-cell mass lower bound show that the
boundary shape `α = 2 Re(s)` has harmonic divergent energy. The normalized
cell-mass comparison propagates this to all larger shapes.
-/

noncomputable section
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ShapeCapacity

/-- Lower derivative bound on a decreasing Pareto density. -/
theorem shapeCellWeight_lower (β a : ℝ) (hβ : 0 < β) (ha : 0 < a) :
    β * (a + 1) ^ (-β - 1) ≤ shapeCellWeight β a := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-β - 1)) volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [uIcc_of_le (by linarith)] at hx
    exact (ha.trans_le hx.1).ne'
  have hcompare : (∫ x in a..a + 1, (a + 1) ^ (-β - 1)) ≤
      ∫ x in a..a + 1, x ^ (-β - 1) := by
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos (ha.trans_le hx.1) hx.2 (by linarith)
  rw [shapeCellWeight_integral β a hβ ha] at hcompare
  have hcompare' : (a + 1) ^ (-β - 1) ≤ shapeCellWeight β a / β := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left,
      one_mul] using hcompare
  have h := (le_div_iff₀ hβ).mp hcompare'
  simpa only [mul_comm] using h

/-- Reverse triangle provides a lower bound independent of the imaginary
part. At the boundary shape the denominator factors exactly. -/
theorem shapeMellinCellEnergy_boundary_lower_ratio (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    shapeCellWeight s.re a / (2 * a ^ (-s.re)) ≤
      shapeMellinCellEnergy (2 * s.re) s a := by
  let A : ℝ := a ^ (-s.re)
  let B : ℝ := (a + 1) ^ (-s.re)
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hB : 0 < B := Real.rpow_pos_of_pos (by linarith) _
  have hdiff : 0 < A - B := shapeCellWeight_pos s.re a hs ha
  have hnorm : A - B ≤ ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ := by
    have hz := Complex.norm_cpow_eq_rpow_re_of_pos ha (-s)
    have hw := Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < a + 1 by linarith) (-s)
    simpa only [hz, hw, Complex.neg_re] using
      norm_sub_norm_le ((a : ℂ) ^ (-s)) (((a + 1 : ℝ) : ℂ) ^ (-s))
  have hsq : (A - B) ^ 2 ≤
      ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ^ 2 := by
    nlinarith [norm_nonneg ((a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))]
  have hfactor : shapeCellWeight (2 * s.re) a = (A - B) * (A + B) := by
    have hpa : a ^ (-(2 * s.re)) = A ^ 2 := by
      dsimp only [A]
      rw [sq, ← Real.rpow_add ha]
      congr 1
      ring
    have hpb : (a + 1) ^ (-(2 * s.re)) = B ^ 2 := by
      dsimp only [B]
      rw [sq, ← Real.rpow_add (show 0 < a + 1 by linarith)]
      congr 1
      ring
    rw [shapeCellWeight, hpa, hpb]
    ring
  have hweight : 0 < shapeCellWeight (2 * s.re) a :=
    shapeCellWeight_pos _ a (by linarith) ha
  unfold shapeMellinCellEnergy
  change (A - B) / (2 * A) ≤ _
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * A) hweight).2
  rw [hfactor]
  calc
    (A - B) * ((A - B) * (A + B)) = (A - B) ^ 2 * (A + B) := by ring
    _ ≤ (A - B) ^ 2 * (2 * A) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hsq (by positivity)

/-- Every positive real part has a uniform harmonic boundary lower bound.
The constant is explicit and positive. -/
theorem shapeMellinCellEnergy_boundary_lower (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 1 ≤ a) :
    (s.re * (2 : ℝ) ^ (-s.re) / 2) / (a + 1) ≤
      shapeMellinCellEnergy (2 * s.re) s a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hay : 0 < a + 1 := by linarith
  have hpow : (2 : ℝ) ^ (-s.re) * a ^ (-s.re) ≤ (a + 1) ^ (-s.re) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha0.le]
    exact Real.rpow_le_rpow_of_nonpos hay (by linarith) (by linarith)
  have hsplit : (a + 1) ^ (-s.re - 1) = (a + 1) ^ (-s.re) / (a + 1) := by
    simp only [sub_eq_add_neg, Real.rpow_add hay, Real.rpow_neg_one, div_eq_mul_inv]
  have hpow' : (2 : ℝ) ^ (-s.re) * a ^ (-s.re) / (a + 1) ≤
      (a + 1) ^ (-s.re - 1) := by
    rw [hsplit]
    exact div_le_div_of_nonneg_right hpow hay.le
  have hmass := (mul_le_mul_of_nonneg_left hpow' hs.le).trans
    (shapeCellWeight_lower s.re a hs ha0)
  have hmass' : s.re * ((2 : ℝ) ^ (-s.re) * a ^ (-s.re)) ≤
      shapeCellWeight s.re a * (a + 1) := by
    apply (div_le_iff₀ hay).mp
    simpa only [mul_div_assoc] using hmass
  have hratio : (s.re * (2 : ℝ) ^ (-s.re) / 2) / (a + 1) ≤
      shapeCellWeight s.re a / (2 * a ^ (-s.re)) := by
    apply (div_le_div_iff₀ hay (by positivity : 0 < 2 * a ^ (-s.re))).2
    nlinarith only [hmass']
  exact hratio.trans (shapeMellinCellEnergy_boundary_lower_ratio s a hs ha0)

theorem shapeMellinEnergy_boundary_not_summable (s : ℂ) (hs : 0 < s.re) :
    ¬ Summable (fun n : ℕ => shapeMellinCellEnergy (2 * s.re) s ((n : ℝ) + 1)) := by
  intro h
  let c : ℝ := s.re * (2 : ℝ) ^ (-s.re) / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ (h.div_const c)
    intro n
    have hl := shapeMellinCellEnergy_boundary_lower s ((n : ℝ) + 1) hs
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    have hl' : c / ((n : ℝ) + 2) ≤
        shapeMellinCellEnergy (2 * s.re) s ((n : ℝ) + 1) := by
      simpa only [c, add_assoc, one_add_one_eq_two] using hl
    apply (le_div_iff₀ hc).2
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hl'
  have hh' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (1 : ℝ)) :=
    hh.congr (fun n => by rw [Real.rpow_one, abs_of_pos (by positivity)])
  have hfalse := (Real.summable_one_div_nat_add_rpow 2 1).1 hh'
  linarith

/-- The complete sharp threshold for every parameter in the positive
half-plane. No zeta-zero hypothesis is used. -/
theorem shapeMellinEnergy_summable_iff (α : ℝ) (s : ℂ)
    (hα : 0 < α) (hs : 0 < s.re) :
    Summable (fun n : ℕ => shapeMellinCellEnergy α s ((n : ℝ) + 1)) ↔
      α < 2 * s.re := by
  constructor
  · intro h
    by_contra hn
    exact shapeMellinEnergy_boundary_not_summable s hs
      (shapeMellinEnergy_summable_of_le (2 * s.re) α 1 s
        (by linarith) (le_of_not_gt hn) (by norm_num) h)
  · intro h
    exact shapeMellinEnergy_summable α s 1 hα h (by norm_num)

theorem shapeMellinShiftEnergy_summable_iff (α : ℝ) (s : ℂ)
    (hα : 0 < α) (hs : 0 < s.re) (k : ℕ) :
    Summable (fun n : ℕ =>
      shapeMellinCellEnergy α s (((n + k : ℕ) : ℝ) + 1)) ↔ α < 2 * s.re := by
  exact (summable_nat_add_iff k).trans (shapeMellinEnergy_summable_iff α s hα hs)

theorem normalizedShapeMellinShiftEnergy_summable_iff (α : ℝ) (s : ℂ)
    (hα : 0 < α) (hs : 0 < s.re) (k : ℕ) :
    Summable (fun n : ℕ =>
      ‖mellinCellCertificate s (((n + k : ℕ) : ℝ) + 1)‖ ^ 2 /
        shapeCellWeight α (((n + k : ℕ) : ℝ) + 1)) ↔ α < 2 * s.re := by
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  simp_rw [normalized_cell_energy_eq]
  rw [summable_div_const_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hs0))]
  exact shapeMellinShiftEnergy_summable_iff α s hα hs k

end RiemannResearch.RH.Pareto.ShapeCapacity

/-!
# Exact order and comparability of Pareto shape weights

Different positive Pareto shapes are not uniformly comparable. A one-sided
comparison holds exactly in the order dictated by the tail exponent.
Necessity follows from the exact Mellin-energy summability threshold, with
an explicit positive real Mellin parameter between the two thresholds.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ShapeCapacity

/-- An upper comparison of physical weights reverses the comparison of
the actual Mellin dual energies. -/
theorem shapeMellinEnergy_summable_of_weight_le (α β C : ℝ) (s : ℂ)
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ n : ℕ,
      shapeCellWeight α ((n : ℝ) + 1) ≤ C * shapeCellWeight β ((n : ℝ) + 1))
    (hs : Summable (fun n : ℕ => shapeMellinCellEnergy α s ((n : ℝ) + 1))) :
    Summable (fun n : ℕ => shapeMellinCellEnergy β s ((n : ℝ) + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => shapeMellinCellEnergy_nonneg β s _ hβ (by positivity))
    (fun n => ?_)
    (hs.mul_left C)
  have hwα := shapeCellWeight_pos α ((n : ℝ) + 1) hα (by positivity)
  have hwβ := shapeCellWeight_pos β ((n : ℝ) + 1) hβ (by positivity)
  unfold shapeMellinCellEnergy
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hwβ hwα).2
  have h := mul_le_mul_of_nonneg_left (hw n)
    (sq_nonneg ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
      (((n : ℝ) + 1 + 1 : ℝ) : ℂ) ^ (-s)‖)
  nlinarith only [h]

/-- The exact one-sided domination order of positive Pareto shapes. -/
theorem shapeCellWeight_domination_iff (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      shapeCellWeight α ((n : ℝ) + 1) ≤ C * shapeCellWeight β ((n : ℝ) + 1)) ↔
      β ≤ α := by
  constructor
  · rintro ⟨C, _hC, hw⟩
    by_contra horder
    have hlt : α < β := lt_of_not_ge horder
    let s : ℂ := (((α + β) / 4 : ℝ) : ℂ)
    have hsre : s.re = (α + β) / 4 := by simp only [s, Complex.ofReal_re]
    have hspos : 0 < s.re := by rw [hsre]; positivity
    have hleft : α < 2 * s.re := by rw [hsre]; linarith
    have hright : 2 * s.re < β := by rw [hsre]; linarith
    have hsα : Summable (fun n : ℕ => shapeMellinCellEnergy α s ((n : ℝ) + 1)) :=
      (shapeMellinEnergy_summable_iff α s hα hspos).2 hleft
    have hsβ := shapeMellinEnergy_summable_of_weight_le α β C s hα hβ hw hsα
    have hbad := (shapeMellinEnergy_summable_iff β s hβ hspos).1 hsβ
    linarith
  · intro horder
    refine ⟨α / β, div_pos hα hβ, ?_⟩
    intro n
    have hn : 1 ≤ (n : ℝ) + 1 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hw := shapeCellWeight_div_antitone ((n : ℝ) + 1) hn hβ hα horder
    have hw' := (div_le_div_iff₀ hα hβ).mp hw
    calc
      shapeCellWeight α ((n : ℝ) + 1) ≤
          (shapeCellWeight β ((n : ℝ) + 1) * α) / β :=
        (le_div_iff₀ hβ).2 hw'
      _ = (α / β) * shapeCellWeight β ((n : ℝ) + 1) := by ring

/-- Two positive Pareto shapes have global two-sided weight comparison
if and only if their exponents agree. In particular the equivalence with
Pareto(1) cannot be transferred merely by changing the shape. -/
theorem shapeCellWeight_comparable_iff (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      c * shapeCellWeight β ((n : ℝ) + 1) ≤ shapeCellWeight α ((n : ℝ) + 1) ∧
      shapeCellWeight α ((n : ℝ) + 1) ≤ C * shapeCellWeight β ((n : ℝ) + 1)) ↔
      α = β := by
  constructor
  · rintro ⟨c, C, hc, hC, hw⟩
    have hβα : β ≤ α := (shapeCellWeight_domination_iff α β hα hβ).1
      ⟨C, hC, fun n => (hw n).2⟩
    have hαβ : α ≤ β := (shapeCellWeight_domination_iff β α hβ hα).1 (by
      refine ⟨1 / c, one_div_pos.mpr hc, ?_⟩
      intro n
      calc
        shapeCellWeight β ((n : ℝ) + 1) ≤
            shapeCellWeight α ((n : ℝ) + 1) / c := by
          apply (le_div_iff₀ hc).2
          simpa only [mul_comm] using (hw n).1
        _ = (1 / c) * shapeCellWeight α ((n : ℝ) + 1) := by ring)
    exact le_antisymm hαβ hβα
  · intro h
    subst β
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro n
    simp

end RiemannResearch.RH.Pareto.ShapeCapacity
