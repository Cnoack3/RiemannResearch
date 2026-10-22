import RiemannResearch.RH.DyadicFiniteBoundaryCoordinates

/-!
# Exact support of the canonical boundary coefficients

Source: user-provided `DyadicRegularizedVerificationContinuation20260910 (2).md`,
Appendix §§1–2, September 10, 2026. The support is proved directly by dyadic
refinement on integer grids, without introducing a new abstract tent family.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Within a normalized dyadic grid, a nonzero actual boundary coefficient
forces strict membership in the corresponding open tent interval. -/
theorem dyadicBoundaryCoordinate_step_support
    (L l : ℕ) (hL : 0 < L) (hlL : L ≤ l) (hl2L : l < 2*L)
    (d m : ℕ) (hm : 0 < m)
    (hlo : 2^d*L ≤ m) (hhi : m ≤ 2^d*(2*L))
    (hne : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) (l-1) ≠ 0) :
    2^d*l < m ∧ m < 2^d*(l+1) := by
  have hl : 0 < l := lt_of_lt_of_le hL hlL
  have hlsub : l-1+1 = l := by omega
  induction d generalizing m with
  | zero =>
    have hz : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) (l-1) = 0 := by
      apply dyadicBoundaryCoordinate_step_zero
      norm_num at hhi
      omega
    exact False.elim (hne hz)
  | succ d ih =>
    have hp : 0 < (2 : ℕ)^d := by positivity
    have hm2 : 2 ≤ m := by
      rw [pow_succ'] at hlo
      nlinarith
    have hu : 0 < m/2 := Nat.div_pos_iff.mpr ⟨by norm_num, hm2⟩
    have hlow : 2*(2^d*L) ≤ m := by
      simpa only [pow_succ', Nat.mul_assoc] using hlo
    have hhigh : m ≤ 2*(2^d*(2*L)) := by
      simpa only [pow_succ', Nat.mul_assoc] using hhi
    have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    have hu_low : 2^d*L ≤ m/2 := by omega
    have hu_high : m/2 ≤ 2^d*(2*L) := by omega
    by_cases he : m % 2 = 0
    · have hmform : m = 2*(m/2) := by omega
      have hv : dyadicProjectedStep m hm = dyadicProjectedStep (m/2) hu := by
        simpa only [← hmform] using dyadicProjectedStep_double (m/2) hu
      rw [hv] at hne
      have hi := ih (m/2) hu hu_low hu_high hne
      rw [pow_succ']
      constructor <;> nlinarith [hi.1, hi.2]
    · have hmform : m = 2*(m/2)+1 := by omega
      have hup_high : m/2+1 ≤ 2^d*(2*L) := by omega
      have hv : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) (l-1) =
          (if l = m/2 then 1 else 0) + (1/2 : ℝ) *
            (dyadicBoundaryCoordinate (dyadicProjectedStep (m/2) hu) (l-1) +
              dyadicBoundaryCoordinate
                (dyadicProjectedStep (m/2+1) (by positivity)) (l-1)) := by
        simpa only [← hmform, hlsub] using
          dyadicBoundaryCoordinate_step_odd (m/2) hu (l-1)
      by_cases hroot : l = m/2
      · have hpow : (2 : ℕ)^d = 1 := by
          by_contra h
          have hp2 : 2 ≤ (2 : ℕ)^d := by omega
          nlinarith
        rw [pow_succ', hpow]
        constructor <;> nlinarith
      · have hparents :
            dyadicBoundaryCoordinate (dyadicProjectedStep (m/2) hu) (l-1) ≠ 0 ∨
              dyadicBoundaryCoordinate
                (dyadicProjectedStep (m/2+1) (by positivity)) (l-1) ≠ 0 := by
          by_contra h
          push_neg at h
          apply hne
          rw [hv, if_neg hroot, h.1, h.2]
          ring
        rcases hparents with ha | hb
        · have hi := ih (m/2) hu hu_low hu_high ha
          rw [pow_succ']
          constructor <;> nlinarith [hi.1, hi.2]
        · have hi := ih (m/2+1) (by positivity) (by omega) hup_high hb
          rw [pow_succ']
          constructor <;> nlinarith [hi.1, hi.2]

/-- Two nonzero coordinates at one boundary force the two grid points to be
strictly less than one boundary interval apart. -/
theorem dyadicBoundaryCoordinate_common_support_separation
    (L l : ℕ) (hL : 0 < L) (hlL : L ≤ l) (hl2L : l < 2*L)
    (d m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmlo : 2^d*L ≤ m) (hmhi : m ≤ 2^d*(2*L))
    (hnlo : 2^d*L ≤ n) (hnhi : n ≤ 2^d*(2*L))
    (hmne : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) (l-1) ≠ 0)
    (hnne : dyadicBoundaryCoordinate (dyadicProjectedStep n hn) (l-1) ≠ 0) :
    |(m : ℤ)-(n : ℤ)| < (2 : ℤ)^d := by
  have ha := dyadicBoundaryCoordinate_step_support L l hL hlL hl2L d m hm hmlo hmhi hmne
  have hb := dyadicBoundaryCoordinate_step_support L l hL hlL hl2L d n hn hnlo hnhi hnne
  have hap : (2 : ℤ)^d*(l : ℤ) < m ∧ (m : ℤ) < (2 : ℤ)^d*(l+1) := by
    exact_mod_cast ha
  have hbp : (2 : ℤ)^d*(l : ℤ) < n ∧ (n : ℤ) < (2 : ℤ)^d*(l+1) := by
    exact_mod_cast hb
  rw [abs_lt]
  constructor <;> nlinarith [hap.1, hap.2, hbp.1, hbp.2]

/-- The geometric common-support estimate allows different denominator
depths; it therefore applies directly to normalized integer mantissas. -/
theorem dyadicBoundaryCoordinate_common_support_normalized_separation
    (L l : ℕ) (hL : 0 < L) (hlL : L ≤ l) (hl2L : l < 2*L)
    (d e m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmlo : 2^d*L ≤ m) (hmhi : m ≤ 2^d*(2*L))
    (hnlo : 2^e*L ≤ n) (hnhi : n ≤ 2^e*(2*L))
    (hmne : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) (l-1) ≠ 0)
    (hnne : dyadicBoundaryCoordinate (dyadicProjectedStep n hn) (l-1) ≠ 0) :
    |(m : ℝ)/((2 : ℝ)^d*L) - (n : ℝ)/((2 : ℝ)^e*L)| < 1/(L : ℝ) := by
  have ha := dyadicBoundaryCoordinate_step_support L l hL hlL hl2L d m hm hmlo hmhi hmne
  have hb := dyadicBoundaryCoordinate_step_support L l hL hlL hl2L e n hn hnlo hnhi hnne
  have hap : (2 : ℝ)^d*(l : ℝ) < m ∧ (m : ℝ) < (2 : ℝ)^d*(l+1) := by
    exact_mod_cast ha
  have hbp : (2 : ℝ)^e*(l : ℝ) < n ∧ (n : ℝ) < (2 : ℝ)^e*(l+1) := by
    exact_mod_cast hb
  have hpd : 0 < (2 : ℝ)^d := by positivity
  have hpe : 0 < (2 : ℝ)^e := by positivity
  have hma : (l : ℝ) < (m : ℝ)/(2 : ℝ)^d :=
    (lt_div_iff₀ hpd).mpr (by nlinarith [hap.1])
  have hmb : (m : ℝ)/(2 : ℝ)^d < l+1 :=
    (div_lt_iff₀ hpd).mpr (by nlinarith [hap.2])
  have hna : (l : ℝ) < (n : ℝ)/(2 : ℝ)^e :=
    (lt_div_iff₀ hpe).mpr (by nlinarith [hbp.1])
  have hnb : (n : ℝ)/(2 : ℝ)^e < l+1 :=
    (div_lt_iff₀ hpe).mpr (by nlinarith [hbp.2])
  have hnorm : |(m : ℝ)/(2 : ℝ)^d - (n : ℝ)/(2 : ℝ)^e| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  rw [← div_div, ← div_div (n : ℝ), ← sub_div, abs_div, abs_of_pos hLR]
  exact (div_lt_div_iff_of_pos_right hLR).mpr hnorm

end
end RiemannResearch.RH.Pareto
