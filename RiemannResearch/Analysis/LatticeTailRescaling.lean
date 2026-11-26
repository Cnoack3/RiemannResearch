import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Comparison of reciprocal tails on a lattice and on the physical width
scale, retaining an explicit error for replacing the last lattice site by
the upper integration endpoint. -/

namespace RiemannResearch.Analysis.LatticeTailRescaling

theorem one_le_floor_width {a q : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) (hq : 1 ≤ q) :
    1 ≤ ⌊q / a⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ ha).mpr
  norm_num
  linarith

/-- The integer and continuous reciprocal principal terms cancel up to the
position of the width in its lattice cell. -/
theorem abs_sub_le_rescaled {a q d c A B coeff : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1 / 2) (hq : 1 ≤ q)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hcoeff : 0 ≤ coeff)
    (hd : |d - coeff / (a * (⌊q / a⌋₊ : ℝ))| ≤ A / (⌊q / a⌋₊ : ℝ) ^ 2)
    (hc : |c - coeff / q| ≤ B / q ^ 2) :
    |d - c| ≤ (4 * a ^ 2 * A + 2 * coeff * a + B) / q ^ 2 := by
  let n : ℝ := (⌊q / a⌋₊ : ℝ)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hn1 : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast one_le_floor_width ha ha' hq
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hfloor : n ≤ q/a := Nat.floor_le (div_nonneg hq0.le ha.le)
  have hceil : q/a < n+1 := Nat.lt_floor_add_one _
  have han : a*n ≤ q := by simpa only [mul_comm n a] using (le_div_iff₀ ha).mp hfloor
  have hrem : q-a*n ≤ a := by nlinarith only [(div_lt_iff₀ ha).mp hceil]
  have hscale : q ≤ 2*(a*n) := by linarith only [han,hrem,ha',hq]
  have hanpos := mul_pos ha hn
  change |d-coeff / (a*n)| ≤ A / n^2 at hd
  have hdisc : A/n^2 ≤ (4*a^2*A)/q^2 := by
    apply (div_le_div_iff₀ (pow_pos hn _) (pow_pos hq0 _)).mpr
    have hsq := (sq_le_sq₀ hq0.le (by positivity : 0 ≤ 2*(a*n))).mpr hscale
    nlinarith only [mul_le_mul_of_nonneg_left hsq hA]
  have hprincipal : |coeff / (a*n)-coeff / q| ≤ (2*coeff*a)/q^2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (div_le_div_of_nonneg_left hcoeff hanpos han))]
    calc
      coeff / (a*n)-coeff / q = coeff*(q-a*n)/((a*n)*q) := by
        field_simp [ha.ne',hn.ne',hq0.ne']
        <;> ring
      _ ≤ coeff*a/((a*n)*q) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrem hcoeff) (mul_nonneg hanpos.le hq0.le)
      _ ≤ (2*coeff*a)/q^2 := by
        apply (div_le_div_iff₀ (mul_pos hanpos hq0) (pow_pos hq0 _)).mpr
        nlinarith only [mul_le_mul_of_nonneg_right hscale (mul_nonneg (mul_nonneg hcoeff ha.le) hq0.le)]
  have ht := abs_sub_le d (coeff / (a*n)) c
  have hu := abs_sub_le (coeff / (a*n)) (coeff / q) c
  rw [abs_sub_comm (coeff / q) c] at hu
  rw [add_div,add_div]
  linarith only [ht,hu,hd,hdisc,hprincipal,hc]

end RiemannResearch.Analysis.LatticeTailRescaling
