import RiemannResearch.RH.QResidueMeshNorm
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The squarefree trace remainder and ζ(4)

Grouping the reciprocal-square series by its squarefree part gives a
uniform bound for every finite squarefree residue Gram trace. The factor
ζ(2)/ζ(4)-1 is the one in Noack's October 2026 CRT carry note.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeTraceRemainder
open ZetaTwoProbability

def zetaFour : ℝ := ∑' k : ℕ+, 1/(k : ℝ)^4

private theorem four_summable : Summable (fun k : ℕ+ => 1/(k : ℝ)^4) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4:ℕ))).subtype _

theorem zetaFour_pos : 0 < zetaFour :=
  four_summable.tsum_pos (fun _ => by positivity) 1 (by norm_num)

theorem zetaFour_eq_riemannZeta : (zetaFour : ℂ) = riemannZeta 4 := by
  have ha : zetaFour = ∑' n : ℕ, 1/(n : ℝ)^4 := by
    unfold zetaFour
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1/(n : ℝ)^4)]
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4:ℕ))
    simpa using h.tsum_eq_zero_add.symm
  rw [ha, Complex.ofReal_tsum]
  have hz := zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < (4:ℕ))
  norm_num only [Nat.cast_ofNat] at hz
  rw [hz]
  congr 1
  funext n
  push_cast
  rfl

private theorem squarefree_part_unique {d e k l : ℕ} (hd : Squarefree d) (he : Squarefree e)
    (hk : k ≠ 0) (hl : l ≠ 0) (h : k^2*d = l^2*e) : d = e := by
  apply Nat.eq_of_factorization_eq' hd.ne_zero he.ne_zero
  ext p
  have hf := congrArg (fun n : ℕ => n.factorization p) h
  simp only [Nat.factorization_mul (pow_ne_zero 2 hk) hd.ne_zero,
    Nat.factorization_mul (pow_ne_zero 2 hl) he.ne_zero, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hf
  have hd' := hd.natFactorization_le_one p
  have he' := he.natFactorization_le_one p
  omega

theorem mass_le_quotient (s : Finset ℕ) (hs : ∀ d ∈ s, Squarefree d) :
    (∑ d ∈ s, 1/(d : ℝ)^2) ≤ zetaTwo / zetaFour := by
  classical
  let g (x : ↥s × ℕ+) : ℕ := (x.2 : ℕ)^2 * (x.1 : ℕ)
  have hi : Function.Injective g := by
    rintro ⟨d,k⟩ ⟨e,l⟩ hh
    change (k : ℕ)^2*d.val = (l : ℕ)^2*e.val at hh
    have hde := squarefree_part_unique (hs d d.property) (hs e e.property) k.property.ne' l.property.ne' hh
    have hd : d = e := Subtype.ext hde
    subst e
    have hkl : (k : ℕ)^2 = (l : ℕ)^2 := Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (hs d d.property).ne_zero) hh
    have hk : k = l := Subtype.ext (Nat.pow_left_injective (by decide) hkl)
    subst l
    rfl
  let f := fun n : ℕ => 1/(n : ℝ)^2
  have hf : Summable f := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))
  have hinj := tsum_comp_le_tsum_of_inj hf (fun n => by dsimp [f]; positivity) hi
  have hsum := hf.comp_injective hi
  rw [le_div_iff₀ zetaFour_pos, zetaTwo_eq_nat_sum]
  apply le_trans _ hinj
  apply le_of_eq
  rw [hsum.tsum_prod, tsum_fintype, Finset.sum_mul, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro d _
  rw [zetaFour, ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [Function.comp_apply, f, g, Nat.cast_mul, Nat.cast_pow]
  ring

/-- Excluding conductor one subtracts exactly one from the uniform bound. -/
theorem squarefree_trace_defect_upper (s : Finset ℕ) (hs : ∀ d ∈ s, Squarefree d) (h1 : 1 ∉ s) :
    (∑ d ∈ s, QResidueMeshNorm.defect d / (zetaTwo * (d : ℝ)^2)) ≤ zetaTwo / zetaFour - 1 := by
  apply (QResidueMeshNorm.total_defect_bounds s
    (fun d hd => Nat.pos_of_ne_zero (hs d hd).ne_zero)).2.trans
  have hu := mass_le_quotient (insert 1 s) (fun d hd => by
    rcases Finset.mem_insert.mp hd with rfl | hm
    · exact squarefree_one
    · exact hs d hm)
  rw [Finset.sum_insert h1] at hu
  norm_num at hu
  simp only [one_div]
  linarith

end RiemannResearch.RH.QSquarefreeTraceRemainder
