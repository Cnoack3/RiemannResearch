import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.IntegratedRamanujanBasis

/-! # The character fibres of the integrated packets of conductors ten and thirty
Source: direct finite Fourier inversion of the physical Möbius residue rows.
All table entries are four times the Fourier coefficients. The quartic entry
uses real and imaginary coordinates; its conjugate supplies the other column.
-/

namespace RiemannResearch.CategoryTheory.ValuationCharacterExamples
open RiemannResearch.RH.Pareto
open scoped BigOperators

private def tenInt (n : ℕ) : ℤ :=
  2 * (((n / 2) % 5 : ℕ) : ℤ) - ((n % 5 : ℕ) : ℤ)

private def thirtyInt (n : ℕ) : ℤ := 3 * tenInt (n / 3) - tenInt n

private theorem tenInt_cast (n : ℕ) : (tenInt n : ℝ) = ramanujanPacket 10 n := by
  change _ = ramanujanPacket (2*5) n
  rw [ramanujanPacket_mul_prime_of_not_dvd 2 5 n (by decide) (by decide) (by decide),
    ramanujanPacket_prime_eq_residue 5 (by decide)]
  simp only [tenInt, dilation, residue, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Nat.cast_ofNat]

private theorem thirtyInt_cast (n : ℕ) : (thirtyInt n : ℝ) = ramanujanPacket 30 n := by
  change _ = ramanujanPacket (3*10) n
  rw [ramanujanPacket_mul_prime_of_not_dvd 3 10 n (by decide) (by decide) (by decide)]
  simp only [thirtyInt, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, tenInt_cast,
    dilation, Nat.cast_ofNat]

/-- Coordinates of four times the coefficients of 1, χ (real and imaginary
parts), η and ηχ². Here χ(2)=i modulo five and η is the sign modulo three. -/
structure Coefficients where
  constant : ℤ
  quarticRe : ℤ
  quarticIm : ℤ
  signThree : ℤ
  signFifteen : ℤ
  deriving DecidableEq

def ten : ℕ → Coefficients
  | 1 => ⟨6, -5, -5, 0, 0⟩
  | 2 => ⟨10, -5, 5, 0, 0⟩
  | 5 => ⟨16, 0, 0, 0, 0⟩
  | _ => ⟨0, 0, 0, 0, 0⟩

def thirty : ℕ → Coefficients
  | 1 => ⟨18, -10, 5, -9, 15⟩
  | 2 => ⟨14, 5, 10, -9, -15⟩
  | 3 => ⟨12, -10, -20, 0, 0⟩
  | 5 => ⟨8, 0, 0, -36, 0⟩
  | 6 => ⟨20, -20, 10, 0, 0⟩
  | 10 => ⟨24, 0, 0, -36, 0⟩
  | 15 => ⟨32, 0, 0, 0, 0⟩
  | _ => ⟨0, 0, 0, 0, 0⟩

/-- Evaluation of the scaled real character synthesis at a unit representative. -/
def Coefficients.evaluate (a : Coefficients) (u : ℕ) : ℤ :=
  let x : ℤ := if u % 5 = 1 then 1 else if u % 5 = 4 then -1 else 0
  let y : ℤ := if u % 5 = 2 then 1 else if u % 5 = 3 then -1 else 0
  let e : ℤ := if u % 3 = 1 then 1 else -1
  a.constant + 2 * (a.quarticRe*x - a.quarticIm*y) + a.signThree*e +
    a.signFifteen*e*(x*x-y*y)

private theorem ten_table :
    ∀ d : Fin 11, d.val ∣ 10 → ∀ u : Fin 10, Nat.Coprime u.val 10 →
      4 * tenInt (d.val * u.val) = (ten d.val).evaluate u.val := by decide

private theorem thirty_table :
    ∀ d : Fin 31, d.val ∣ 30 → ∀ u : Fin 30, Nat.Coprime u.val 30 →
      4 * thirtyInt (d.val * u.val) = (thirty d.val).evaluate u.val := by decide

theorem ten_fibres (d : Fin 11) (hd : d.val ∣ 10) (u : Fin 10)
    (hu : Nat.Coprime u.val 10) :
    4 * ramanujanPacket 10 (d.val*u.val) = ((ten d.val).evaluate u.val : ℝ) := by
  rw [← tenInt_cast]
  exact_mod_cast ten_table d hd u hu

theorem thirty_fibres (d : Fin 31) (hd : d.val ∣ 30) (u : Fin 30)
    (hu : Nat.Coprime u.val 30) :
    4 * ramanujanPacket 30 (d.val*u.val) = ((thirty d.val).evaluate u.val : ℝ) := by
  rw [← thirtyInt_cast]
  exact_mod_cast thirty_table d hd u hu

end RiemannResearch.CategoryTheory.ValuationCharacterExamples
