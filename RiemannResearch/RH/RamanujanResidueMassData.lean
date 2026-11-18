import Mathlib.Tactic

/-!
# Integer head certificate for the conductor-124 Pareto trial

The signed coefficients have the common denominator one million. Each
finite contribution is rounded upwards in units of one trillionth.
-/

open scoped BigOperators
namespace RiemannResearch.RH.RamanujanResidueMass.Certificate

def rows : List (ℕ × ℤ) :=
  [(2, 472895), (3, 313231), (4, 22472), (5, 165642), (6, -112991),
    (7, 106482), (8, 1310), (9, 1517), (10, -57268), (11, 55202),
    (12, -1431), (13, 42681), (14, -34845), (15, -36083), (17, 30088),
    (18, 345), (19, 23812), (21, -23234), (22, -15607), (23, 16211),
    (26, -12870), (28, -160), (29, 9799), (30, 14522), (31, 9684),
    (33, -9134), (34, -9653), (35, -9111), (37, 6632), (38, -6336),
    (39, -7087), (41, 5981), (42, 7805), (43, 4802), (46, -1213),
    (47, 1717), (51, -3616), (53, 2067), (55, -3205), (57, -3402),
    (58, -471), (59, 304), (61, 583), (66, 117), (67, 1696),
    (70, 1001), (71, 1791), (73, 96), (79, 1248), (85, -1009),
    (86, -1032), (87, -704), (91, -518), (92, -1819), (93, -1851),
    (97, 243), (101, 1350), (102, 380), (103, 1316), (105, 1179),
    (107, 626), (109, 692), (119, -736), (123, -961), (124, -175)]

def signal : List (ℕ × ℤ) → ℕ → ℤ
  | [], _ => 0
  | (d,z)::s, k => z * ((k%d : ℕ) : ℤ) + signal s k

def difference (k : ℕ) : ℤ := 1000000 - signal rows k

/-- One outward-rounded upper bound in units of 10⁻¹² at physical site k+1. -/
def headUnit (k : ℕ) : ℕ :=
  (difference (k+1)).natAbs^2 / ((k+1)*(k+2)) + 1

def block (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 128, headUnit (j*128+i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Reduce the 256 blocks of 128 positive sites using integer arithmetic in the kernel.
theorem head_units_total :
    (∑ j ∈ Finset.range 256, block j) = 10810291372 := by decide +kernel

end RiemannResearch.RH.RamanujanResidueMass.Certificate
