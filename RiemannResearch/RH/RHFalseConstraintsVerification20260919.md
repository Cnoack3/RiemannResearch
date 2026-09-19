# RH-failure constraints: verification record, 2026-09-19

Base commit: `28e77bcc716333507adbefcd3f4f1d4dca4f2fef`.

Source: user-provided RH-equivalence audit and first-coordinate/tail-capacity continuation.
The new development derives consequences from the single explicit hypothesis
`¬ RiemannHypothesis`; it does not use `PositiveResidueDensityFromRH`.

## Established implications and geometry

- `RH/CanonicalTailCapacityGeometry.lean`: point projection orthogonality to
  all integer dilations m≥2; exact finite capacity limit under a nonzero point
  residual; strong convergence of finite dual minimizers; canonical
  Pythagorean minimality; exact canonical Mellin interpolation at every
  right-half-plane zero.
- `RH/RHFalseTailConstraints.lean`: one canonical reciprocal certificate under
  ¬RH, primitive square summability and failure of absolute summability,
  cofinal power/logarithmic partial-sum excursions, both signs arbitrarily
  far out, finite total capacity gain, positive constant-residual first
  coordinate, and one common actual zero with a genuine pole and the
  phase-sensitive unrestricted head-energy lower bound.
- `RH/MobiusResidualInfiniteDefects.lean`: biorthogonal reconstruction
  uniqueness, exclusion of ordinary ordered Hilbert convergence of the
  residual-defect series, exclusion of its unconditional summability and
  absolute norm summability, and arbitrarily large wrong stabilized
  coefficients under ¬RH.

## Verification

Combined coherent source check: `job_v2wUgORiFOvdTZffFYwtP6qJCBezs9Oq`.
Exit code 0; verified true; elapsed 6.037 seconds; no output truncation.
Source SHA-256:
`10f9870204d60ca6e55ce582894d092842d1af12ac353a5dbefc88997a945979`.

All 18 audited endpoints reported only `propext`, `Classical.choice`,
and `Quot.sound`. No project-local axioms, unfinished proofs or unsafe
declarations were persisted. Checkpoint validates the separate modules and
their actual imports before publication.

## Open boundary and written-only additions

No contradiction or unconditional RH theorem is claimed. Canonical primitive
absolute summability, actual screened-gain divergence, a cofinal subpower
head-energy upper bound, or convergence of the actual coefficient-defect
reconstruction remains an additional arithmetic input.

The accompanying mathematical report derives the comparison
sum |c∞,d+μ(d)|/sqrt(d)=infinity under ¬RH from the checked norm-weighted
divergence. The explicit residue-norm estimate, simultaneous zero-derivative
Gram calculation, and complex Mellin-kernel compatibility model are written
arguments, not separate Lean declarations in this change.

In particular, minimum norm plus all integer-dilation orthogonalities
does not by itself imply primitive l1: an explicit closed Mellin-kernel
model has those properties with primitive proportional to n^(-conj(s)),
for 1/2<Re(s)<1. The actual residue subspace requires further arithmetic.
