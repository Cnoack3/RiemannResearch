# Lean continuation: signed primitives, sieve boundaries, and the RH endpoint

Source: the continuation handoff
RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md,
Sections 24–31. This record concerns the new formalization, not a claim
of mathematical novelty. The earlier general summable-tail rigidity
theorem is reused explicitly.

## Conclusion

The central regularity, finite-sieve, divergent-energy, and joint-correction
results are formalized. The two RH implications below are **conditional
research reductions**. No provider discharges their substantive premises,
and no unconditional RH theorem is added.

## Established statements and their scope

All paths below are relative to RiemannResearch/.

| Handoff claim | Lean module and principal declarations | Exact coverage |
|---|---|---|
| Automatic primitive regularity, §25 | Analysis/DiscreteTailHardy; RH/ParetoSignedTailRegularity; RH/ParetoPrimitiveRegularity | Actual weighted-H membership implies primitive ℓ², the constant-four sum bound, \(nA_n^2\le E_{\ge n}\), and \(\sqrt n A_n\to0\). The exact difference-energy identity was already available. |
| Certificate exclusion, §26 | RH/ResidueTailCertificateRegularity: tailCertificate_not_summable_signedTail | An actual reciprocal-source tail certificate cannot have an absolutely summable primitive. Uses existing general ParetoSummableTailRigidity. |
| Strictness of the improved criterion | RH/ParetoOscillatoryRegularityGap: exists_tail_summable_primitive_not_firstMoment | The actual alternating example with exponent α=0 has summable signed primitives and divergent absolute first moment. |
| Automatic ℓ² does not imply ℓ¹ | RH/ParetoOscillatoryRegularityGap: constantOne_square_summable, constantOne_signedTail, constantOne_not_summable_signedTail | The sequence h(k)=1 has finite Pareto energy and primitive 1/n. This is a general regularity counterexample, not a tail certificate. |
| Additive cancellation, (26.7)–(26.8) | RH/ResidueTailAdditiveCancellation; Analysis/LogPowerSummability | The actual condition \(\sum |Z(n)|/n^2<\infty\) excludes a certificate. Eventual power saving and logarithmic saving with positive exponent imply this condition. The logarithmic majorant is proved by Cauchy condensation. |
| Finite signed sieve boundary, §27 | RH/ParetoFiniteSieveBoundary; RH/ParetoMobiusSieveBoundary | Finite Abel identity, residue-mask identity, full finite coprime Möbius identity, and fixed-test boundary decay. No infinite sieve interchange is assumed. |
| Full signed functional norm, (27.3)–(27.7) | RH/ParetoSieveBoundaryNorm; RH/ParetoSieveBoundaryGrowth | Actual representing Hilbert kernel, complete signed square, sharpness in the ambient Hilbert space, exact tail Cauchy–Schwarz bound, and \(\mathfrak B\ge c_Y^2Y/128\) for every integer Y≥8 with cutoff floor(Y/2). Hence the functional norms diverge. |
| Prime-product estimates | Analysis/FinitePrimeProductBounds | \(c_Y\to0\), \((4/15)^3\le c_Y^3(2Y+1)\), and \(Yc_Y^2\to\infty\), without an unresolved asymptotic premise. |
| Actual prime-sieve candidate, §28 | RH/PrimeSievePointEnergy | Finite legality, exact head, normalization, fixed-coordinate and actual coefficient limits, full-tail summability at every cutoff, exact retained-coordinate energy bound, and unconditional full-tail energy divergence. |
| Joint screened correction, §29 | RH/TailCapacityJointCorrections | Actual old zero-head space and optimizer; full signed covariance; normal equations including dependent trial families; attained optimal energy; \(0\le\Lambda<\epsilon\); exact source/defect pairing; capacity-gain lower bound and telescope. |
| Canonical endpoint, §31 | RH/TailCertificateCancellationEndpoint | CanonicalTailSummability is equivalent to vanishing of the canonical point residual, and implies RH. Actual additive cancellation is a sufficient input. No such input is proved. |

The sieve is indexed by divisors of Y! in Lean. Möbius coefficients discard
repeated factors, and the reciprocal mass is formally identified with the
product over all primes ≤Y. Thus the physical candidate and its energy are
the ones in the handoff, rather than a different sequence with similar
finite coordinates.

The joint optimization uses attained finite-dimensional normal equations.
This gives the same optimum in singular cases as the manuscript's
Moore–Penrose expression; a separately named Moore–Penrose matrix is not
constructed. Lean stage n contains moduli 2 through n+1.

## Remaining formalization boundaries

The formal Abel tail formula is proved under the additive-cancellation
hypothesis needed for certificate exclusion. The standalone version for
every Hilbert sequence in (26.5), and the precise displayed norm-sum
constant in (26.6), are not separate new declarations.

The alternating family is formalized at α=0; the full range
0<α<1/2 is not newly formalized. The displayed off-critical-zero
calculation in §30 is not newly formalized in this change.
These omissions do not enter the checked exclusion, sieve divergence,
joint optimization, or conditional RH results.

## The remaining RH obligations

Let z* denote canonicalTailCertificate, let r* denote pointDualResidual,
and let A be anchoredSignedTail (hilbertSequence z*).

1. **Open — canonical signed cancellation.** Under r*≠0, prove Summable A.
   The certificate is already proved to exist under that alternative, and
   tailCertificate_not_summable_signedTail would then contradict it.
   The checked equivalence
   canonicalTailSummability_iff_pointDualResidual_eq_zero
   exposes the full strength of this proposed provider.

2. **Open — a concrete additive estimate.** Under the same alternative,
   derive summability of \(|Z(n)|/n^2\), or an eventual power/logarithmic
   saving, from the actual reciprocal-residue equations. The formal
   exclusion criteria do not assert these bounds for z*.

3. **Open — divergent actual screened gains.** Supply finite legal trial
   families for JointScreenedGainDivergence. The theorem
   riemannHypothesis_of_jointScreenedGainDivergence proves the implication
   with this premise explicit. Under any actual certificate, the checked
   telescope bounds accumulated gains by its energy minus the initial
   capacity; obtaining divergence must genuinely exclude that alternative.

The exact additional identities
reciprocalDefect_eq_certificate_error and
screenedTrial_source_certificate_error identify the missing source
correlations with z−z_N. They do not assert that the correlations are
large enough, small enough, or summable.

The prime-sieve obstruction matters to both attempts: correct coordinate
and coefficient limits coexist with divergent full-tail energy. Likewise,
a vanishing tail norm multiplied by an unbounded boundary-operator norm
need not tend to zero. Neither interchange is justified by generic Hilbert
regularity.

## Verification record

The combined source and axiom check succeeded with exit code 0:
job_a6TuctA7RAJ12OqO6zPXhY4-Q6hTwnEI, 16.158 seconds.
Source SHA-256:
0202d2fe8fa542571dff5d1943c991b6dd0908cd915d3b00745e5c58c803be12.

All 23 audited endpoints reported only propext, Classical.choice,
and Quot.sound. The source contains no sorry, admit, project-local axiom,
or unsafe declaration. Ordinary foundational axioms do not discharge
substantive hypotheses appearing in theorem types.

The separate ephemeral unconditional attempt,
job_-CU5vw5_k8KEtbWDSNwiaQ38cRHXFaOS, ended with this unsolved goal:

~~~lean
hr : pointDualResidual ≠ 0
hcert : IsResidueTailCertificate canonicalTailCertificate
hweighted : Summable (fun k =>
  positiveWeight k * hilbertSequence canonicalTailCertificate k ^ 2)
hprimitive_square : Summable (fun k =>
  anchoredSignedTail (hilbertSequence canonicalTailCertificate) k ^ 2)
hdecay : Tendsto (fun n =>
  Real.sqrt (n : ℝ) * signedTail (hilbertSequence canonicalTailCertificate) n)
  atTop (𝓝 0)
⊢ Summable (anchoredSignedTail (hilbertSequence canonicalTailCertificate))
~~~

This was a bounded tactic search after the mathematical reduction, not
an exhaustive search for every possible RH proof. No unfinished Lean
declaration from the attempt was persisted.

The source check is distinct from project integration: the final
workspace checkpoint checks the actual module imports and affected
dependents before publication. Its outcome and commit are recorded in the
updated handoff. A failed unconditional proof search is evidence of a
remaining goal, not a refutation of RH.

The first project-validation attempt exposed a missing explicit import of
Mathlib.Tactic.NormNum.Prime in FinitePrimeProductBounds. The import was
added; the module then passed an isolated check using only its own imports
in job_ly99kJRRntSsOxCkYNjgyXIwewYshITq (exit 0), including the standard
axiom audit of its divergence theorem. No mathematical statement or proof
was changed by this integration repair.
