# CRT proof recovery and Lean verification — 2026-10-13

## Verification

Recovered workspace: `ws_8mGWZfvEgM4mkcQCUvjzqZ-f3Ex2LutN`.
Base commit: `d01390749cf05f9481b868ba242d58bf06945dd7`.

The old queued job `job_e5PYFoNAU3e2gY8cb4SxO0aupoxBFpH5`
terminated as interrupted: its owner exited before compilation began.
The saved four-module source and aggregate exports remained intact.

Fresh combined import and axiom audit:
`job_CfF-ItEXLk9irhbBIdf40jU-kB3HtFhC`.
Result: succeeded, exit code 0, verified true, 19.168 seconds execution.
Submitted code SHA-256:
`1798e363fb178118056b5bc250deb68dfd9f76a0cd725af8165f97c04f71038c`.

Imported modules:
- RiemannResearch.Analysis.AffineObservationProjection
- RiemannResearch.RH.ExactHeadTailMoment
- RiemannResearch.RH.ExactHeadCRTExample
- RiemannResearch.RH.CanonicalMobiusErrorEnergy

All ten selected transitive axiom checks reported exactly the ordinary
foundations: propext, Classical.choice, Quot.sound. They covered the general
square completion, scalar prefix equivalence, finite legality, attained
minimum, full remainder, conditional RH consumer, all three explicit
M=1 example formulas, and PNT-backed normalized complete error limit.
The build produced style warnings but no compiler errors.

## Precise mathematical scope

With g_d(n)=(n mod d)/d, beta_M=sum_(d=1)^M mu(d)/d, M>0, and
a finite tail dictionary S of conductors d>M, put
F=-sum_(d=1)^M mu(d)g_d+sum_(d in S)c_d g_d.
The checked scalar characterization states:
F(n)=1 for 1<=n<=M iff sum_(d in S)c_d/d=beta_M.

In the complete Pareto Hilbert space, let T be the finite tail span,
z=1+sum_(d=1)^M mu(d)g_d, e the first-coordinate representer,
p=P_T z, and q=P_T e. For nonempty S, ||q||^2>0. The optimizer is
x*=p+((beta_M-<e,p>)/||q||^2)q, and every feasible x satisfies

    ||z-x||^2 = ||z-p||^2
                 + (beta_M-<e,p>)^2/||q||^2
                 + ||x-x*||^2.

No physical tail is truncated. The candidate has literal finite legal
support with an explicit conductor cap. Enlarging the dictionary cannot
increase the attained minimum.

## Open arithmetic premise

The exact type of riemannHypothesis_of_cofinally_bounded_tailMinimum
retains a nonempty finite dictionary schedule s, a real C, and the premise

    forall M, exists N, M <= N and tailMinimum (N+1) (s N) <= C.

This premise is Open. The unconditional canonical error-energy limit
E_N/N -> 0 does not prove this uniform bound or E_N -> 0.

The manuscript's specific constant-12 estimate, literal determinant,
fixed-anchor representation, and packaged unrestricted-infimum dichotomy
are not newly formalized here. The published RH-to-density theorem is
still an explicit analytic provider in the existing converse assembly.
It is not an axiom or hypothesis of the new finite optimization or its
bounded-minimum-to-RH implication.

## Publication gate

The combined import audit above verifies the four modules at the recovered
workspace state. Publication must additionally pass agent_workspace_checkpoint
with push enabled, including any integrated source validation. A queued
checkpoint is not publication evidence; its terminal record supplies the
published commit and final validation scope.

## Integration recovery

The original checkpoint job_XC6GGr4zcK9KAcoiTm7S6xu9jlPcuOZM
created local commit 3df946d873ac3de4140cc49ca945abdf755780ab, then
failed while integrating newer main because both the aggregate imports
and theorem catalog had concurrent edits. Nothing was pushed by that job.
The original workspace and commit remain preserved.

The same four modules are carried into workspace
ws_ZA4GigtIG0nd5-s_SNgoG3aOTA9irjqY, based on published commit
c7306f6dabafe0cf7ede9250f5f8775f507fcb08. Existing newer exports and
catalog entries are retained. Publication of this combined source requires
a fresh successful server checkpoint.
