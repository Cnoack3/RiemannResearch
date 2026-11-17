# Exact-head Green continuation: remove the head before estimating R5

Date: 16 November 2026 (America/Los_Angeles).
Source: the selected 17-page *Best Nyman Beurling for RH.pdf*, internally
*Exact-Head Green Profiles in the Nyman–Beurling Program*, 27 July 2026.
Starting repository revision: `f5995c89c9e2f16f8ec1dbdad613c1dbef7e9579`.
Integrated with `afb083e826484de4fdaa7a84f144d2a42bc1db42` before publication.
That newer revision already supplies the complementary-energy inequality,
deficit theorem, and sharper kernel witnesses at all four cutoffs. They are
reused directly. This continuation adds the full tail Gram remainder,
the explicit jointly cofinal RH assembly, and an independent cutoff-seven
certificate using nine six-decimal coefficients.

## The mathematical improvement

Write P=greenPeriod(x), R for the actual complete-weight gcd-atom optimizer,
q=||R||², psi for the explicit affine signed-moment probe, and
m=<R,psi>. For any upper-span correction v and real alpha, set

    g(r) = psi(r) - alpha*C_P(r) - v(r),
    T_x(alpha,v) = sum_{x<r<P} w_P(r) g(r)^2.

The optimizer, target and every upper-span correction vanish at the positive
head r<=x. Therefore the following are exact identities:

    ||g||²_complete = sum_{1<=r<=x} w_P(r) psi(r)^2 + T_x(alpha,v),
    m-alpha*q = sum_{x<r<P} w_P(r) R(r) g(r),
    q*T_x(alpha,v) - (m-alpha*q)^2
      = (1/2) sum_{x<r,s<P} w_P(r)w_P(s)
          (R(r)g(s)-R(s)g(r))^2.

All progression weights still contain their complete infinite tails. Only
residue coordinates on which R is exactly zero have been removed. The signed
summands and complete nonnegative Gram remainder are retained.

In particular, for M>=0 and eps>0,

    T_x(alpha,v)<=M
      ==> m<=(alpha+eps)*q + M/(4*eps).

This is a strictly weaker sufficient R5 requirement than bounding the full
centered-probe energy. No bound on q or on the affine coefficients is assumed.

## Meaning of the previous head obstruction

The previous H_x lower bound remains correct for the full centered-probe
energy. Its paper comparison with square-root Mobius cancellation is still
unformalized. Neither that comparison nor a uniform upper bound for H_x is
needed by the tail-only criterion.

The exact-head support restriction is the additional orthogonality used here.
Upper-span corrections cannot change the head, but a head-supported test
function pairs to zero with R anyway. Thus a difficulty in bounding the full
probe is not automatically a difficulty in bounding its signed observation.
This does not establish a uniform tail bound.

## Conditional RH assembly

`riemannHypothesis_of_atom_affine_tail_probe` checks the following implication.
At the same cofinal stages, take the actual affine normal fit h and legal
upper-span corrections v. Suppose constants satisfy

    eps>0, k>=0, C>=0, M>=0, k<1-alpha-eps,
    (signedSum(b)-signedSum(h))^2 <= k^2*q^2+C*q,
    T_x(alpha,v)<=M.

Then RH follows through the existing bounded-exact-head closure theorem.
The finite normal equations and upper-span membership are explicit in the
declaration. The two jointly cofinal analytic bounds are **Open**. This is a
conditional research reduction, not an unconditional RH theorem.

The PDF's stronger E_aff=O(q/x) and bounded-coefficient conjectures are not
assumed. The projected-Mobius dispersion factor from the previous continuation
remains available as a sufficient way to bound the signed error.

## Finite certificates

The integrated `ExactHeadProbeWitnesses.centered_probe_energy_bounds` already
certifies these stronger endpoints, using the published rational coefficients:

| cutoff | complete complementary-energy upper bound | classification |
|---|---:|---|
| 5 | 18057/1000000 = 0.018057 | Lean kernel checked on integrated main |
| 7 | 32283/1000000 = 0.032283 | Lean kernel checked on integrated main |
| 11 | 9073/1000000 = 0.009073 | Lean kernel checked on integrated main |
| 13 | 5777/1000000 = 0.005777 | Lean kernel checked on integrated main |

The following independent replay uses smaller six-decimal coefficients and
only one explicit progression step. It preserves a short, separate witness;
it does not supersede the sharper endpoints above.

Reusing the kernel-checked cutoff-five full-energy upper bound 0.63 and
unperiodized head lower bound 0.6026 gives

    T_5(1/2,v_5) <= 137/5000 = 0.0274.

An independent rational replay uses one explicit progression term and a
proved enclosure for the remaining infinite progression. It rounds each
energy summand upward on a 10^(-10) grid and uses six-decimal rational
corrections. All four tested stages satisfy the candidate M=1/30:

| cutoff | complete tail upper bound | classification |
|---|---:|---|
| 5 | 93638483/5000000000 = 0.0187276966 | External exact rational replay; the weaker 0.0274 bound has a separate Lean proof |
| 7 | 324629179/10000000000 = 0.0324629179 | Exact rational witness; Lean module checks the upper bound 1/30 |
| 11 | 45443099/5000000000 = 0.0090886198 | External exact rational replay |
| 13 | 57791241/10000000000 = 0.0057791241 | External exact rational replay |

The cutoff-seven Lean certificate checks all nine correction coefficients,
all 202 tail residues, and every complete infinite progression. The proposed
finite coefficient vector is not an assumed optimizer. The actual-optimizer
moment conclusion uses the proved tail observation inequality.

The complete reproduction source is retained in
`ResearchData/ExactHeadGreen20261116/moment_tail_reproduction.md` below
`RiemannResearch`. Its Python block reads the centered-probe witness file and writes
`ResearchData/ExactHeadGreen20261116/moment_tail_certificates.json` below
`RiemannResearch`. Its optional `--emit-lean PATH` reconstructs the cutoff-seven
certificate source. Python output alone is not a Lean kernel certificate.

## Revised agenda and acceptance criteria

| Item | This continuation | Next acceptance criterion |
|---|---|---|
| R1 | Reuse all four kernel witnesses; add an independent cutoff-seven replay | Replay actual dispersion and proportional moments at 7,11,13; certify 19 and 23 |
| R2 | The residue head/tail split is exact | Keep this residue split distinct from the PDF's conductor-block ledger |
| R3 | Full tail Gram identity retains mixed terms | Identify the actual boundary carry/discrepancy with the affine subspace |
| R4 | Existing direct signed-error criterion is retained | Supply a jointly cofinal signed dispersion estimate with strict gap |
| R5 | Full-energy budget replaced by the smaller tail-energy budget | Construct v_x and bound T_x(alpha,v_x) uniformly on the same cofinal stages, with alpha<1 |
| R6 | M=1/30 passes four finite tail stages | Test larger stages with complete rational bounds; finite success is not a cofinal theorem |

Priority: estimate the tail after removing both the exact head and the legal
upper span. Do not require the stronger full-probe head bound merely because
it appeared in the previous sufficient criterion. The unresolved analytical
content has not disappeared: the entire remaining residue tail and its
infinite progression weights must be controlled.

## Provenance and verification

The full tail Gram remainder is independently assembled from
the repository's existing finite weighted identities. No literature novelty
claim is made. The primary Baez-Duarte manuscript
<https://arxiv.org/abs/math/0202141> supports the natural-dilation closure
criterion; it is not an unconditional provider of the two new analytic
hypotheses. The squarefree-counting source
<https://arxiv.org/abs/1107.4890> belongs to the earlier head-coercivity paper
argument and is not an input to these tail theorems.

Integrated focused audit: job `job_KBUEm06srOhyJofOSTB_lnSRKLCs6YUl`
passed all 35 guards and the new modules in 153.251 server-reported seconds.
[Build](https://app.buildbuddy.io/invocation/ceaed8ab-f9c4-4375-ab46-e65ac3bfac42).
The integration workspace-opening request took 27.6 seconds, independently
of verification. Admission-to-start delay was about 0.009 seconds; status
polls used the prescribed 30–60-second cadence. These are separate from
the server-reported build duration and are not kernel-only timings.

Focused Bazel/BuildBuddy checks of the retained pre-integration draft:

- `ExactHeadMomentTail`: job `job_j6o85YMYxeU9p0j8bfsEEHZMnWSp4GBr`, 52.126 s,
  [build](https://app.buildbuddy.io/invocation/24bd8369-049d-44df-8c17-e1d452110a4f).
- `ExactHeadGreenTailCriterion`: job `job_Fkkt73Y4xetkRC1EZleAEKQ-Y6bZ4MbC`, 54.752 s,
  [build](https://app.buildbuddy.io/invocation/9e45d263-71cc-4a98-a512-4bd21587b8c3).
- Integrated `ExactHeadGreenAxiomAudit`, including the cutoff-seven certificate:
  job `job_aqutW8-gxafAfSF1Vhc4kONFk9oPLTSE`, 111.003 s,
  [build](https://app.buildbuddy.io/invocation/6c621710-69bc-46fd-85db-bfa065d85b80).
  All 32 guarded declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`; there is no added axiom or unproved placeholder.

The integrated audit preserves all 31 upstream guards and adds four, for 35.
These earlier focused checks precede the final managed full-project checkpoint, which
is the authority for the exact published source. Publication must pass
`//:RiemannResearch` and the permanent guarded axiom audit.

Retained draft workspace: `ws_cscVXTomnZXwUW5dQvAjrxXqAne9iRiA`.
Integration workspace: `ws_fHGW-QSd-QVGb9AG12aGY_B-WuzbGO3H`.
No proof of RH, unconditional cofinal dispersion bound, or unconditional
cofinal signed-moment bound is claimed.
