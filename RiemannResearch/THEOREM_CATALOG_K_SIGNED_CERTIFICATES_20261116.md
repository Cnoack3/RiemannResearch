# Signed K middle block: verified one-sided certificates and remaining obligation

Prepared 16 November 2026.

## Status

**The requested unconditional cancellation is not proved by this change.**

The new module `RH/QJointSieveSignCertificate.lean` extracts quantitative,
one-sided estimates from the existing signed sieve certificate and applies
them to the actual squarefree fit and the actual closed prime span. It does
not replace the squarefree dictionary by all conductors, change the fit, assume
RH, or assume Q-mean zero.

The new results strengthen the repository's quantitative reduction. They are
not claimed as an improvement to a published zero-free-region or density theorem.

## Exact objects

In the physical Pareto Hilbert space, let

- $V$ be `QSquarefreeMeasureRigidity.paretoSquarefreeClosure`;
- $S$ be `ZetaTwoOptimizerStage.closure`, its matching Q realization;
- $W$ be `QPrimeCarryProjection.primeClosure`;
- $K=V\cap W^{\perp_P}\cap W^{\perp_Q}$, using the physical transfer maps;
- $D f(n)=f(n)/n$;
- $f_Q=\mathrm{toPareto}(\Pi_S^Q1)$ and $f_P=\Pi_V^P1$;
- $k=\Pi_K^P(f_Q-f_P)$;
- $u=f_Q-\Pi_W^P f_Q-\Pi_K^P f_Q$.

The notation $\Pi_W^P$ means projection onto the Pareto image of the closed
prime span. The new instance proves this image is closed via the existing
continuous linear equivalence.

The existing P-mean theorem gives $\Pi_K^P f_P=0$, hence
$k=\Pi_K^P f_Q$. The exact block equation is

$$
 k+\Pi_K^P Dk=\Pi_K^P D1-\Pi_K^P Du.
$$

The acceptance equality remains

$$
 \boxed{\Pi_K^P D1=\Pi_K^P Du.}
$$

## New unconditional quantitative estimates

Define the finite signed conductor pairing

$$
 b_N=-\sum_{d\mid N!}\mu(d)
       \langle k,Dg_d\rangle_P-\langle k,Du\rangle_P.
$$

The $d=1$ and prime terms vanish by the existing checked theorem
`QSievePairingCertificates.mobiusPairing_eq_nonprime`. Composite squarefree
terms remain. The final middle-coupling term remains with its sign.

These are finite sums over conductors, but their entries are complete Hilbert
inner products involving the actual infinite fit. A numerical truncation is
not an exact certificate without certified tail errors.

Put

$$
 E=\|k\|_P^2+\langle k,Dk\rangle_P,\qquad a_N=\frac1{N+1}.
$$

The existing complete error estimate is

$$
 |E-b_N|^2\le a_N\|k\|_P^2,\qquad E\ge\|k\|_P^2.
$$

The new Lean proofs yield

$$
 \boxed{\|k\|_P^2\le 2b_N+\frac1{N+1}},\qquad
 \boxed{b_N\ge-\frac1{4(N+1)}}.
$$

In particular, any exact certificate $b_N\le0$ gives
$\|k\|_P^2\le1/(N+1)$.

Proof: with $r=\|k\|_P$, the complete error estimate implies
$r^2\le b_N+r\sqrt{a_N}$.
Use $2r\sqrt{a_N}\le r^2+a_N$ for the first bound and
$r^2-r\sqrt{a_N}=(r-\sqrt{a_N}/2)^2-a_N/4$ for the second.
No sign of an individual composite summand is assumed.

## Exact remaining arithmetic obligation

The following one-sided cofinal statement is equivalent, in Lean, to the
requested equality for the actual squarefree fit:

$$
 \boxed{\forall\varepsilon>0\;\forall J\;\exists N\ge J:
             b_N\le\varepsilon.}
$$

Thus it is enough to prove an arbitrarily small upper bound along cofinally
many cutoffs. An absolute-value bound, termwise cancellation, or convergence
proof for a substituted fit is not required by this consumer.

**This arithmetic provider is still missing.** The new equivalence must not
be marked as an unconditional proof of its right-hand side.

To close the task, prove this statement for
`QJointSieveSignCertificate.Squarefree.actualSignedSieve` from the actual
coefficients, with no cancellation, RH, target-membership, or equivalent
density premise. Then apply
`Squarefree.cancellation_iff_cofinal_signed_sieve_upper`.

## P mean, Q mean, and displacement are separate

| Claim | Checked status |
|---|---|
| $\langle1,k\rangle_P=0$ | Proved, including the actual squarefree block. |
| $\langle1,h\rangle_Q=0$ for every $h\in K$ | Not proved. Equivalent to $\Pi_K^P D1=0$. |
| $\Pi_K^P D1=\Pi_K^P Du$ for the actual fit | Not proved. Equivalent to the cofinal signed upper bound above. |

The exact energy identity, also specialized in the new module, is

$$
 \|k\|_P^2+\langle k,Dk\rangle_P
 =\zeta(2)\langle1,\mathrm{toQ}(k)\rangle_Q
  -\langle k,Du\rangle_P.
$$

Even a future proof of Q-mean zero would leave the actual middle coupling to
control. The present proof does not assume Q-mean zero, and cancellation does
not require asserting that the two vector terms separately vanish.

## Main Lean declarations

All names below are in `RiemannResearch.RH.QJointSieveSignCertificate`.

| Declaration | Content |
|---|---|
| `scalar_signed_certificate` | General real-variable estimate and sharp negative floor from the stated scalar hypotheses. |
| `block_signed_sieve_bounds` | Both finite bounds for any block satisfying the exact normal equation. |
| `block_norm_sq_le_of_signed_sieve_nonpos` | An exact nonpositive signed certificate bounds the block norm. |
| `block_eq_zero_iff_cofinal_signed_sieve_upper` | One-sided cofinal criterion, with no Q-mean-zero premise. |
| `Squarefree.actualK_normal` | Specialization to the actual squarefree fits and actual prime closure. |
| `Squarefree.actual_signed_sieve_bounds` | Unconditional finite bounds for those actual objects. |
| `Squarefree.cancellation_iff_cofinal_signed_sieve_upper` | The requested equality iff the remaining arithmetic provider. |
| `Squarefree.actualK_pMean_zero` | Established P-mean zero. |
| `Squarefree.qMean_zero_iff_reciprocal_projection_zero` | Separate Q-mean obligation. |
| `Squarefree.actualK_energy_qMean` | Complete energy with both Q mean and signed middle coupling retained. |

## Sources and verification

Inspected repository base:
`8db47ed43c4ffd5fffff3b69319f21c3a1bc0e28`.

Existing checked inputs:
`QParetoJointAnnihilator.lean`, `QParetoJointBlock.lean`,
`QSievePairingCertificates.lean`, `QJointSieveForcing.lean`,
`QSquarefreeMeasureRigidity.lean`, and `QPrimeCarryProjection.lean`.

Published background:

1. B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
   of the Riemann hypothesis*, [arXiv:math/0607733](https://arxiv.org/abs/math/0607733),
   Theorem 1 and the following weight-comparison discussion. The all-conductor
   constant-membership statement is equivalent to RH; equivalent norms do not
   identify the two orthogonal projections.
2. L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the
   Riemann hypothesis*, [arXiv:math/0202141](https://arxiv.org/abs/math/0202141),
   Theorem 1.1 and Section 2.2. Its proof of the sufficient approximation
   direction assumes RH. It is not an unconditional provider for this K block.

No published theorem closing this particular signed prime/squarefree block
was identified in the inspected sources. No assertion that K-cancellation
alone is equivalent to RH is made.

Wolfram Language independently checked the scalar implication by real
quantifier elimination (result `True`). That computation is not used as a
Lean axiom or proof term.

The coherent generic snippet passed Bazel/BuildBuddy in
`job_B_SWzInT4WTsBB0ue6LGxnMWHkEJvZVN`.
The committed module includes axiom-audit guards on the two central actual-fit
theorems, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The initial actual-fit file check exposed a missing closedness instance, which
was supplied. The next check compiled the actual-fit theorems and confirmed
the standard axiom list, but its guard caught a style warning in a long audit
command. The audit command has been shortened.

The managed publication checkpoint validates the exported module, its axiom
guards, and the full `//:RiemannResearch` target before committing and publishing.
Its terminal job identifier and exact published commit are reported with the
final verification report.
