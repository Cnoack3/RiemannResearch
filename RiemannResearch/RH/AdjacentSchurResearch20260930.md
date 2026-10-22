# Adjacent conductors improve the actual gain certificate

Date: 2026-09-30, America/Los_Angeles.
Continuation of FirstSiteTwoChannels20260930.md and requested base
4f4ede96e4e8fd5167f4f389bf03c64ee47670cc.

This is a paper proof and a Lean formalization whose declaration bodies passed\nisolated kernel checks. Final integrated publication uses checkpoint validation.
It establishes no capacity divergence, RH proof, or claim of priority. The earlier
checkpoint ended interrupted after its worker exited, without publication. This
adjacent-Schur module is now being integrated with the preserved three modules.

## Exact adjacent trial and all-period bound

At new conductor q=n+3, let

$$v_q=t_q-\frac{q-1}{q}t_{q-1}.$$

The old reciprocal observation cancels exactly, so
$$\eta_q=-\langle v_q,z_{q-2}\rangle.$$
Here the subscript on eta denotes the conductor; the Lean stage is q-2.
The exact finite inverse-Gram completion gives
$$\|v_q\|^2=\sigma_q+
  \|\operatorname{synthesis}(c-\operatorname{inverseCoeff}(t_q))\|^2.$$
The second square is retained before comparing sigma to the trial norm.

The head cancels, and the entire physical sequence is
$$v_q(k)=\frac{(k\bmod q)-(k\bmod(q-1))}{q}.$$
This is also $-1/((q-1)q)$ times the repository's
`adjacentMomentPacket (q-3)`; the existing theorem
`adjacentMomentPacket_harmonic_exact` retains the full infinite remainder.
Let H_d=sum_{m=1}^d 1/m, L=q(q-1), and let T_d be the literal raw-residue
remainder from `AdjacentResidueHarmonic.lean`. Then

$$\|v_q\|^2=
 \frac{H_{q-1}-(q-1)/q+T_{q-1}}{q^2},
 \qquad 0\le T_{q-1}\le(q-1)/q.$$

For an independent check of the first period, partition it into
$[m(q-1),mq)$ and $[mq,(m+1)(q-1))$, m=1,...,q-1.
The signed trial values are $(q-m)/q$ and $-m/q$, respectively.
Telescoping the positive Pareto weights gives

$$\sum_{1\le k<L}\frac{v_q(k)^2}{k(k+1)}
 =\frac{H_{q-1}}{q^2}-\frac{q-1}{q^3}.$$

Every remaining coordinate is bounded by $(q-1)/q$ in absolute value,
and the entire tail weight is $1/L$. Thus its energy is at most
$(q-1)/q^3$. Combining the exact prefix and explicit full tail yields

$$\boxed{\sigma_q\le\|v_q\|^2\le H_{q-1}/q^2},
\qquad
\boxed{\mathrm{gain}_q\ge q^2\eta_q^2/H_{q-1}}.$$

This applies to the actual prime and nonprime gains, with no replacement of
eta by its positive source and no deletion of the screened factorial/CRT terms.
The general norm certificate and its historical capacity accounting are intact.
The raw adjacent harmonic estimate was already in the repository; the new
assembly connects it to the actual Schur pivot and gain.

## Effect on the source scale

The established factorial source lower bound delta_q>=1/(2q) already implies
$$\frac{\delta_q^2}{\sigma_q}\ge\frac1{4H_{q-1}}.$$
With the classical PNT tail/product calculation delta_q~(log q)/q,
$$\frac{\delta_q^2}{\sigma_q}\ge(1-o(1))\log q$$
on prime conductors. PNT in Chebyshev form therefore gives
$$U_N\ge(1-o(1))N.$$
Combining this with the Burnol point-to-constant transfer C_N=O(log N)
gives a stronger explicit rate
$$C_{N+1}/U_N=O(\log N/N),\qquad
 |\tau_N|=O(\sqrt{\log N/N}).$$
These rate assemblies remain classical deductions, not newly completed
analytic Lean providers. They supply no lower bound on the actual signed eta.

## A concrete block task for the remaining RH step

For either all prime conductors or all composite conductors in [2^j,2^(j+1)),
put
$$M_j=\sum q^2\eta_q^2.$$
The trial bound and H_{q-1}<=1+log q give
$$\sum_{q\text{ in block}}\mathrm{gain}_q
 \ge \frac{M_j}{1+(j+1)\log2}.$$
Consequently a uniform eventual lower bound M_j>=c>0, or a sufficiently dense
set of blocks with divergent harmonic mass, would force the respective gain
series to diverge. Under the vanishing-slope result, prime-gain divergence
also forces nonsummability of the full angular increments Gamma. Nonprime-gain
divergence forces J_N unbounded directly. Either would imply RH by the actual
capacity criterion. This block moment estimate is OPEN.

The fixed dyadic moment target is sharper than demanding nonsummability of
the unscaled 2p bucket certificate. Exploratory double-precision data show
that the latter loses a decreasing factor through sigma/K: on prime p blocks
[16,32), [32,64), [64,128), the bucket lower sums are approximately
0.3860, 0.1314, 0.0558, while their actual gains are 2.2249, 1.4614, 1.1241.
Several signed p*eta_(2p) values are very close to zero and change sign.
These are motivation for aggregate moments and smaller norm costs, not
certified estimates or asymptotic evidence.

The same full-period digamma computation screens the improved target:

| conductor block | prime M_j | prime harmonic lower | composite M_j | composite harmonic lower |
| --- | ---: | ---: | ---: | ---: |
| [16,32) | 2.2522 | 0.5995 | 9.3617 | 2.5072 |
| [32,64) | 2.3230 | 0.5365 | 18.8550 | 4.4095 |
| [64,128) | 2.6032 | 0.5139 | 19.9868 | 3.9894 |
| [128,256) | 4.5566 | 0.7824 | 24.1568 | 4.1504 |

The corresponding last-block actual gains are about 1.1931 and 7.2842.
These conductor blocks differ from the earlier budget-index blocks by the
explicit q=n+3 shift. The entries are exploratory double-precision values,
with no interval or kernel certification; they do not prove an eventual
positive lower bound. They indicate that the adjacent norm test captures
substantially more finite gain than the binary-bucket norm test.

## Formalized finite certificate

`ParetoAdjacentSchurBound.lean` derives the exact scaled-packet identity,
the full-tail harmonic norm identity and bound, the actual Schur upper bound,
the balanced eta identity, and the corresponding actual prime/nonprime lower
certificates. It contains no sorry, admit, project-local axiom or unsafe
declaration. Its complete declaration bodies passed the isolated check recorded\nbelow. The raw energy theorem it uses is an existing repository result. Final\ninstalled-module validation is performed by the publication checkpoint.

## Additional primary-source check

H. Carvill, arXiv:2510.18132 (2025), was examined as a possible smoothed
Gram comparison. It is not used. The proof of Theorem 6.1, page 8, asserts
|lambda| >= c*d for lambda=(j'-j)log2+(k'-k)log3,
c=min(log2,log3), d=|j'-j|+|k'-k|. For indices (1,0) and (0,1), this would
require log(3/2)>=2log2=log4, which is false. Thus that proof does not justify
the proposed decay transfer; the asserted conclusion would need an independent
valid proof before use. The repository's exact adjacent-residue estimate does
not depend on this preprint.
https://arxiv.org/abs/2510.18132

## Historical execution status at the initial handoff

The publishing checkpoint job_e71bWLxwW6Ko2zCxGEFTavC_Q3fdNMdI was last
observed running at 1,999/2,086 tasks (95.8%), with no progress after the
initial build replay. Subsequent status and declaration-search calls returned
UNAVAILABLE connection timeouts. Its terminal result could not be established.
No new kernel verification or publication is claimed. The last confirmed
published commit remains be45e99a22abe009356faf7dd686248b4ebb77d5.
The adjacent-Schur candidate is a local draft and was not included in that
running checkpoint. On continuation, recover the existing job before
submitting any Lean verification or mutating its workspace.

### Recovery on October 1, 2026 UTC

Job `job_e71bWLxwW6Ko2zCxGEFTavC_Q3fdNMdI` was recovered as terminal
`interrupted`, with the error that its owner exited while the checkpoint was
pending. It was not replayed. The workspace retained the three installed
candidates, root exports, catalog changes and first note. No active job remained.
The adjacent candidate and this note were recovered from the original local
source package and added without overwriting existing work. This recovery is
not a kernel-verification or publication receipt.

### Successful isolated kernel check

Job `job_ZsK2rFhy2jzVtSlv1C5A7di2gYzpU3y3` compiled the complete balanced-trial
and adjacent-Schur declaration bodies on October 1, 2026 UTC. It returned terminal
success, exit 0, verified true, elapsed 5.397 seconds. Code SHA256:
`33511cdde63e677aa5024b9853248f3a2755b2caad99edd2eef1b82727eb8846`.
The audited `adjacentInnovationLower_sum_le_capacity` and
`factorialPrimeSourceEnergy_ge_adjacent_harmonic` depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Nonfatal tactic-linter warnings
were reported. No arithmetic growth hypothesis was introduced into these finite
certificates. The actual moment lower bound and the analytic scale providers
remain Open. The installed modules and affected dependents receive final
validation through the publishing checkpoint.
