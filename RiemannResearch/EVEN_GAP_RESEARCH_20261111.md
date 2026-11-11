# Even-gap prime correlations: exact reduction and unconditional limits

Date: 2026-11-11. Review base: `6c4fe3312e24b00813bcc5c329cf28ba0fe14333`,
which includes the requested `4990152321b0c1926efeeebc10cc0e33b46cd562` development.
The user approved this reviewed development for publication on 2026-11-11.
Publication uses the server checkpoint, including validation of any integrated main changes.

## 1. Outcome

The new result is a quantitatively exact removal of the odd-gap obstruction
at the **variance scale**, with all one-point terms and endpoints retained.
It applies whenever `1 <= H <= N` eventually and `H log(N)/N -> 0`, hence
throughout every fixed polynomial range in the request. The needed even-gap
cancellation itself remains open. The identities are additions to this
repository; no claim of a new theorem in analytic-number-theory literature is made.

The strongest unconditional analytic consequence found in the literature is
coarse cancellation at the `NH^2` scale in a substantial polynomial range.
That consequence is distinct from the new kernel-checked reductions, and it
does not identify the secondary term at scale `HN log N`.

## 2. Definitions and complete endpoint identity

Write

\[
 a(n)=\Lambda(n)-1,\quad
 P_N(h)=\sum_{x=0}^{N-1}\Lambda(x+2)\Lambda(x+2+h),\quad
 R_N(h)=\sum_{x=0}^{N-1}a(x+2)a(x+2+h).
\]

Let

\[
 M_N=\sum_{x=0}^{N-1}\Lambda(x+2),\quad e_N=M_N-N,
 \quad b_N(h)=\sum_{x=0}^{h-1}[\Lambda(N+x+2)-\Lambda(x+2)].
\]

The already established exact relation is

\[
 R_N(h)=P_N(h)-N-2e_N-b_N(h).
\tag{1}
\]

Set `w_H(h)=H-h` for `1 <= h < H`. The repository's `C(N,H)` is the
complete off-diagonal, not just the fixed-base triangular sum:

\[
 C(N,H)=2\sum_{h=1}^{H-1}w_H(h)R_N(h)+B(N,H),
\tag{2}
\]

\[
 B(N,H)=2\sum_{h=1}^{H-1}\sum_{j=0}^{H-h-1}\sum_{x=0}^{j-1}
 [a(N+x+2)a(N+x+2+h)-a(x+2)a(x+2+h)].
\]

With
\(V=\sum_{x<N}(\sum_{j<H}a(x+j+2))^2\) and
\(D=\sum_{j<H}\sum_{x<N}a(x+j+2)^2\), one has `V=D+C` exactly.
The existing signed-prefix identity is

\[
 C+HN\log H=2\sum_{k=0}^{H-1}E_N(k)+B,
\quad E_N(k)=\sum_{h=1}^{k}R_N(h)
 +\frac N2[(k+1)\log(k+1)-k\log k].
\]

## 3. Precise remaining even-gap estimate

Define

\[
 S_e=2\sum_{\substack{1\le h<H\\2\mid h}}w_H(h)R_N(h),\qquad
 W_o=\sum_{\substack{1\le h<H\\2\nmid h}}w_H(h)=\lfloor H^2/4\rfloor,
\]

\[
 O_o=2\sum_{\substack{1\le h<H\\2\nmid h}}w_H(h)P_N(h),\quad
 \Delta_o=-4e_NW_o-2\sum_{\substack{1\le h<H\\2\nmid h}}w_H(h)b_N(h).
\]

For `H=2K`, the odd weights sum to `K^2`; for `H=2K+1` they sum to
`K(K+1)`. This proves the displayed floor formula. Lean uses the finite sum
`oddWeight` directly; it does not require the floor formula.

Equation (1) gives the exact separation

\[
 2\sum_{h\text{ odd}}w_H(h)R_N(h)=-2NW_o+\Delta_o+O_o.
\]

Consequently, defining

\[
 F_e(N,H)=S_e-2NW_o+\Delta_o+B+HN\log H,
\]

we obtain

\[
 \boxed{C+HN\log H=F_e+O_o.}
\tag{3}
\]

This is `offDiagonal_even_exact`. `prefix_even_exact` identifies the same
right-hand side with `2 sum E_N + B` directly.

The odd-pair support theorem says that a nonzero odd-gap pair must contain
a positive power of two. Applying its proved bound separately at each gap,

\[
 0\le O_o\le 4W_o\log^2(N+H+2)\le 2H^2\log^2(N+H+2).
\tag{4}
\]

In particular `F_e <= C+HN log H <= F_e+4W_o log^2(N+H+2)`.
For `N>=2` and `1<=H<=N`, the checked elementary bound is

\[
 \frac{2H^2\log^2(N+H+2)}{HN\log N}
 \le 18\frac{H\log N}{N}.
\tag{5}
\]

Thus, uniformly for `H<=N^(1-epsilon)` with fixed `epsilon>0`, the error
in removing the corrected odd contribution tends to zero. The stronger
condition `H=o(N/log N)` also suffices. In this range the exact outstanding
target is

\[
 \boxed{S_e=2NW_o-HN\log H-\Delta_o-B+o(HN\log N).}
\tag{6}
\]

**Neither `Delta_o` nor `B` can be deleted using the results checked here.**
The old statement `R_N(h)/N -> -1` gives only an `o(NH^2)` error after
triangular averaging. Equation (4) gives the necessary smaller error after
the one-point terms are removed exactly.

Positivity also gives the unconditional one-sided constraint

\[
 F_e\ge HN\log H-D-4W_o\log^2(N+H+2).
\]

It does not give the missing upper bound or the desired secondary term.

## 4. Singular series: exact arithmetic error versus a model identity

For any real model `sigma(h)` that vanishes on odd gaps, define

\[
 T_\sigma(H)=2\sum_{h=1}^{H-1}w_H(h)(\sigma(h)-1),
\]
\[
 D_e(\sigma;N,H)=2\sum_{h\text{ even}}w_H(h)[P_N(h)-N\sigma(h)],
 \qquad
 G(N,H)=2\sum_{h=1}^{H-1}w_H(h)[2e_N+b_N(h)].
\]

The checked comparison is

\[
 C+HN\log H=D_e+N[T_\sigma(H)+H\log H]-G+B+O_o.
\tag{7}
\]

The signed prefix formulation is also checked:

\[
 D_e=2\sum_{k=0}^{H-1}\sum_{\substack{1\le h\le k\\2\mid h}}
 [P_N(h)-N\sigma(h)].
\tag{8}
\]

For the classical prime-pair singular series,
\(\mathfrak S(h)=0\) for odd `h` and
\(\mathfrak S(h)=2C_2\prod_{p\mid h,p>2}(p-1)/(p-2)\) otherwise.
Montgomery--Soundararajan, equation (16), proves the unconditional model
identity

\[
 T_{\mathfrak S}(H)=-H\log H+(2-\gamma-\log(2\pi))H
 +O_\eta(H^{1/2+\eta}).
\tag{9}
\]

Reference: <https://arxiv.org/abs/math/0409258>. This result is external
here: the new Lean module proves (7)--(8) for a model, not (9).
Substitution into (7) reduces the desired result to the actual arithmetic
estimate `D_e-G+B=o(HN log N)`. Evaluating an Euler product alone cannot
establish this estimate.

The checked absolute-error transfer explicitly loses a factor `H`:

\[
 |D_e|\le 2H\sum_{\substack{1\le h<H\\2\mid h}}|P_N(h)-N\sigma(h)|.
\tag{10}
\]

Matomaki--Radziwill--Tao, Theorem 1.3, gives logarithmic-saving averaged
prime-pair estimates for `N^(8/33+epsilon)<=H<=N^(1-epsilon)`.
Controlling the exceptional shifts by trivial bounds and increasing the
logarithmic saving gives an aggregate absolute error
`O_A(NH/(log N)^A)`. Hence (10) gives `O_A(NH^2/(log N)^A)`.
Reference: <https://arxiv.org/abs/1707.01315>.
This is an external theorem and an elementary consequence, not a newly
formalized analytic provider. Dividing that bound by `HN log N` leaves
`H/(log N)^(A+1)`, which does not tend to zero for polynomial `H` with fixed `A`.
Choosing `A` to grow with `N` is not justified by that theorem.

## 5. Strongest broader-range unconditional consequence located

Guth--Maynard, Corollary 1.4 and its proof in Section 13.2, supplies
quantitative almost-all short-interval PNT estimates from exponent
`2/15+epsilon`, and an underlying mean-square bound with a stretched
exponential saving relative to `NH^2`. The printed corollary has upper
endpoint `N^0.99`.
Reference: <https://arxiv.org/abs/2405.20552>, published in Annals of
Mathematics 203 (2026), 623--675,
<https://doi.org/10.4007/annals.2026.203.2.6>.
These analytic inputs are not formalized in the proposed Lean files.

For a concrete range avoiding any extension of the printed upper endpoint,
fix `eta>0` and take
`N^(2/15+eta)<=H<=N^(0.99-eta)` when the interval is nonempty.
The corresponding full-prefix bound follows by dyadic decomposition:
discard starting points below `N/(log N)^K` using the elementary bound
`|sum a|<=H(log(N+H)+1)`; apply the short-interval mean-square result on
the remaining dyadic blocks. The exponent margin ensures its range holds
on those blocks. Choose `K` larger than the desired logarithmic saving.
Integer endpoint changes contribute only logarithmic endpoint errors.
Thus for every fixed `A>0`,

\[
 V(N,H)\ll_{A,\eta}NH^2(\log N)^{-A}.
\]

The elementary diagonal bound `D<=NH(log(N+H)+1)^2`, the positive power
lower bound on `H`, effective PNT for `e_N`, the elementary shifted-mean
bound `|b_N(h)|<=2h log(N+H+2)`, and the retained endpoint bound
`|B|=O(H^3 log^2(N+H))` then give the derived coarse even-gap estimate

\[
 \boxed{S_e=2NW_o+O_{A,\eta}(NH^2(\log N)^{-A}).}
\tag{11}
\]

This is a leading-order even-gap asymptotic deduced from published work,
not a new breakthrough. Its stated range is deliberately narrower than
the full range of the new parity reduction. In particular it does not
resolve the `-HN log H` term. For polynomial `H`, even a stretched
exponential saving relative to `NH^2` remains too large at the requested scale.

## 6. Parseval and Ramanujan models: what remains after decomposition

For a finite arithmetic model `b(n)` put `U_x=sum_{j<H}b(x+j+2)` and
`E_x=sum_{j<H}(a-b)(x+j+2)`. The Lean code proves

\[
 V(a)=V(b)+2\sum_{x<N}U_xE_x+V(a-b),
\quad V(a)\ge 2\sum_{x<N}W_a(x)U_x-V(b).
\tag{12}
\]

It also proves, for every positive `delta`,

\[
 |V(a)-V(b)|\le\delta V(b)+(1+\delta^{-1})V(a-b).
\tag{13}
\]

These are unconditional finite inequalities, including their specialization
to the actual von Mangoldt sequence. As a **conditional implication**,
`V(b)=O(HN log N)` and `V(a-b)=o(HN log N)` would transfer a model
asymptotic by first fixing and then shrinking `delta`. Neither arithmetic
estimate for a growing Ramanujan model is supplied here.

For a finite expansion `b=sum_r c_r v_r`, the checked empirical Gram identity is

\[
 V(b)=\sum_{r,s}c_rc_s\sum_{x<N}W_{v_r}(x)W_{v_s}(x).
\tag{14}
\]

All `r != s` terms remain. Orthogonality under a complete residue-period
average or prime-torus Haar measure does not identify this finite empirical
Gram with its diagonal.

The numerical model is the finite Ramanujan approximation

\[
 \lambda_R(n)=\sum_{q\le R}\frac{\mu(q)}{\varphi(q)}c_q(n)
 =\sum_{q\le R}\frac{\mu(q)^2}{\varphi(q)}
   \sum_{d\mid(q,n)}d\mu(d),\quad b=\lambda_R-1.
\]

The second formula is Goldston--Yildirim, equation (1.1):
<https://arxiv.org/abs/math/0412366>. The experiment uses this finite
divisor formula. The formal model-transfer theorem accepts any `b`; it
does not claim to verify the numerical evaluation or the Ramanujan formula.

Likewise, a padded additive DFT for the sample must keep the Gram factor
`sum_{x<N}exp(2*pi*i*(k-l)*(x+2)/Q)`. It is not zero for general `k!=l`.
The included finite DFT experiment checks the complete matrix and separately
reports the error made by dropping its off-diagonal part. At N=64, H=16,
Q=128, the actual energy is 240.5753, the Fourier diagonal alone is
655.1113, and the signed off-diagonal correction is -414.5360.

## 7. Numerical evidence and failed shortcuts

The script `tools/even_gap_experiment.py` sieves all prime powers, evaluates
correlations by FFT, independently checks selected gaps by direct dot
products and all odd contributions by their power-of-two exception sums,
and checks an endpoint correction by a direct triple sum on a small sample.
These are floating-point diagnostics, not certified inequalities or limit proofs.
The singular-series constant is a documented numerical approximation.

For `N=1,000,000`, divide all the following by `q=HN log N`:

| H | `(C+HN log H)/q` | `F_e/q` | `O_o/q` | `Delta_o/q` | `B/q` |
|---:|---:|---:|---:|---:|---:|
| 31 | -0.0342122 | -0.0342675 | 0.0000553195 | 0.000923910 | -0.00000604128 |
| 1,000 | -0.0184458 | -0.0199760 | 0.00153015 | 0.0290932 | -0.000222724 |
| 31,622 | -0.0150212 | -0.0558123 | 0.0407911 | 0.627537 | 0.00393948 |

The normalized discrepancy in (3) is below `1.1e-13` in the nine tested
`(N,H)` pairs. This measures numerical consistency only.
At the largest entry, the one-point odd correction is about `0.628q`:
substituting `R_N(odd)=-N` at this precision is numerically inappropriate.

At `N=1,000,000`, `H=1,000`, `R=128`, the model energy, signed mixed
term and residual energy, divided by `q`, are respectively
`0.00250845`, `-0.0000239870`, and `0.33379326`; their sum is the actual
`0.33627773`. Increasing a small fixed cutoff does not make the remaining
energy negligible in this test. No extrapolation to growing `R` is made.

## 8. Repository additions and remaining obligations

Four new analysis modules are added:

| Module | Responsibility |
|---|---|
| `EvenGapPrimeReduction.lean` | Exact parity/prefix reduction, explicit odd error enclosure, one-sided positivity bound. |
| `EvenGapPrimeAsymptotic.lean` | Checked `H=o(N/log N)` and polynomial-range equivalences. |
| `EvenGapSingularModel.lean` | Full model comparison, even signed prefixes, explicit loss in absolute averaging. |
| `ShortIntervalModelTransfer.lean` | Finite variance transfer, signed cross term, variational lower bound, empirical Gram. |

The development exports those modules from `RiemannResearch.lean` and adds
this research note and a theorem catalog. Existing theorems are not weakened.
The reproducible numerical script and CSV/JSON results are supplied in the
[review archive](https://chatgpt.com/library?file_id=libfile_fde3_f-4ab1e18f2e748191b60523ecb275e571_b4363c4030c88191b769fe4d9fd2e85e&account_id=personal).
Their intended paths are `tools/even_gap_experiment.py` and
`experiments/even_gap_20261111/`. The publication workspace protects those
paths, so these companion assets are retained in the archive, not added to
the repository by this checkpoint.

Open analytic obligations remain:

1. Prove `F_e=o(HN log N)` uniformly in the requested range, equivalently
   the actual signed error in (7) after the known model term is evaluated.
2. Control the complete boundary at that scale, or prove cancellation jointly
   with it. The existing absolute `H^3 log^2` bound is insufficient in much
   of the range.
3. For a Ramanujan/divisor model, prove actual residual-energy estimates and
   preserve its mixed term; a formal Gram identity alone supplies neither.
4. Combine with the appropriate diagonal asymptotics and discharge the
   separate prime-to-zero transfer, raw-ordinate comparison, and transition-frequency
   obligations before claiming Montgomery's complete pair-correlation limit.

**This work proves neither the even-gap secondary asymptotic nor Montgomery's
pair-correlation conjecture.** It gives a precise remaining even-gap target
and removes the corrected odd exception at the necessary scale.

## 9. Verification

Final verification records and declaration counts are supplied in the
companion theorem catalog and `verification.json`. Checks use the Lean
server's Bazel/BuildBuddy backend. An imported-file check certifies those
saved modules and transitive imports; it is not represented as a complete
project build. The subsequent publication checkpoint validates the complete
integrated project; its terminal result is the publication evidence.
