# Prime logarithms and valuations: exact Möbius inversion and the remaining Hilbert-space problem

Prepared 21 October 2026 for the RiemannResearch continuation.

**Lean verification status.** The coherent arithmetic/closure candidate passed server job `job_xR-gOGP0D4dh3vKjAFu3pVeXUJGenHEY` (`verified=true`, exit 0; server elapsed 109.866 seconds). The final saved-module import check passed `job_JnLIITc1oOKShH3ulH5N7q-vDsXqqug7` (`verified=true`, exit 0; 185.662 seconds), including both modules below and the seven sampling modules. The inspected arithmetic identities and closure obstruction depend only on `propext`, `Classical.choice`, and `Quot.sound`. Publication remains gated by the final source-audit and aggregate/changed-module checkpoint; the final response and containing Git history identify its receipt.

The mathematical proofs below are self-contained ordinary arguments. The accompanying Lean source has the following precise scope:

| Result | Formalization scope |
|---|---|
| Prime-power jump indicator, divisor-sum formula, Möbius inversion, telescoping, and cumulative double divisor sum | RiemannResearch/NumberTheory/PrimeLogValuationMobius.lean; subject to the status above |
| Any Q-Hilbert representative of the actual prime valuation lies outside closureWithConstants | RiemannResearch/RH/PrimeValuationClosureObstruction.lean; subject to the status above |
| Regrouping into floor-cutoff sums, factorial rewriting, cumulative-summation unboundedness, and the naive-cutoff asymptotic | Ordinary proved consequences in this note; no new Lean verification claimed |

The first combined saved-module import check reached its 180-second wall limit (`job_u4CfcLL2-dlJkhA8Bsrtmj1rw-vJe63F`); it is not counted as verification. The successful longer-limit check is recorded above. Server elapsed times include dependency preparation and compilation, not solely kernel time.

Neither membership of \(F_p\) in the legal closure nor RH is proved here. The research agenda begins with the remaining norm and legality estimates, rather than proposing the same finite arithmetic bridge again.

## 1. Definitions and exact identities

Fix a **prime** \(p\). For integers \(n\ge1\), put

\[
F_p(n)=\lfloor\log_p n\rfloor
       =\sum_{k\ge1}\mathbf1_{\{p^k\le n\}},\qquad F_p(0)=0,
\]
\[
v_p(n)=\max\{k\ge0:p^k\mid n\},\qquad
a_p(n)=\Delta F_p(n)=F_p(n)-F_p(n-1).
\]

All divisor and cutoff sums are over positive integers, and all sums at a fixed integer are finite. The jump function is

\[
a_p(n)=\mathbf1_{\{n=p^k\text{ for some }k\ge1\}}.
\]

The inclusion-exclusion connection is exact:

\[
\boxed{v_p(n)=\sum_{d\mid n}a_p(d)
              =\sum_{d\mid n}\Delta F_p(d).}
\tag{1}
\]

Consequently, with \(\mu\) the Möbius function,

\[
\boxed{\Delta F_p(n)=\sum_{d\mid n}\mu(d)v_p(n/d).}
\tag{2}
\]

Cumulative summation gives two equivalent reconstructions:

\[
\boxed{F_p(n)=\sum_{d\le n}\mu(d)
       \sum_{m\le\lfloor n/d\rfloor}v_p(m)
       =\sum_{d\le n}\mu(d)\,
          v_p\!\left(\lfloor n/d\rfloor!\right).}
\tag{3}
\]

Thus the floor logarithm and the valuation are related by **Dirichlet Möbius inversion followed by cumulative summation**. They are not the same random variable.

For clarity, the cumulative formula included in the new arithmetic Lean module is the double divisor sum

\[
F_p(n)=\sum_{k=1}^{n}\sum_{d\mid k}\mu(d)v_p(k/d).
\tag{3a}
\]

The reindexing of (3a) into the two floor/factorial expressions in (3) is proved below as ordinary finite algebra. It is not included in the new module's claimed verification scope.

### Proof

The prime powers dividing \(n\) are precisely

\[
p,p^2,\ldots,p^{v_p(n)},
\]

so counting them proves (1), including \(n=1\), when both sides vanish. In Dirichlet-convolution notation, (1) is \(v_p=\mathbf1*a_p\). Since \(\mu*\mathbf1=\varepsilon\), inversion gives (2). Here \(\varepsilon(1)=1\) and \(\varepsilon(n)=0\) for \(n>1\).

Now telescope \(F_p(n)=\sum_{k=1}^n\Delta F_p(k)\), substitute (2), and reindex \(k=dm\):

\[
\sum_{k\le n}\sum_{d\mid k}\mu(d)v_p(k/d)
=\sum_{d\le n}\mu(d)\sum_{m\le\lfloor n/d\rfloor}v_p(m).
\]

Finally, additivity of the prime valuation under multiplication gives
\(\sum_{m=1}^Nv_p(m)=v_p(N!)\). This proves (3).

For example, at \(p=2,n=6\), the factorial formula gives

\[
F_2(6)=v_2(6!)-v_2(3!)-v_2(2!)+v_2(1!)=4-1-1+0=2.
\]

## 2. What these transforms say under the Q measure

Use

\[
Q(n)=\frac1{\zeta(2)n^2},\qquad
\|f\|_Q^2=\frac1{\zeta(2)}\sum_{n\ge1}\frac{|f(n)|^2}{n^2}.
\]

Both \(v_p\) and \(F_p\) are in the ambient Q Hilbert space: \(0\le v_p(n)\le F_p(n)\le\log_p n\), and the logarithmic square is summable against \(n^{-2}\).

The variables \(v_p\), for distinct primes, are independent under Q, with

\[
Q(v_p=k)=(1-p^{-2})p^{-2k},\qquad
\mathbb E_Qv_p=\frac1{p^2-1},\qquad
\mathbb E_Qv_p^2=\frac{p^2+1}{(p^2-1)^2}.
\]

For a finite set of primes and prescribed exponents, write \(n=(\prod_p p^{k_p})m\), with \(m\) coprime to those primes. Finite inclusion-exclusion in \(\sum m^{-2}\) gives the joint mass \(\prod_p(1-p^{-2})p^{-2k_p}\), proving the independence assertion. The displayed moments then follow from the geometric series.

This independence is useful for ambient moment calculations. It does not imply that the transforms in (1)--(3) preserve any legal approximation space.

### Cumulative summation is unbounded

Define \(Cf(n)=\sum_{k=1}^nf(k)\), initially on finitely supported sequences, and let \(e_M=\mathbf1_{\{n=M\}}\), \(M\ge1\). Then \(Ce_M=\mathbf1_{\{n\ge M\}}\), so

\[
\frac{\|Ce_M\|_Q^2}{\|e_M\|_Q^2}
=M^2\sum_{n\ge M}\frac1{n^2}
\ge M^2\sum_{n=M}^{2M-1}\frac1{n(n+1)}
=\frac M2.
\tag{4}
\]

The full telescoping tail even gives the stronger lower bound \(M\). Therefore cumulative summation has no bounded extension from these finitely supported inputs to the whole Q Hilbert space. Indeed, the ambient vector \(1\) is in \(L^2(Q)\), but \(C1(n)=n\) is not.

Equation (4) is an **ambient** operator obstruction. It does not exclude a specially restricted domain, a compensated operator, or a target-specific construction. It does rule out silently applying cumulative summation to a convergent Hilbert-space approximation without a new estimate. No boundedness claim for the Dirichlet inversion operator is made here either.

## 3. The valuation itself is not in the squarefree legal closure with constants

Let

\[
\mathcal H_{\rm sf}=\overline{\operatorname{span}\{g_d:d\ge2,\ d\text{ squarefree}\}}^{L^2(Q)},
\qquad g_d(n)=\frac{n\bmod d}{d},
\]
\[
\mathcal C_{\rm sf}=\overline{\mathcal H_{\rm sf}+\mathbb R1}.
\]

The established squarefree jump relations require

\[
\Delta f(a^k)=\Delta f(a)\qquad(a\ge2,\ k\ge1)
\tag{5}
\]

for every \(f\in\mathcal C_{\rm sf}\). For the valuation,

\[
\Delta v_p(p)=v_p(p)-v_p(p-1)=1,
\]
\[
\Delta v_p(p^2)=v_p(p^2)-v_p(p^2-1)=2.
\]

Thus the ordinary consequence of (5) is

\[
\boxed{v_p\notin\mathcal C_{\rm sf}.}
\tag{6}
\]

This direct obstruction applies even though \(v_p\) is an especially simple independent coordinate under Q. The accompanying Lean obstruction is stated for **any Q-Hilbert vector whose positive physical coordinates equal the actual valuation**; it does not presuppose a new canonical Hilbert-space construction of that valuation. Its verification status is stated at the top. By contrast, \(\Delta F_p(p^k)=1\) for every \(k\ge1\), so this particular obstruction does not exclude \(F_p\). Passing the jump tests is necessary, not a proved sufficient condition for legal membership.

## 4. The transform cancellation worth retaining

For \(\Re s>1\), absolute convergence gives

\[
\sum_{n\ge1}\frac{v_p(n)}{n^s}
=\frac{\zeta(s)}{p^s-1},\qquad
\sum_{n\ge1}\frac{a_p(n)}{n^s}=\frac1{p^s-1}.
\tag{7}
\]

Möbius inversion removes the factor \(\zeta(s)\). The normalized discrete Mellin transform of \(F_p\) is correspondingly

\[
\Phi_s(F_p)
=\sum_{n\ge1}F_p(n)\bigl(n^{-s}-(n+1)^{-s}\bigr)
=\frac1{p^s-1}.
\tag{8}
\]

The existing target construction extends (8) to \(\Re s>1/2\). In (7), the first series is the **ordinary Dirichlet series of \(v_p\)**; it is not \(\Phi_s(v_p)\). Confusing these transforms would lose the finite-difference operation and produce an incorrect annihilation argument.

The cancellation in (7) is an exact arithmetic mechanism. It supplies neither a norm bound for the inverse transform nor legal approximants to \(F_p\). In particular, division by a displayed zeta factor is not a proof of zeta nonvanishing.

### A finite-cutoff hazard

The naive Möbius truncation

\[
T_{D,p}(n)=\sum_{d\le D}\mu(d)\,
              v_p\!\left(\lfloor n/d\rfloor!\right)
\]

agrees with \(F_p(n)\) when \(n\le D\), but need not even belong to \(L^2(Q)\). Legendre's factorial formula yields, for fixed \(D\),

\[
T_{D,p}(n)=\frac{n}{p-1}\sum_{d\le D}\frac{\mu(d)}d
          +O_{D,p}(\log(n+1)).
\tag{9}
\]

Indeed, \(v_p(N!)=\sum_{k\ge1}\lfloor N/p^k\rfloor\). The nonzero floors differ from their arguments by less than one each, their number is \(O_p(\log(N+1))\), and the remaining geometric tail is \(O_p(1)\). Hence \(v_p(N!)=N/(p-1)+O_p(\log(N+1))\); substituting \(N=\lfloor n/d\rfloor\) and summing over the fixed finite set \(d\le D\) proves (9).

Whenever the displayed reciprocal charge is nonzero, the linear term forces its Q norm to diverge. Thus a finite exact head is not enough. Cancelling that slope is necessary, and showing that the repaired vector uses only squarefree legal conductors is another separate obligation.

## 5. Coordinated research agenda

1. **Build a norm-controlled compensated transform.** Start from (3a), expose the reciprocal charge in (9), and remove the linear term before studying complete-Q energy. Cancellation of the slope alone is insufficient: obtain a bound uniform along a growing-head family, retaining every infinite tail and signed cross term.

2. **Prove actual legality of the repaired family.** Group arithmetic terms before estimating them. Each proposed approximant must belong to the actual squarefree span, or to the explicitly chosen constant enlargement. Neither independent valuations nor an ambient boundedness estimate supplies this membership. Do not replace the original inversion by unjustified termwise legal approximations.

3. **Use the transform cancellation in the complete Gram form.** Derive exact correlations and energy for the compensated family, then compare it with the raw-sieve and signed-row obstructions already in the repository. If it reduces to an excluded family, identify that explicitly and change the construction. If it yields new legal directions, feed their signed correlations into the actual CRT/screened-gain framework.

4. **Reach a quantified RH endpoint.** A uniformly bounded legal family fitting every finite head of \(F_p\) would put \(F_p\) in the legal closed space. For the constant-enlarged space, the established simultaneous memberships \(F_2,F_3\in\mathcal C_{\rm sf}\) would imply RH. An alternative endpoint is an independent lower bound for actual legal gains, or a bounded exact-head energy budget for the constant target. The goal is one of these quantified estimates, not merely another equivalent formulation of membership.

5. **Formalize the remaining supporting algebra when used.** The floor-cutoff/factorial regrouping, the exact cumulative-summation obstruction (4), and the cutoff asymptotic (9) remain ordinary proofs in this note. Formalize those that the chosen construction actually needs. Reuse the two new modules according to their verified status rather than reproving their indicator, inversion, and closure-obstruction statements.

The productive new link is the exact Möbius transform and its signed cancellations. Independence of valuations supplies useful moment data, but cannot replace the missing boundedness and legality estimates.
