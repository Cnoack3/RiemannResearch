# Beurling criterion, digamma regimes, and recovered Lean proofs

7 October 2026

**Subsequent verified continuation:** `MellinZetaDigammaFormalization20261007.md`
formalizes the actual Mellin/zeta identities, complete CRT Laurent series, and
all-order positive-real digamma expansion with strict signed remainder. The
five-module verification record below remains historical; analytic coverage
has been updated to distinguish the now-discharged adapters.

This continuation salvages the mathematical work interrupted by `Session terminated`. The Lean service recovered, and the current project already contains repaired versions of the original CRT drafts. Those existing modules are preserved. Five additional modules develop the optimized gain, exact correction transfer, finite signed tail identity, Beurling obstruction, and literal CRT weight bounds.

The verification and publication record is supplied at the end. A mathematical formula discussed here is a Lean theorem only when the coverage table explicitly says so. The remaining arithmetic provider forcing the actual residual errors to zero is still open.

## 1. Beurling's criterion in the physical space

Write
\[
\rho_a(x)=\left\{\frac1{ax}\right\},\qquad
\chi=\mathbf1_{(0,1]}.
\]
The Nyman–Beurling criterion characterizes RH by approximation of this target using fractional-part functions with the usual centering constraint. Báez-Duarte's strengthened formulation permits natural integer parameters in the full space \(L^2(0,\infty;dx)\). This is an established equivalence, not a new RH proof; see [Báez-Duarte, Theorem 1.1](https://arxiv.org/pdf/math/0205003).

The substitution \(x=1/t\) is an isometry onto
\[
H_T=L^2((0,\infty),dt/t^2).
\]
It sends the target to \(\mathbf1_{[1,\infty)}\), and sends the integer atoms to \(\{t/d\}\). The corrected atoms
\[
\phi_d(t)=\{t/d\}-\frac1d\{t\}
\]
vanish below one. On \([j,j+1)\), for integer \(j\ge1\), they are exactly
\[
\phi_d(t)=g_d(j)=\frac{j\bmod d}{d}.
\]
Consequently their complete norm is the literal Pareto norm
\[
\|g\|_P^2=\sum_{j\ge1}\frac{|g(j)|^2}{j(j+1)}.
\]
This identifies the discrete approximation problem with a step subspace of the continuum problem, including every physical tail.

Why is centering compatible with approximation? For a finite raw combination \(F(x)=\sum_d a_d\rho_d(x)\), put \(\alpha=\sum_d a_d/d\). On \(x>1\), \(F(x)=\alpha/x\), whereas the target vanishes. Thus \(|\alpha|\le\|F-\chi\|_2\). Replacing \(F\) by \(F-\alpha\rho_1\) changes its norm by at most \(|\alpha|\|\rho_1\|_2\), which tends to zero along a convergent approximation. The centered atoms are therefore adequate for this target. Restriction to squarefree conductors requires the additional squarefree approximation input discussed in the previous continuation.

### Mellin separation and the critical boundary

For \(\operatorname{Re}s>0\), the corrected atom has the Mellin signature
\[
\int_1^\infty\phi_d(t)t^{-s-1}\,dt
=\frac{\zeta(s)}s\left(d^{-1}-d^{-s}\right).
\]
The apparent singularity at \(s=1\) is removable and gives \(\log d/d\).

For \(\sigma=\operatorname{Re}s>1/2\), define
\[
\ell_s(h)=\int_1^\infty h(t)t^{-s-1}\,dt.
\]
Cauchy–Schwarz gives
\[
|\ell_s(h)|\le\frac{\|h\|_{H_T}}{\sqrt{2\sigma-1}},
\qquad \ell_s(\mathbf1_{[1,\infty)})=\frac1s.
\]
If \(\zeta(s)=0\) with \(\sigma>1/2\), every corrected atom and every legal finite combination is annihilated, but the target is not. Hence
\[
\boxed{\|1-F\|_P^2\ge\frac{2\sigma-1}{|s|^2}}
\]
for every such trial. This explains the necessity direction of the criterion. At \(\sigma=1/2\), the displayed kernel norm diverges; a zero on the critical line does not create this bounded-functional obstruction. The converse is the substantive approximation theorem.

For the discrete step space, the same functional is
\[
\ell_s(g)=\sum_{j\ge1}\frac{g(j)k_s(j)}{j(j+1)},\qquad
k_s(j)=\frac{j(j+1)}s\bigl(j^{-s}-(j+1)^{-s}\bigr).
\]
These Mellin and zeta identifications are now proved for the actual corrected atoms in `ParetoAtomMellinSignature`. `ParetoBeurlingMellinObstruction` instantiates the functional argument with the actual Bochner integral and complete physical Hilbert norm, including the displayed distance bound. The earlier generic consumer remains available.

## 2. Digamma: choose the correct regime

Let \(\psi=\Gamma'/\Gamma\). Its usual large-positive-argument expansion is
\[
\psi(x)\sim\log x-\frac1{2x}
-\sum_{k\ge1}\frac{B_{2k}}{2k\,x^{2k}}
=\log x-\frac1{2x}-\frac1{12x^2}+\frac1{120x^4}-\cdots.
\]
It is a Poincaré expansion: use a finite truncation with a remainder, rather than treating the infinite Bernoulli series as a convergent identity. See [DLMF §5.11](https://dlmf.nist.gov/5.11).

Binet's integral representation, [DLMF 5.9.15](https://dlmf.nist.gov/5.9.E15), gives for \(x>0\)
\[
\psi(x)=\log x-\frac1{2x}
-2\int_0^\infty\frac{t}{(x^2+t^2)(e^{2\pi t}-1)}\,dt.
\]
Expanding the rational denominator a finite number of times gives the exact remainder after \(N\) Bernoulli terms:
\[
R_N(x)=\frac{2(-1)^{N+1}}{x^{2N}}
\int_0^\infty\frac{t^{2N+1}}{(x^2+t^2)(e^{2\pi t}-1)}\,dt.
\]
Its sign is the sign of the first omitted term, and
\[
0<(-1)^{N+1}R_N(x)
<\frac{|B_{2N+2}|}{(2N+2)x^{2N+2}}.
\]
In particular,
\[
\log x-\frac1{2x}-\frac1{12x^2}
<\psi(x)
<\log x-\frac1{2x}-\frac1{12x^2}+\frac1{120x^4}.
\]
Using \(H_n=\psi(n)+\gamma+1/n\) turns these into rigorous harmonic-number bounds. That is the harmonic lower input used by the finite norm-bound consumer formalized below. The subsequent continuation formalizes these positive-real remainder estimates at every finite order, including strict sign and strict first-omitted-term bound, through complete Bernoulli cell integrals. The Binet integral representation itself is a paper representation here; it is not the formal proof route.

### Fixed CRT residues are a small-argument problem

For \(1\le a\le L\), the complete weight of residue \(a\), representing positive sites \(a+kL\), is
\[
\rho_L(a)=\sum_{k\ge0}\frac1{(a+kL)(a+kL+1)}
=\frac{\psi((a+1)/L)-\psi(a/L)}L.
\]
The identity follows by partial fractions from the digamma difference series in [DLMF 5.7.6](https://dlmf.nist.gov/5.7.E6). Every term is positive, and the residues sum to one.

When \(a\) is fixed and \(L\to\infty\), both digamma arguments tend to zero. The convergent small-argument series, obtained from [DLMF 5.7.4](https://dlmf.nist.gov/5.7.E4) and the recurrence, gives
\[
\psi(z)=-\gamma-\frac1z+\zeta(2)z-\zeta(3)z^2+\zeta(4)z^3-\cdots,
\quad 0<z<1.
\]
Therefore
\[
\boxed{\rho_L(a)=\frac1{a(a+1)}
+\frac{\zeta(2)}{L^2}
-\frac{(2a+1)\zeta(3)}{L^3}
+\frac{(3a^2+3a+1)\zeta(4)}{L^4}
+O_a(L^{-5}).}
\]
For this expansion the convergent series is available once \(L>a+1\). The \(O_a\) constant is allowed to depend on the fixed head index.

In the bulk regime, with \(u=a/L\) bounded away from zero, Taylor expansion instead gives
\[
\rho_L(a)=\frac{\psi'(u)}{L^2}+O(L^{-3}),
\]
uniformly for \(u\) in a fixed compact positive interval. Neither regime gives a uniform residue law \(1/L\). At \(a=1\), the complete weight is always at least \(1/2\); this fixed physical head alone prevents replacing the Pareto norm by a uniform CRT norm.

### A positive tail squeeze that does not need digamma

There is also a direct global bound, valid for real \(a,L>0\). For \(m\ge1\),
\[
\frac1{m^2(L+a+1)^2}
\le\frac1{(a+mL)(a+mL+1)}
\le\frac1{m^2L^2}.
\]
The lower bound follows from \(a+mL+1\le m(L+a+1)\); the upper bound follows from both denominator factors exceeding \(mL\). Summing the first \(N\) tail terms yields
\[
\boxed{\frac{H_N^{(2)}}{(L+a+1)^2}
\le \sum_{m=1}^N\frac1{(a+mL)(a+mL+1)}
\le\frac{H_N^{(2)}}{L^2}.}
\]
This entire finite squeeze, including the head-plus-tail decomposition, is proved in Lean. Passing to the convergent infinite sums on paper gives
\[
\frac{\zeta(2)}{(L+a+1)^2}
\le \rho_L(a)-\frac1{a(a+1)}
\le\frac{\zeta(2)}{L^2}.
\]
It supplies a positive global enclosure and immediately recovers
\(\rho_L(a)=1/[a(a+1)]+\zeta(2)L^{-2}+O_a(L^{-3})\).
The displayed global infinite squeeze is a paper consequence of the finite bounds. Separately, the subsequent continuation proves the actual complete CRT digamma identity and convergent Laurent series with analytic zeta coefficients; these are no longer open analytic adapters.

## 3. Optimized gain and exact error transfer

The strongest recovered finite gain formula uses four signed source moments. Put
\[
a=\mu_0,\ b=\mu_1,\ c=\mu_2,\ d=\mu_3,\qquad
\Delta=(a-b)(c-d)-(b-c)^2.
\]
If \(a-b>0\) and \(\Delta>0\), the optimized two-direction gain is
\[
\boxed{q_2=p\left[\frac{a^2}{a-b}
+\frac{(ac-b^2)^2}{(a-b)\Delta}\right].}
\]
Lean proves the exact Schur completion, explicit attaining coefficients, nonnegative extra gain, and Hilbert-space trial identity. The correction to the actual enlarged-space optimizer is retained as its complete squared norm. The scalar moment values, positivity, and actual operator/source pairings must be supplied by the application; they are not an arithmetic divergence estimate.

The numerator is a genuine signed Hilbert variance:
\[
\|w\|^2\left\|Kw-\frac{\langle w,Kw\rangle}{\|w\|^2}w\right\|^2
=\|w\|^2\|Kw\|^2-\langle w,Kw\rangle^2.
\]
The positive centered third-moment quadratic form is also formalized.

For a correction component \(c\), raw vector \(\rho\), and structural vector \(h\) satisfying \(\langle h,\rho\rangle=\langle h,c\rangle\), Lean proves the exact gap
\[
\|\rho\|^2\|h-\alpha\rho\|^2
-(\|\rho\|^2-\|c\|^2)\|h\|^2
=(\|\rho\|^2\alpha-\langle h,c\rangle)^2
+\|h\|^2\|c\|^2-\langle h,c\rangle^2.
\]
Both terms on the right are nonnegative. If the denominator is positive, this gives the sharp structural bound
\[
\|h\|^2\le
\frac{\|\rho\|^2}{\|\rho\|^2-\|c\|^2}\|h-\alpha\rho\|^2.
\]
Lean also proves an equality witness, the orthogonal split, and scalar consumers translating a supplied complete trapezoidal norm identity and positive tail bounds into finite norm enclosures. Identifying the named constants \(\log(2\pi)-\gamma\) and assembling the infinite correction energy remain analytic work. The all-order positive-real digamma asymptotic and sharp signed remainder are now formalized in the subsequent continuation.

The finite signed source identity keeps its boundary:
\[
P_a(n)=-\sum_{j<n}a_j,\qquad
\sum_{j<N}(T_j-T_{j+1})P_a(j+1)
=-\sum_{j<N}a_jT_j+T_N\sum_{j<N}a_j.
\]
The old source in a finite transported-source sum is also kept. Infinite orthogonality does not authorize discarding it at every finite cutoff.

## 4. Exact formalization scope

All new modules use focused Mathlib imports. There are 64 theorem declarations in total.

| Module | Theorems | Kernel-checked content | Inputs still required |
|---|---:|---|---|
| Analysis/FiniteKrylovGain.lean | 18 | Exact two-direction Schur completion, coefficients, moment bonus, signed variance and centered third moment, Hilbert trial and full optimizer-square adapters | Actual stage moment and pairing instantiation; arithmetic cumulative gain budget |
| Analysis/StepCorrectionGain.lean | 12 | Sharp generic correction transfer, equality witness, orthogonal split, finite norm-bound and tail consumers | Actual step projection constants and complete trapezoidal norm assembly; harmonic/digamma bounds are now supplied |
| Analysis/FiniteSignedTailCharge.lean | 10 | Signed finite Abel formula with endpoint, finite tails, exact transported-source splitting | Infinite convergence, endpoint decay, arithmetic cancellation estimates |
| Analysis/BeurlingAnnihilator.lean | 9 | Positive quantitative functional separation, legal-sequence nonconvergence, span and closed-span obstruction | Discharged by the actual Mellin/zeta continuation; approximation converse remains open |
| Analysis/FiniteCRTWeightBounds.lean | 15 | Literal positive CRT terms, physical head, strict domination, pointwise and finite tail squeeze | Digamma/zeta identification and convergent CRT expansion now supplied; application estimates retain their domains |

No RH proof, unconditional arithmetic gain divergence, or formalized new Nyman–Beurling equivalence is claimed. The subsequent continuation does prove all-order positive-real digamma asymptotics and the sharp strict remainder.

## 5. Verification record

All five modules were compiled together against the current project dependency environment. The final coherent verification returned `verified: true`, exit code 0, in 4.259 seconds. All 64 theorem declarations elaborated. The remaining warnings are tactic-style linter messages, with no compilation errors.

- Verification job: `job_PHLj_gAqDah1WPi_37RmdOTm8PzKYrLt`.
- Coherent Lean source SHA-256: `49e250df725b0a217d60b5b54fb221673d67d3681fc3b6c06d0061e65e58e20f`.
- Repository base: `64a5c2e11b90a4eda4552b4961bc843416687f21`.
- Source scan: no `sorry`, `admit`, custom `axiom`, `unsafe`, or unqualified `import Mathlib` in any new module.

Eight selected `#print axioms` reports were checked: `moment_two_direction_gain_bonus`, `scaled_two_direction_optimizer_gain`, `correction_transfer_sq`, `trapezoid_two_moment_norm_bound`, `finite_abel`, `transported_source_split`, `target_not_mem_closure_span`, and `residuePrefix_two_sided`. Every report contains only `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx` or a project axiom.

The project exports and theorem catalog are updated with the five modules. Publication is performed through the project's single push-enabled validation checkpoint, rather than a separate manual commit or push.

The initial interruption was an execution-service failure. After recovery, real Lean diagnostics identified ordinary proof repairs: nonzero base norms were needed for division by squared norms; `prefix` was a reserved identifier; real reciprocal definitions needed a noncomputable section; and functional norm positivity was proved directly from its quantitative bound. These repairs do not introduce assumptions or proof holes.

This note supplements `RH_CRT_Optimized_Gains_and_Uniform_Obstruction_20261007.md`. Its historical statement that Lean was unavailable describes the earlier attempt; the new verification record supersedes that execution status for the modules listed here.
