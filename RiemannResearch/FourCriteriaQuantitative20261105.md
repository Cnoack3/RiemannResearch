# Quantitative displacement regularity: repository comparison and stronger paper criterion

Status: paper derivation, 5 November 2026 UTC. No Lean jobs were submitted by the author of this note. Existing source declarations below were read on GitHub; the stronger Vinogradov–Korobov provider and its complete application have not been kernel checked here. No unconditional proof of RH is claimed and no claim of novelty in the literature is made.

## 1. What is already in the repository

The current `RiemannResearch/RH/QMobiusStretchedEnergy.lean` contains:

- `exactHead_eventual_stretched_energy` and `exactHead_error_eventual_stretched_energy`, with saving `exp(-a * logProductPower (1/11) (6 + log N))`;
- `exactHead_eventual_log_power_energy` and `exactHead_error_eventual_log_power_energy`, giving every fixed logarithmic saving;
- `exactHead_energy_of_uniform_mertens_log`, a more flexible conditional finite bound described below.

`Analysis/StretchedExponentialBounds.lean` defines `logProductPower beta s = (s * log s)^beta`. Thus the already formalized stretched profile is

\[
\Psi(N)=((6+\log N)\log(6+\log N))^{1/11}.
\]

`RH/QSquarefreeStretchedDisplacement.lean` already transfers this profile to the actual displacement. In particular, it contains `exists_stretched_displacement_tail_escape`, `exists_residual_zero_iff_frequently_bounded_stretched_displacement_tail`, and `exists_critical_stretched_displacement_tail_criterion`. The current repository also has actual-displacement polylogarithmic results in `QSquarefreeLogDisplacement.lean`, as identified by the coordinating agent. Therefore **polylogarithmic weakening is inherited work, not a new result of this investigation**.

The strengthened paper profile below is

\[
\Phi(N)=(\log N)^{3/5}(\log\log N)^{-1/5},\qquad N>e.
\]

It is strictly larger asymptotically: `Phi(N)/Psi(N)` tends to infinity. Therefore `exp(-c Phi(N))` is a stronger energy saving and allows a weaker upper-bound requirement on displacement tails than the existing `1/11` profile. This comparison concerns the inspected declarations; it is not an exhaustive claim that no other repository file contains a related statement.

GitHub sources inspected:

- https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QMobiusStretchedEnergy.lean
- https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QSquarefreeStretchedDisplacement.lean
- https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/StretchedExponentialBounds.lean
- https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QMobiusExactHead.lean

## 2. Primary analytic sources and exact scope

Ethan Simpson Lee and Nicol Leong, *New explicit bounds for Mertens function and the reciprocal of the Riemann zeta function*, arXiv:2208.06141v5, 9 September 2026, Theorem 1.1 equation (12), provides an unconditional explicit bound of the form

\[
|M_\mu(x)|\ll x\log x\exp(-a\Phi(x)),\qquad a>0.
\]

Reducing `a` absorbs the logarithm, giving `|M_mu(x)| <= C x exp(-b Phi(x))` for some `b,C>0` and all sufficiently large `x`. This source is a research preprint; its journal publication was not established here. It gives a modern explicit form of the classical Vinogradov–Korobov consequence.

Source: https://arxiv.org/html/2208.06141v5 (Theorem 1.1, equation (12)); https://arxiv.org/abs/2208.06141.

Terence Tao, *A remark on partial sums involving the Mobius function*, arXiv:0908.4323v5, proves the exact global inequality

\[
\left|\sum_{n\le x}\frac{\mu(n)}n\right|\le1.
\]

The theorem is more general, allowing prime-supported multiplicative semigroups; taking all primes supplies exactly the inequality needed here. Its abstract also gives convergence to zero in the all-prime case using PNT. Thus using the constant one in the bound for the canonical exact heads is justified, including small cutoffs.

Source: https://arxiv.org/abs/0908.4323.

The final squarefree closure connection is Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*, Remark 8 (direct sequence-space statement), together with the equivalent-weight observation after Theorem 1. Remark 4 is its Hardy-space predecessor.

Source: https://arxiv.org/pdf/math/0607733.

## 3. Fastest formalization route: reuse the existing uniform envelope theorem

Let `Z=zeta(2)` and retain the actual canonical Q exact head

\[
E_N=-\sum_{k\le N}\mu(k)g_k+(N+1)m_Ng_{N+1},
\quad m_N=\sum_{k\le N}\mu(k)/k.
\]

The inspected declaration `QMobiusStretchedEnergy.exactHead_energy_of_uniform_mertens_log` states, for positive `N`, positive `epsilon <= 1`, `epsilon*(1+log(1/epsilon)) <= 1/2`, and the explicit assumption `|M_mu(y)| <= epsilon*y` for every real `y>=N`, that

\[
\frac{\|E_N\|_Q^2}{N}
\le\frac2Z\left(\frac3N+260\epsilon(1+\log(1/\epsilon))\right).
\tag{1}
\]

From Lee–Leong choose `epsilon_N=C exp(-b Phi(N))`. The function `Phi` is eventually increasing, so this is a uniform bound for every `y>=N`. The smallness hypotheses in (1) hold eventually. Since `Phi(N)` tends to infinity and `log Phi(N)=o(Phi(N))`, every fixed `0<c<b` gives

\[
\epsilon_N(1+\log(1/\epsilon_N))=O(e^{-c\Phi(N)}).
\]

Consequently

\[
\|E_N\|_Q^2=O(1+N e^{-c\Phi(N)}),\qquad
\|1-E_N\|_Q^2=O(1+N e^{-c\Phi(N)}).
\tag{2}
\]

The error estimate follows from `||1-E_N||^2 <= 2+2||E_N||^2`. Since `Phi(N)=o(log N)`, the quantity `N exp(-c Phi(N))` tends to infinity and absorbs the additive constant:

\[
\boxed{\|1-E_N\|_Q^2\ll N e^{-c\Phi(N)}}.
\tag{3}
\]

This route already has a verified algebraic/energy consumer. The main new formal provider required is the stronger quantitative Mertens estimate, together with elementary asymptotics of its profile. Merely citing Lee–Leong does not supply this Lean proof. A conditional Lean declaration parameterized by the uniform envelope would remain conditional and should be labeled accordingly.

## 4. Independent elementary energy derivation

For completeness, here is a separate derivation of the same profile from finite Mertens data. Set

\[
S_N=\max_{1\le k\le N}|M_\mu(k)|,\qquad R_N=S_N/N.
\]

Since `M_mu(1)=1` and `|M_mu(k)|<=k`, one has `1/N<=R_N<=1`. Discrete partial summation and the variation of `t -> {n/t}` give, for integers `1<=K<=N`,

\[
\left|\sum_{K<k\le N}\mu(k)\{n/k\}\right|
\le S_N(3+2n/K).
\]

Indeed, the smooth variation is at most `n/K`, the jumps contribute at most `n/K+1`, and the two endpoint terms are bounded by `2 S_N`. The first `K` summands contribute at most `K`, while the correction contributes at most `2N|m_N|`. Thus

\[
|E_N(n)|\le K+S_N(3+2n/K)+2N|m_N|.
\tag{4}
\]

Choose `K=ceil(N R_N^(1/4))` and `T=R_N^(-1/2)`. Here `1<=K<=N` and `K<=2N R_N^(1/4)`. For `N<n<=TN`, equation (4) gives

\[
|E_N(n)|\ll N(R_N^{1/4}+|m_N|).
\]

The corresponding Q energy is `O(N(sqrt(R_N)+|m_N|^2))`. On the infinite tail `n>TN`, use the exact global bound `|E_N(n)|<=2N`: the conductor-one term vanishes, so the first sum is at most `N-1`, and Tao's `|m_N|<=1` makes the correction at most `N+1`. The tail energy is therefore `O(N/T)=O(N sqrt(R_N))`. The exact initial head contributes at most one. Hence

\[
\boxed{\|1-E_N\|_Q^2\ll
N(\sqrt{R_N}+|m_N|^2+N^{-1})}.\tag{5}
\]

The quantitative Mertens estimate, splitting the maximum at `sqrt(N)`, gives `R_N << exp(-b_1 Phi(N))`. Partial summation and `sum mu(k)/k=0` give

\[
m_N=M_\mu(N)/N-\int_N^\infty M_\mu(t)t^{-2}\,dt
\ll e^{-b_2\Phi(N)}
\]

for some positive constants `b_1,b_2`. Substituting into (5) proves (3), with a possibly worse exponential constant. This independent proof explains the full infinite-tail control; it is less efficient for Lean than reusing (1).

## 5. Strengthened annihilator and displacement criteria

Let `u in V^perp`. Choose by Bertrand a prime `M<p<=2M` and put `L=p-1`. The canonical head `E_L` is squarefree legal and equals one on `1,...,L`. Thus

\[
|\langle1,u\rangle_Q|^2
\le\|1-E_L\|_Q^2\,\|T_Mu\|_Q^2.
\tag{6}
\]

As `M<=L<2M`, equation (3) gives an absolute `c>0` and a constant `C` with

\[
|\langle1,u\rangle_Q|^2
\le C M e^{-c\Phi(M)}\|T_Mu\|_Q^2
\]

eventually. If the mean is nonzero, for every `0<c'<c` this forces

\[
M e^{-c'\Phi(M)}\|T_Mu\|_Q^2\longrightarrow\infty.
\tag{7}
\]

Apply (7) to the actual Schur witness `w=Br_P-d`. Its positive mean is

\[
\langle1,w\rangle_Q=\langle r,Br\rangle_Q+\|d\|_P^2/Z,
\]

which vanishes precisely when `r=0`. Also `Br_P in c_0`; hence `M||T_M Br_P||^2` tends to zero. The reverse triangle inequality transfers (7) to `d` whenever `r!=0`. Therefore for some absolute `c'>0`,

\[
\boxed{\mathrm{RH}\iff
\liminf_{M\to\infty}M e^{-c'\Phi(M)}
\sum_{n>M}\frac{|d(n)|^2}{Zn^2}<\infty.}
\tag{8}
\]

The forward direction uses `d=0` under RH. The reverse direction is exactly (7) and faithfulness of the witness. The arithmetic upper bound in (8) is still open.

An accessible consequence is

\[
\boxed{\log(2+|d(n)|)=o(\Phi(n))\Longrightarrow\mathrm{RH}.}
\tag{9}
\]

To prove it, for every `epsilon>0` the assumption gives `|d(n)|<=C_epsilon exp(epsilon Phi(n))`. Because the derivative of `t -> Phi(exp t)` tends to zero, for all sufficiently large `M` and every `n>=M`,

\[
e^{2\epsilon\Phi(n)}
\le e^{2\epsilon\Phi(M)}(n/M)^{1/2}.
\]

Thus `||T_M d||^2 << M^(-1) exp(2 epsilon Phi(M))`. Taking `2 epsilon<c'` proves (8). In particular the still-open condition `d(n)=O(exp(sqrt(log n)))` is enough, and is substantially weaker than the boundedness criteria of the supplied document. It is also weaker than a bound using a sufficiently small multiple of the repository's existing `1/11` profile. This is a paper improvement of the inspected rate, not an unconditional estimate on d.

## 6. Consequences already covered at weaker rates

Equation (3) implies every logarithmic saving, but those are already formalized. Likewise the criterion

\[
\exists A\ge0:\quad
\liminf_{M\to\infty}\frac M{(\log M)^A}\|T_Md\|_Q^2<\infty
\]

and fixed-polylog physical upper bounds belong to the inherited logarithmic program. They should be presented as recovered consequences, not new results. The averaged finite-head relaxation

\[
\sum_{n\le M}|d_{J_k}(n)|^2\le C M(\log(eM))^A
\quad(1\le M\le H_k)
\]

for cofinal stages and heads follows by passing to fixed finite sums, then dyadic tail summation. Its novelty status requires an exact repository comparison; this note does not claim it is absent elsewhere.

## 7. Honest remaining gap

The classical Mertens estimate controls the explicit testing family E_N. It does not control the particular orthogonal-projection displacement d. The strengthened tail criterion and pointwise condition retain an RH-equivalent arithmetic obligation. Hilbert norm boundedness, compactness of the Schur operator, and the unconditional statement d(n)=o(n) do not supply (8) or (9).
