# Tail capacity: literature audit and primorial sieve obstruction

Section numbers follow the supplied tail-capacity handoff. The mathematical proofs and formalization boundaries below are part of the same continuation.

---

## 24. Literature audit: what the papers and Lean actually imply

**Audit date: 19 September 2026.** The reviewed literature and the checked Lean endpoint do **not** give an unconditional proof of RH. They give a rigorous route to RH once the actual capacity divergence is supplied. The missing estimate is a mathematical obligation; completing the formalization of the cited classical theorems would not itself discharge it.

### 24.1 The discrete space already has an exact literature identification

Bhaskar Bagchi's [*On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*, Theorem 1](https://arxiv.org/pdf/math/0607733) uses exactly

\[
H=\left\{a:\sum_{k\ge1}\frac{|a(k)|^2}{k(k+1)}<\infty\right\},
\qquad \gamma_d(k)=\{k/d\}.
\]

Its conclusion is the equivalence of RH, membership of the constant sequence in the closed residue span, and density of that span in \(H\). Here \(\gamma_1=0\) and \(\gamma_d=g_d\) for \(d\ge2\). Although Bagchi works over the complex numbers, approximation of a real target by real atoms transfers to the real span by taking real parts, which cannot increase the error.

Thus the correspondence is literal, with no change of weight or dictionary. Combining that theorem with this handoff's point-target and capacity identities gives the mathematical equivalence

\[
\boxed{\mathrm{RH}\iff\mathbf1\in W\iff e_1\in W
\iff\delta_N\to0\iff\tau_N\to\infty.}
\tag{24.1}
\]

This is a direct literature justification of the converse used in Section 9. It does not assert any of the equivalent conditions unconditionally. No novelty is claimed for the discrete density criterion.

### 24.2 Hypothesis audit of the relevant estimates

| Source | What is proved | Consequence for this handoff |
| --- | --- | --- |
| [Báez-Duarte, Theorem 1.1](https://arxiv.org/pdf/math/0202141) | RH is equivalent to approximation by integer dilates in the strong Nyman–Beurling criterion. | Classifies the target; the direction producing approximants assumes RH. |
| [Bagchi, Theorems 1–2](https://arxiv.org/pdf/math/0607733) | The discrete weighted residue criterion and its Hardy-space version are equivalent to RH. | Applies directly to this \(H,V,W\); it supplies no unconditional density estimate. |
| [Burnol, Theorem 1.3](https://arxiv.org/pdf/math/0103058) | A logarithmic lower bound for the approximation error, with squared zero multiplicities. | Supports Section 19's rate obstruction, hence an upper envelope for capacity. It does not force capacity to grow. |
| [Burnol, Theorems 1.3–1.4](https://arxiv.org/pdf/math/0202166) | Shifted reciprocal-zeta estimates and Möbius Dirichlet-polynomial estimates under RH. | These cannot be used as unconditional providers in a proof of RH. |
| [Bettin–Conrey–Farmer, Theorem 1](https://arxiv.org/pdf/1211.5191) | A sharp \(1/\log N\) error asymptotic for a smoothed Möbius polynomial, assuming RH and a bound on reciprocal zeta derivatives. | The theorem's hypotheses already include RH. Its error is a Dirichlet-polynomial approximation error; a finite normalization comparison is also needed before treating it as this note's \(\delta_N\). |

For the last row the additional hypothesis is

\[
\sum_{|\Im\rho|\le T}\frac1{|\zeta'(\rho)|^2}
\ll T^{3/2-\eta}\qquad\text{for some }\eta>0.
\]

It in particular requires simple zeros. The conclusion concerns the choice
\(\sum_{n\le N}\mu(n)(1-\log n/\log N)n^{-s}\).

Two apparent shortcuts therefore remain invalid: using a theorem whose approximating conclusion assumes RH to establish RH, or using a lower bound on error as though it were an upper bound tending to zero. Even an eventual bound of the form \(\tau_N\le C\log N\) is compatible with bounded capacity.

### 24.3 What was checked in the live Lean project

The audit opened the published base
`d5da91fe163bc7a091eaeb033dc4b06517229158` and rechecked the actual declarations with their ordinary imports. The successful audit job was
`job_81-NxzbyYzIRaTmWCX95zzLlPkJRXq5d` (exit code 0, 3.402 seconds).

In namespace
`RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity`, Lean printed:

```lean
def TailCapacityDivergence : Prop :=
  Filter.Tendsto tailCapacity Filter.atTop Filter.atTop

riemannHypothesis_of_tailCapacity_tendsto
  (h : TailCapacityDivergence) : RiemannHypothesis

tailCapacity_bounded_iff_exists_certificate :
  (∃ C, ∀ n, tailCapacity n ≤ C) ↔
    ∃ z, RiemannResearch.RH.Pareto.IsResidueTailCertificate z
```

The audit also checked capacity monotonicity and the equivalence of capacity divergence with point-error convergence. The RH conclusion is Mathlib's actual `RiemannHypothesis`, rather than a newly introduced proposition with that name.

The principal implication and certificate equivalence use only `propext`, `Classical.choice`, and `Quot.sound`. This axiom report does not remove the displayed argument `h`. No unconditional provider for `TailCapacityDivergence` was obtained.

## 25. An explicit CRT sieve family: correct coordinates, divergent energy

The dual-certificate route in Section 21 suggests applying finite Möbius sieves and passing to a limit. The following calculation tests a concrete version of that idea without replacing the signed objective by coefficient bounds. It gives a rigorous obstruction to this particular family. The calculation is included with its proof; no claim of mathematical priority is made.

For an integer \(X\ge2\), define

\[
P_X=\prod_{p\le X}p,\qquad
c_X=\prod_{p\le X}\left(1-\frac1p\right),\qquad
\Phi_X(k)=\#\{1\le j\le k:\gcd(j,P_X)=1\}.
\]

Let \(g_1=0\) and form the finite legal vector

\[
F_X=-\sum_{d\mid P_X}\mu(d)g_d\in V_{P_X}.
\tag{25.1}
\]

**Proposition 25.1 (exact sieve identity).** For every integer \(k\ge1\),

\[
\boxed{F_X(k)=\Phi_X(k)-c_Xk.}
\tag{25.2}
\]

**Proof.** Finite inclusion–exclusion gives

\[
\Phi_X(k)=\sum_{d\mid P_X}\mu(d)\lfloor k/d\rfloor,
\qquad
c_X=\sum_{d\mid P_X}\frac{\mu(d)}d.
\]

Substitute \(g_d(k)=k/d-\lfloor k/d\rfloor\) into (25.1). All sums are finite. \(\square\)

For \(1\le k\le X\), every integer \(j\in\{2,\ldots,k\}\) has a prime divisor at most \(X\). Consequently

\[
\boxed{F_X(k)=1-c_Xk\quad(1\le k\le X).}
\tag{25.3}
\]

Also \(c_X\to0\): the reciprocal finite Euler product is the sum of \(1/n\) over all positive integers whose prime factors are at most \(X\), so

\[
\frac1{c_X}\ge H_X\longrightarrow\infty.
\tag{25.4}
\]

Thus \(F_X(k)\to1\) for every fixed \(k\). For every fixed modulus \(d\), its coefficient also eventually equals \(-\mu(d)\): every fixed squarefree \(d\) eventually divides \(P_X\), and nonsquarefree coefficients are zero throughout.

Nevertheless the approximation fails in the Hilbert norm. Put
\(A_X=\sum_{k=1}^X1/(k+1)=H_{X+1}-1\). The entire initial-segment error is exactly

\[
\boxed{
\sum_{k=1}^X\frac{(1-F_X(k))^2}{k(k+1)}
=c_X^2(X-A_X)
=c_X^2(X+1-H_{X+1}).
}
\tag{25.5}
\]

In particular,

\[
\|\mathbf1-F_X\|_H^2
\ge c_X^2(X+1-H_{X+1})\ge\frac12Xc_X^2.
\tag{25.6}
\]

For completeness the initial-segment norm itself is

\[
\boxed{
\sum_{k=1}^X\frac{F_X(k)^2}{k(k+1)}
=\frac{X}{X+1}+c_X^2X-(2c_X+c_X^2)(H_{X+1}-1).
}
\tag{25.7}
\]

These identities retain the actual signed combination before squaring. The lower bound uses only nonnegativity of the omitted physical tail.

### 25.1 An elementary bound suffices to prove divergence

No RH, prime number theorem, or sharp Mertens estimate is required. There exists an absolute constant \(C_0>0\) such that

\[
\boxed{c_X\ge C_0X^{-4/15}\qquad(X\ge5).}
\tag{25.8}
\]

To prove this, every prime greater than five is coprime to \(30\). Adding factors in \((0,1)\) can only decrease a product, hence

\[
c_X\ge\frac4{15}
\prod_{\substack{7\le n\le X\\(n,30)=1}}\left(1-\frac1n\right).
\]

The elementary inequality \(\log(1-u)\ge-u-u^2\), \(0\le u\le1/2\), and convergence of \(\sum n^{-2}\) reduce the estimate to a reciprocal sum over residue classes. Finite inclusion–exclusion gives the exact formula

\[
\sum_{\substack{1\le n\le X\\(n,30)=1}}\frac1n
=\sum_{d\mid30}\frac{\mu(d)}dH_{\lfloor X/d\rfloor}
=\frac4{15}\log X+O(1).
\]

The last step uses only the integral bounds \(H_n=\log n+O(1)\), with the eight divisors of \(30\) fixed. Taking logarithms in the product proves (25.8), after adjusting the constant for the finite initial range.

Combining (25.6) and (25.8) now proves

\[
\boxed{
\|\mathbf1-F_X\|_H^2\ge\frac{C_0^2}{2}X^{7/15}
\longrightarrow\infty.
}
\tag{25.9}
\]

Therefore \(\|F_X\|_H\to\infty\) as well. This is a concrete example in the full legal residue space with the correct limit at every coordinate and the correct eventual value of every fixed coefficient, yet divergent full energy. It does not contradict the coefficient theorem for the **actual orthogonal projections**. The vectors \(F_X\) are not those projections.

## 26. The simplest exact-head repair also has divergent Pareto energy

One might try to remove the linear head defect in (25.3) by a single legal correction. Set \(A=X+1\) and

\[
\widehat F_X=F_X+c_XA g_A.
\tag{26.1}
\]

This is still a finite legal vector, with largest modulus at most \(\max(P_X,X+1)\). It has the exact formula

\[
\boxed{
\widehat F_X(k)=\Phi_X(k)-c_XA\lfloor k/A\rfloor,
\qquad \widehat F_X(k)=1\quad(1\le k\le X).
}
\tag{26.2}
\]

Thus its first \(X\) coordinates are exactly right. Its coefficients at every fixed modulus still eventually equal \(-\mu(d)\), since the additional modulus \(X+1\) moves to infinity.

**Proposition 26.1.** Whenever \(c_XA\ge8\),

\[
\boxed{
\sum_{k>X}\frac{\widehat F_X(k)^2}{k(k+1)}
\ge\frac{A c_X^3}{64}.
}
\tag{26.3}
\]

**Proof.** Put \(L=\lfloor c_XA/4\rfloor\). For \(0\le j\le L\), we have \(A+j<2A\), since \(c_X\le1/2\). There is only one integer coprime to \(P_X\) in \([1,X]\), and at most \(j+1\) additional ones through \(A+j\). Hence

\[
\widehat F_X(A+j)
=\Phi_X(A+j)-c_XA
\le j+2-c_XA\le-\frac{c_XA}{2}.
\]

Also \((A+j)(A+j+1)\le4A^2\). Each of these \(L+1\) physical tail coordinates contributes at least \(c_X^2/16\), and \(L+1\ge c_XA/4\). Summing proves (26.3). \(\square\)

By (25.8), the condition \(c_XA\ge8\) holds eventually, and

\[
\boxed{
\|\widehat F_X\|_H^2\ge\frac{C_0^3}{64}X^{1/5}
\longrightarrow\infty.
}
\tag{26.4}
\]

Its distance from the constant target also tends to infinity by the triangle inequality. The defect has moved just beyond the interpolated head.

This rules out this one-correction family as a source of controlled full Pareto energy. It does not refute the optimized full dictionary or identify \(\|F\|_H^2\) with the distinct conditional-mean energy \(\mathcal E(F)\). It also makes no claim that every more elaborate signed CRT correction must fail.

The parameters must remain distinct: \(X\) is the prime cutoff; \(P_X\) is the largest possible modulus in (25.1). The displayed polynomial lower bounds concern \(X\), and do not describe the optimum at maximum modulus \(N\).

## 27. What the continuation changes about the next attack

The primorial calculation eliminates a specific attempted shortcut: coordinatewise convergence, eventual Möbius coefficients, and even an exactly interpolated growing head do not provide the energy control required by the RH bridge. These examples have unbounded norms, so they cannot converge weakly in \(H\) either.

For the capacity formulation, the exact remaining task is unchanged:

\[
\boxed{\sup_N\tau_N=\infty,}
\tag{27.1}
\]

or, equivalently by monotonicity,

\[
\forall B>0\ \exists N\ge2:\quad v_N^{\mathsf T}T_N^{-1}v_N>B.
\tag{27.2}
\]

In the screened dyadic form this is

\[
\boxed{\sup_J\sum_{j<J}s_j^{\mathsf T}\Sigma_j^{-1}s_j=\infty.}
\tag{27.3}
\]

An explicit divergent rate would be useful, but is not logically necessary. A proof at arbitrarily sparse finite dictionaries suffices if their actual capacities are unbounded. Alternatively, one must exclude all the Hilbert certificates of Section 15 using their equations; the first-moment exclusion covers only a proper regularity class.

The concrete construction lesson is to analyze the complete signed energy of corrections jointly with the defect they remove. The single correction in Section 26 has an explicit post-head cost that diverges. A successful replacement must control that cost after full reoptimization. None of the literature results audited in Section 24 proves the required estimate.

## 28. Verification boundary for this audit and continuation

The live audit rechecked the existing capacity-to-RH implication and bounded-capacity/certificate equivalence. It did not prove their open antecedents, formalize the classical RH converse, or rerun every module in the project.

The new module `RiemannResearch/Analysis/FiniteParetoAffineEnergy.lean` contains the finite energy calculations used in Section 25:

| Declaration | Content |
| --- | --- |
| `finite_pareto_affine_energy` | Exact Pareto energy through a finite head for \(1-ck\). |
| `finite_pareto_linear_energy` | Exact finite error energy \(c^2(X+1-H_{X+1})\). |
| `pareto_affine_head_error_lower` | Transfers that exact head error to the full sum, with an explicit summability hypothesis. |
| `pareto_affine_head_error_lower_linear` | Gives the simpler full-error lower bound \(c^2X/2\). |

The finite CRT identity, elementary Euler-product bounds, asymptotic primorial failure, and the one-correction obstruction have written proofs in Sections 25–26. They are **not claimed as end-to-end Lean formalizations** in this change. In particular, the generic affine-head hypothesis in the new module has not been discharged there for a Lean definition of the primorial family.

The literature audit supplies an exact identification with a classical criterion and clarifies which estimates are conditional. The new calculations rule out two explicit approximation families. **Capacity divergence and RH remain unproved in this work.**

The four finite-energy declarations passed the isolated check `job_OnBMcT-hn3O8oxp5hs8fzElks_ud9oeC` (exit 0, 2.530 seconds). Each axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`. The current capacity implication was independently audited in the job recorded in Section 24.3.
