# Ramanujan–Plancherel and A1–A2 audit, 2026-11-17

## Source and scope

Source: [Best Nyman Beurling for RH - A1-A2 Audited Revision.pdf](https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view).

The inspected file has 89 physical PDF pages: the main manuscript and an appended research continuation through section 23. The main manuscript is dated 28 July 2026. Source SHA-256:

79504dae598aac3f67b4ae5fc5f7c47fc52f86a568ccb45e871ef678bc40589c

This audit separates newly kernel-checked finite identities, a new conditional RH criterion for the actual optimizer, reviewed arguments, and unproved analytic estimates. It is not a blanket certification of the PDF or its companion large-sieve theorem.

## Critical dependency gap: the claimed bound q_x <= 1

Main section 2.2 asserts

$$0\le q_x\le \Delta_x^2=\omega_P(P)+q_x\le1$$

on the ground that the zero approximant is admissible. Here the optimizer belongs to the constrained exact-head family. The zero approximant does not satisfy its prescribed head. Setting the upper-atom coefficients to zero gives the residual C_x, not the residual of the unconstrained zero approximant. Orthogonal projection therefore gives q_x <= ||C_x||^2, not automatically q_x <= 1.

[ExactHeadEnergyAudit.lean](RH/ExactHeadEnergyAudit.lean) makes the dependency precise:

- zero_coefficients_not_exact_head rejects the all-zero coefficient trial already at d=1.
- atom_energy_lower_bound_at_zeta_zero gives a quantitative lower bound for this exact atom optimizer.
- riemannHypothesis_of_cofinal_atom_energy_bound proves that any fixed energy bound along arbitrarily late exact-head stages implies actual Mathlib RiemannHypothesis.
- riemannHypothesis_of_paper_atom_energy_bound specializes this to the paper's exact convention P=primorial(x), for every x>2.
- riemannHypothesis_of_primorial_atom_energy_le_one also covers the repository's greenPeriod(x)=primorial(x+1) convention.

Explicitly, if s is a zeta zero with Re(s)>1/2 and s != 1, then

$$
\frac{2\Re(s)-1}{|s|^2}(x+1)^{2\Re(s)-1}
\le \omega_P(P)+q_{P,x},
$$

provided x<P and every squarefree d<=x divides P. For cofinal x the left side is unbounded. Consequently

$$
\bigl(\exists B,\ \forall x>2,\ q_{\operatorname{primorial}(x),x}\le B\bigr)
\Longrightarrow \mathrm{RH}.
$$

The new theorem is stronger than the paper's proposed normalization: squarefreeness of the periods, a bound at every stage, decay to zero, A1, and A2 are unnecessary for the cofinal criterion. Coverage of the squarefree head and boundedness of the actual optimizer remain explicit hypotheses.

**Conclusion:** the zero-trial justification is invalid, and uniform boundedness is a substantive RH-sufficient premise. This audit does not prove that q_x<=1 is false, does not prove its converse from RH, and does not prove RH.

### Consequences for the manuscript

The supplement's section 4 explicitly calls its low-field decay absolute because q_x<=1. The displayed q_x-dependent inequality (4.3) does not justify its absolute conclusion (4.4) without a suitable bound on q_x. The same caution applies to main section 5 and later physical-tail/cutoff deductions whenever q_x is silently replaced by 1.

Retain the complete factor:

$$
\|L_{x,Y}\|_{w,x}^2
\ll q_x(\log x)^2
\exp\!\left((\log2+o(1))\frac{\log Y}{\log\log Y}\right)
\left(\frac Yx+\frac{Y^3}{x^2}\right).
$$

This formula itself depends on the cited primitive large-sieve theorem, which was not newly formalized in this change. Its transition to an absolute o(1/log x) bound is now conditional on the missing growth estimate. Thus removing the low range before identifying the high range as the only remaining A1 obstruction is not currently justified by the PDF alone.

The finite A1–A2 Cauchy–Schwarz identities and the conditional closure strategy should be kept separate from this gap. No finite identity below uses q_x<=1.

## Corrected Ramanujan–Plancherel theorem

Let P be squarefree and let c_a(g) be the repository's real Ramanujan sum. For arbitrary real divisor coordinates W, define

$$S(a)=\sum_{g\mid P}W(g)c_a(g).$$

[RamanujanFinitePlancherel.lean](RH/RamanujanFinitePlancherel.lean) proves the arithmetic kernel directly from the prime contrasts:

$$
\sum_{a\mid P}\frac{c_a(g)c_a(h)}{\varphi(a)}
=\mathbf1_{g=h}\frac P{\varphi(P)}\varphi(g)
\qquad(g,h\mid P).
$$

It then proves the corrected identity

$$
\sum_{a\mid P}\frac{S(a)^2}{\varphi(a)}
=\frac P{\varphi(P)}\sum_{g\mid P}\varphi(g)W(g)^2,
$$

and the stronger polarization and inversion formulas

$$
\sum_{a\mid P}\frac{S_W(a)S_V(a)}{\varphi(a)}
=\frac P{\varphi(P)}\sum_{g\mid P}\varphi(g)W(g)V(g),
$$

$$
W(g)=\frac{\varphi(P)}{P\varphi(g)}
\sum_{a\mid P}\frac{c_a(g)S(a)}{\varphi(a)}.
$$

These results apply to any squarefree period, not just a primorial.

### Internal definition and actual optimizer bridge

[ExactHeadRamanujanPlancherel.lean](RH/ExactHeadRamanujanPlancherel.lean) supplies the definition left external in the PDF:

$$W(g)=\langle R,A_g\rangle_w.$$

It proves, by finite gcd-class synthesis,

$$
S(a)=\left\langle R,\sum_{n\le r}c_a(n)\right\rangle_w,\qquad
S(1)=\langle R,r\rangle_w=\beta,
$$

and, for a>1,

$$
S(a)=-\langle R,J_a\rangle_w
=\theta(a)-\frac{\varphi(a)}2\tau.
$$

The existing repository primitiveScore uses the opposite sign to the paper's theta; conductorScore_primitive records this convention explicitly.

For the actual atom optimizer, upper normality proves W(g)=0 when x<g. Hence atomResidual_plancherel establishes the paper's corrected formula without assuming any estimate on q_x, beta, coefficients, or return operators:

$$
\sum_{a\mid P}\frac{S(a)^2}{\varphi(a)}
=\frac P{\varphi(P)}
\sum_{\substack{g\mid P\\g\le x}}\varphi(g)W(g)^2.
$$

Removing a=1 subtracts exactly beta^2. The arithmetic theorem omitted_conductor_identity_iff proves that omitting this subtraction is valid precisely when sum_g W(g)=0. For the actual residual this is beta=0, which is not automatic.

### Stronger lower-support information

For any finite positive support D, the exact mass remainder is

$$
\left(\sum_D\varphi(g)W(g)^2\right)
\left(\sum_D\frac1{\varphi(g)}\right)
-\left(\sum_D W(g)\right)^2
=
\frac12\sum_{g,h\in D}\varphi(g)\varphi(h)
\left(\frac{W(g)}{\varphi(h)}-\frac{W(h)}{\varphi(g)}\right)^2.
$$

Consequently, with D={g|P:g<=x},

$$
\beta^2\le
\left(\sum_D\frac1{\varphi(g)}\right)
\left(\sum_D\varphi(g)W(g)^2\right).
$$

The remainder identifies the precise deviation from W(g) proportional to 1/phi(g). This is finite energy accounting, not a decay theorem for its right side.

## New agenda: endpoint drift and activated moments

[FiniteWeightedReturnDrift.lean](Analysis/FiniteWeightedReturnDrift.lean) formalizes the algebraic core of supplement section 23.

Let u be a global fit, v a tail fit, h=C-u on a prefix L, and d=u-v on the tail T. Suppose the global and tail normal equations hold in a common subspace V. For every F in V,

$$\langle h,F\rangle_L=\langle d,F\rangle_T.$$

If u,v belong to V, then

$$
E_L(C-u)+E_T(C-u)
=E_T(C-v)+E_L(C-u)+E_T(u-v).
$$

Thus the energy available to the endpoint return is the extension energy minus its prefix component. Using the whole extension energy as if it were entirely return energy loses a nonnegative term when weights are nonnegative.

The implementation improves the hypotheses: these equalities require neither an invertible Gram matrix nor a basis. They even hold for signed weights; positivity is needed only for subsequent inequalities. The source also proves a rank-one normal-update identity and a telescoping identity for verified updates.

The target-blind accessibility result is constructive: whenever a prefix vector h and a tail vector d in V satisfy the compatibility normal equations, a target taking values h on L and -d on T realizes that endpoint drift. This formalizes the obstruction behind Proposition 23.9. It does not establish an operator-norm lower bound or refute target-specific cancellation.

[ExactHeadAtomReturnMoments.lean](RH/ExactHeadAtomReturnMoments.lean) connects these identities to the actual gcd-atom space. Define

$$
m_Y(g)=\langle h,A_g\rangle_{[1,Y]},\qquad
U_p=\sum_{\substack{g\mid P\\x<g\\p\mid g}}A_g,\qquad
S_Y(p)=\sum_{\substack{g\mid P\\x<g\le Y\\p\mid g}}m_Y(g).
$$

Lean proves:

1. m_Y(g)=0 for g>Y.
2. U_p belongs to the upper-atom span.
3. The complete tail covariance equals the activated moment: <d,U_p>_T=S_Y(p).
4. Return differences equal S_Y(p)-S_Y(q).
5. The three-label determinant combination is exactly
   p(r-q)S_Y(p)-q(r-p)S_Y(q)+r(q-p)S_Y(r).

These results hold for arbitrary divisor labels and periods, not only primes and primorials. They formalize the activated-moment algebra of (23.21)–(23.24). The physical-window continuation below now identifies the paper's original z_Y(p)/p with these coordinates, including the exact correction outside the safe cutoff. The numerical curvature prefactors and full inverse-Gram/Hessian formulas are not asserted as newly kernel-checked.

## Physical-window continuation

[ExactHeadPhysicalReturn.lean](RH/ExactHeadPhysicalReturn.lean) now formalizes the missing arithmetic bridge from supplement sections 22.2 and 23.5. This preserves the earlier audit of the invalid uniform-energy justification; it does not reinstate any absolute estimate obtained by deleting \(q_x\).

Write \(G_p(n)=\lfloor n/p\rfloor\), \(A_g(n)=\#\{1\le k\le n:\gcd(k,P)=g\}\), and \(U_p=\sum_{g\mid P,\ x<g,\ p\mid g}A_g\). For \(P\ne0\), \(p\mid P\), and \(p\le x<2p\), the all-position identity is

$$
U_p(n)=G_p(n)-A_p(n).
$$

For arbitrary real weights \(w\) and signal \(h\), the definition of the paper's physical signal retains its factor \(p\) and integer interval:

$$
z_Y(p)=p\sum_{x<n\le Y}w(n)h(n)(G_p(n)-1).
$$

With the activated moment \(S_Y(p)\) already defined in ExactHeadAtomReturnMoments, the complete correction formula is

$$
z_Y(p)=pS_Y(p)+p\sum_{x<n\le Y}w(n)h(n)(A_p(n)-1).
$$

No cutoff restriction is needed for this equality. If \(p\) is prime, every prime at most \(p\) divides \(P\), and \(Y<p^2\), the lower-class correction vanishes exactly:

$$
z_Y(p)=pS_Y(p).
$$

In particular, the arithmetic hypotheses are supplied for \(P=\operatorname{primorial}(x)\), \(p\) prime, \(p\le x<2p\), and \(Y<p^2\). The general proof needs neither squarefreeness of the period, positive weights, an energy bound, nor normal equations. The paper's physical ceiling \(Y<x^2/4\) and window \(p>x/2\) lie inside this range.

The cutoff cannot simply be removed. A finite kernel certificate gives

$$
U_3(9)=1,\qquad G_3(9)-1=2\qquad(P=30,\ x=5).
$$

This refutes extension of the zero-correction formula through the first square; it does not refute the paper's correctly restricted window.

For the actual atom residual \(R\) with the exact periodized Pareto weight, the proved normal equations supply the full tail identity under the same safe-window hypotheses and \(Y<P\):

$$
z_Y(p)=-p\langle R,U_p\rangle_{Y<n<P}.
$$

For a global fit \(u\) and tail-only fit \(v\) satisfying their normal equations, the corresponding endpoint formula is

$$
z_Y(p)=p\langle u-v,U_p\rangle_{\mathrm{tail}}.
$$

The signs differ because the first formula pairs the residual, while the second pairs the fitted drift. Neither formula truncates the return graph. Combining this identification with triple_curvature_moment supplies the original three-prime signal's signed activated-moment numerator. A quantitative bound for that numerator remains open.

The physical-window identification is therefore discharged. The remaining work must retain the inverse-tail-Gram return cost and any required \(q_x\) growth hypothesis. The companion large-sieve input, full Hessian normalization and asymptotic curvature estimates are not certified by this finite bridge.

## Status by claim

| Claim | Status after this change |
| --- | --- |
| Complete finite Ramanujan–Plancherel formula including conductor 1 | Newly kernel-checked |
| Actual optimizer coordinates W(g), S(1), centered primitive sign, upper support | Newly kernel-checked |
| Polarization, inversion, exact weighted mass remainder | Newly kernel-checked strengthening |
| Uniform/cofinal actual atom-energy bound implies RH | Newly kernel-checked conditional implication |
| q_x<=1 justified by the zero approximant | Invalid justification; bound remains unproved |
| Absolute low-primitive decay obtained by deleting q_x | Unsupported without additional growth control |
| Companion primitive large-sieve estimate | Cited analytic input; not newly kernel-checked |
| Endpoint covariance, energy split, update telescope | Newly kernel-checked, weaker hypotheses |
| Activated-atom moment and three-label return formulas | Newly kernel-checked finite identities |
| Physical-window realization z_Y(p)=p S_Y(p), with prime coverage and Y<p^2 | Newly kernel-checked by the continuation |
| All-cutoff lower-class correction and actual residual's complete tail identity | Newly kernel-checked strengthening |
| Full inverse-Gram/Hessian formulas and numerical curvature prefactors in sections 22–23 | Reviewed source claims; not fully formalized in this change |
| Uniform actual signed-curvature/nonalignment estimate | Open |
| A1, A2, q_x -> 0, RH | Not proved by this change |

## Next concrete obligations

1. Correct section 2.2 and propagate q_x through every downstream estimate. Maintain separate relative and absolute conclusions.
2. If pursuing the low/high split, prove the actual growth control needed by the selected cutoff. Do not classify that estimate as a routine normalization; even uniform boundedness already suffices for RH.
3. Use the now-checked physical-window identification to estimate the actual signed moments. Retain the lower-class correction if the physical cutoff reaches a prime square; retain the periodized weights and complete upper-atom family.
4. Attack the actual signed three-prime moment combination. A bound for its weighted curvature energy requires arithmetic information about C_x beyond global and tail normality.
5. Keep the inverse tail Gram geometry in the energy budget. Neither diagonal replacement, Plancherel alone, nor normal equations provide the required asymptotic smallness.
6. For the trivial-conductor A2 route, bound the actual lower-support weighted score energy; the exact mass remainder is a concrete certificate to investigate. This still leaves the other signed scalar contributions unless separately controlled.

The source's final target, an actual endpoint-curvature quantity o(x^2/log^3 x), remains open. The identities isolate its inputs but do not supply its rate.

## Verification record

All six modules are exported by RiemannResearch.lean. They contain named proofs with no unfinished proof placeholders or project-local axioms.

Component Bazel/BuildBuddy checks:

- Arithmetic transform, energy audit, and endpoint drift: job_6q52U64wM0lyIzsJjjEz_-FGT57rfoG2, [115.431 seconds of server verification](https://app.buildbuddy.io/invocation/678d598d-d3c6-44f8-ab35-914a5c3d982d).
- Actual optimizer bridge and paper-period RH criterion: job_PdCoO6_T3yoWlAutLFVIVaH6MIR8FBSu, [85.074 seconds of server verification](https://app.buildbuddy.io/invocation/3aa95ac2-ff0c-4fd3-a29c-d7ebf5d1a8b4).
- Activated-moment check: job_QrTbzxUHOdpwx7ukCxQeUyhTuYIEMQV0, [62.628 seconds of server verification](https://app.buildbuddy.io/invocation/cfd4d582-ed79-4f82-97be-8730015fa207).

These durations are server-reported verification elapsed times, not API round-trip or queue/polling measurements. Successful component checks certify their imported source graph, not the full repository. The managed publication checkpoint separately validates the full //:RiemannResearch target and, if required, the source integrated with newer main before publishing its exact commit.

### Physical-window continuation verification

- File acceptance: job_mt7ljakLdZC2vEO6JY-HFSV-1ldhok4W.
- Scope: //RiemannResearch/RH:ExactHeadPhysicalReturn and its transitive imports.
- Backend: Bazel --config=buildbuddy; verified=true, exit_code=0.
- [BuildBuddy invocation](https://app.buildbuddy.io/invocation/619ec47e-dc55-4c85-bd96-0829cc262fc9).
- Server verification elapsed: 34.363 seconds.
- Checked file SHA-256: f98e181733f0b183d04ff6ed24f07f2dbd8b42482e4e873011c7b01a97b285ab.

This component result is not a full-project checkpoint. The final managed
checkpoint validates the complete project and any integration with newer main
before publishing. No A1, A2, curvature-rate or RH conclusion follows from
the finite identities.

The actual-optimizer theorem also passed a guarded axiom check:
job_MUoKCBNHHBeFMlt223xyKg7FoUXnXF2p,
[BuildBuddy invocation](https://app.buildbuddy.io/invocation/b01459d6-9e7d-414e-82ab-4f92caeca8a6).
The checked `#guard_msgs` assertion requires exactly
`[propext, Classical.choice, Quot.sound]` for
`RiemannResearch.RH.ExactHeadPhysicalReturn.atomResidual_physicalSignal_eq_tail`.
It passed through Bazel with `verified=true`; no project-specific axiom occurs
in that theorem's dependency set. Its arithmetic window assumptions remain
explicit in its type.

## Signed three-prime quantitative continuation

The [signed-moment theorem catalog](THEOREM_CATALOG_SIGNED_THREE_PRIME_RETURN_20261117.md)
records four further checked modules. With the actual residual R, complete
signed atom profile F, numerator N, and complete tail return d, they prove

    Q = E_L(R) + E_T(R+d) + E_T(d),
    (E_L(F)+E_T(F)) N² <= [Q-E_T(R+d)] E_L(F) E_T(F).

The exact nonnegative Gram remainders precede these inequalities. In the safe
prime window they also prove the position-independent signed floor bound
|F(n)| <= (q-1)(r-p), hence

    N² <= Q * M_[x+1,Y] * [(q-1)(r-p)]².

Here Q is the actual atomEnergy(P,x); it is never replaced by 1. The periodized
mass and all tail Gram cross terms remain explicit. The corrected polarized
Ramanujan formula is applied to activated prefix scores with conductor one
included. The full-period upper scores cannot be substituted for those
prefix scores.

The actual tail representer is constructed without invertibility. Its cost
is both c transpose G_T c and c transpose m. The period-endpoint atom is a
zero tail Gram column; a matrix inverse must therefore specify a reduced
basis or the feasible range.

These are unconditional finite estimates under their stated cutoff/arithmetic
assumptions. They do not prove a cofinal bound for Q, a uniform inverse-return
estimate, the requested normalized curvature decay, A1, A2, or RH. See the
linked catalog for exact declaration names, hypotheses, and verification scope.
