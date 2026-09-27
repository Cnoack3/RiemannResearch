# Uniform half-range damping and endpoint continuity

Date: 2026-09-27. Project: RiemannResearch, Lean 4 / Mathlib.

## Established strengthening

The earlier result proved full natural-order Hilbert convergence for
each fixed damping epsilon>=1/2. The convergence is now proved
**uniformly over the entire unbounded half range**.

With
`F_epsilon,M(n)=-sum_{d<=M} mu(d)*d^(-1-epsilon)*(n mod d)`
and
`g_epsilon(n)=dampedMobiusPrefix epsilon n
 - n*Re(1/zeta(1+epsilon))`,
the principal result is

```math
\forall\eta>0\;\exists K\;\forall\varepsilon\ge\tfrac12\;
\forall M\ge K,\qquad
\|F_{\varepsilon,M}-g_\varepsilon\|_P\le\eta,
\qquad
\|h\|_P^2=\sum_{n\ge1}\frac{|h(n)|^2}{n(n+1)}.
```

This is `dampedMobius_half_range_uniform_approximation`.
The canonical vector `dampedMobiusHalfRangeLimit epsilon h_epsilon`
is selected from the already proved convergence theorem; its specification
identifies every arithmetic coordinate and its natural-order limit.
The inequality includes the complete infinite physical tail.

## Exact signed Abel argument

Put u_n=-arithmeticResidueTerm(dampedMobiusWeight(1/2),n),
S_N=sum_{n<N}u_n, delta=epsilon-1/2, and a_n=(n+1)^(-delta).
The checked factorization gives

```math
F_{\varepsilon,N}=\sum_{n<N}a_nu_n.
```

For N>=1, the exact finite identity is

```math
\sum_{n<N}a_nu_n
=a_{N-1}S_N+
\sum_{n<N-1}(a_n-a_{n+1})S_{n+1}.
```

When delta>=0, every coefficient on the right is nonnegative, and
their sum telescopes to a_0=1. Consequently a common norm bound C
on the full signed prefixes gives the same bound C after damping.
No individual residue-atom norm is summed.

The same identity applies to shifted prefixes:
sum_{n<r}u_{K+n}=S_{K+r}-S_K. If all these differences have norm at most
eta, then for every N>=K and every positive decreasing weight with
a_0<=1,

```math
\left\|\sum_{n<N}a_nu_n-\sum_{n<K}a_nu_n\right\|\le\eta.
```

Thus the endpoint Cauchy modulus works for every extra damping.
Taking the known weighted limit gives uniform approximation to
g_epsilon. The abstract results require no completeness assumption
when the relevant limits are supplied.

## Other discharged dependencies

- `dampedMobius_half_range_uniform_norm_bound`: one C bounds
  ||F_epsilon,M|| for every epsilon>=1/2 and M.
- `dampedMobius_half_range_uniform_energy_and_signed_bounds`: one B
  bounds E_epsilon=||g_epsilon||^2, every full signed Gram off-diagonal,
  and every signed physical head, for all epsilon>=1/2 and all H,M.
  This removes the previous dependence of the stated bound on epsilon.
- `dampedMobius_joint_damping_cutoff_tendsto`: if epsilon_j>=1/2,
  epsilon_j->1/2, and M_j->infinity, then
  F_epsilon_j,M_j->g_(1/2) in full Hilbert norm. No relation between the
  two rates is required, and epsilon_j need not be monotone.
- `dampedMobius_varying_damping_error_tendsto`: for arbitrary
  epsilon_j>=1/2 and M_j->infinity,
  ||F_epsilon_j,M_j-g_epsilon_j||->0. The damping sequence need not converge.
- `dampedMobius_limit_tendsto_half`: g_epsilon_j->g_(1/2) in norm
  whenever epsilon_j>=1/2 and epsilon_j->1/2.
- `dampedMobius_energy_tendsto_half`: the actual infinite arithmetic
  energies converge to the endpoint energy under the same assumptions.

For joint Abel regularity, first fix a sufficiently long endpoint prefix.
The remaining weighted tail is uniformly small. On the fixed finite
prefix all damping coefficients tend to one. This proves the joint limit.
Uniform approximation then transfers the result to the limiting vectors;
continuity of the squared norm gives the energy limit.

## Scope and provenance

The analytic transfer is unconditional once the base natural-order
convergence is given. In the actual arithmetic specialization that premise
is discharged by the existing half-endpoint provider. No new arithmetic
hypothesis, RH assumption, or absolute vector summability is inserted.

**Open:** descent to actual finite energy below one half, and finite
energy or signed bounds at positive dampings tending to zero. For
epsilon<1/2 the extra weights grow with conductor, so the positive
decreasing-weight argument no longer applies. Endpoint continuity from
above does not supply continuation below the endpoint.

Burnol, *On an analytic estimate in the theory of the Riemann zeta function
and a theorem of Baez-Duarte*, Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166, supports the underlying endpoint
membership statement. The uniform transfer here is an explicit standard
Abel argument built on checked repository declarations; no novelty claim
is made.

## Lean files and verification

- `Analysis/MonotoneAbelConvergence.lean`: general norm and tail bounds,
  uniform Cauchy and limit approximation, and joint Abel regularity.
- `RH/DampedMobiusUniformHalfRange.lean`: exact arithmetic factorization,
  canonical limits, uniform approximation and bounds, joint limits,
  endpoint norm continuity, and energy continuity.

The complete source passed with exit_code=0 and verified=true, with no
warnings (job_7DD8A80cfEmv7QgYzg99iH3Pqc0mKBSr).
The generic module passed with its focused import alone
(job_E23KO-UKAfzTmpD9b_FPCOLRFxvg8wVK).
The principal axiom checks contain only propext, Classical.choice,
and Quot.sound. No sorry, admit, project-local axiom, or unsafe
declaration is used. Final publication validates the changed modules
and their affected local dependents.
