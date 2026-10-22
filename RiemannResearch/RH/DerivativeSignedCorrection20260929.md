# Fixed signed derivative correction, 2026-09-29

Continuation from 41b7faf6f5f70d57481b666f09c38eb8bb2c0170.
This is new mathematical development, not a repetition of the separate CI/source audit.

## Notation and exact signed correction

Write Delta for the anchored backward difference, P_n for the actual legal
projection at repository stage n (conductor cutoff n+1), r=1-P_infinity,
C_n=correctionSynthesis n, and R_n=rawMobiusDerivativeResidual (n+1).
Let e_n=G_n^{-1}(b_n+G_n mu_n) and
K_i(j)=<Delta g_(i+2),Delta g_(j+2)>.
The new module RH/DerivativeSignedCorrection.lean defines

B_n(i) = sum_(j<n) e_n(j) K_i(j).

It proves B_n(i)=<Delta g_(i+2),Delta C_n> and the exact identity

fixedMismatch(n,i) = <Delta g_(i+2),R_n> - B_n(i).

The first term tends to zero unconditionally. The second term has the
identified limit -<r,Delta* Delta g_(i+2)>; it has not been shown to vanish.
No exchange of a growing sum with a coordinatewise limit is used.

## Dimension-independent result about the identified limit

Put H_n=P_infinity-P_n. The exact vector error is

Delta C_n + Delta r = R_n - Delta H_n.

Its complete squared norm equals

||R_n||^2 - 2<R_n,Delta H_n> + ||Delta H_n||^2.

In particular, for EVERY Hilbert test f,

|<f,Delta C_n> + <f,Delta r>|
  <= ||f|| (||R_n|| + 2||H_n||),

and

|<f,Delta C_n> + <f,Delta r>|^2
  <= 2||f||^2 [||R_n||^2 + 4(E_n-D)].

Here E_n=||1-P_n||^2 and D=||r||^2. The projection identity
E_n=D+||H_n||^2 is retained exactly. The bracket tends to zero without RH.
The unsquared budget also tends to zero. Consequently the paired error
tends to zero for ANY uniformly norm-bounded moving tests f_n; no convergence
of f_n is required. Constants are independent of Gram dimension.
This proves convergence ABOUT the identified limit, not that the limit is zero.

## Exact Abel reduction and the remaining arithmetic estimate

Extend e_n by zero beyond j=n-1 and put
A_n(k)=sum_(j<k)e_n(j). Exact finite summation by parts gives

B_n(i) = A_n(n) K_i(n)
         - sum_(k<n) A_n(k+1)[K_i(k+1)-K_i(k)].

The endpoint K_i(n) uses the next derivative atom. It is retained even
though the correction coefficient is zero there. The second Abel form is
also formalized, including BOTH boundary terms and all second differences.

The following condition is proved EQUIVALENT to r=0:

For every fixed i and epsilon>0, arbitrarily large n satisfy

| A_n(n) K_i(n)
  - sum_(k<n) A_n(k+1)[K_i(k+1)-K_i(k)] | < epsilon.

Thus each i and epsilon may have its own cofinal set. No rate, uniformity
in i, common subsequence, inverse-Gram operator bound, or separate bound on
the absolute values of the Abel summands is needed. This is an exact
necessary-and-sufficient arithmetic target, not a claimed smallest condition
among all possible reformulations. It implies Mathlib's RiemannHypothesis
through the existing fixedMismatch reduction.

OPEN: a provider of this cofinal signed cancellation for the actual e_n.
The equivalence and conditional RH implication do not provide it.

## Conductor two and the retained obstruction

The correction-row limit at i=0 is exactly

D + <r,(4g_2-1)/(k+2)>,

with sequences anchored at zero. This is the negative of the previously
proved first mismatch limit. Neither term can be removed by ordinary legal
orthogonality. Vanishing of the first row alone is not asserted to imply RH.

## Search conclusions

- NaturalMobiusDerivativeConvergence gives the complete raw derivative limit
  and exact correction limit, including cancellation q-2q+q=0.
- Analysis/SignedAbel supplies two exact finite formulas; the new module
  applies them directly to the derivative correction coefficients.
- ResidueCorrectionDivisorAbel and ResidueCorrectionAbelLimits give exact
  progression/tail formulas and certified finite approximations for the
  original corrections. Their cofinal signed cancellation provider is open.
- ResidueTailAdditiveCancellation provides conditional Abel estimates and
  obstructions; its required additive cancellation is not established for
  the canonical residual.
- FiniteDyadicDefect and ResidualDerivativeCoercivity preserve dyadic defects
  and all square remainders. Their lower/coercive controls do not give the
  needed signed-row upper decay.
- CRTExactSignedEnergy retains signed periodic remainders and gives uniform
  enclosures, but no estimate for growing canonical correction rows.
- DerivativeAdjointRows identifies the weighted arithmetic progression test
  precisely; membership of these tests in the legal closure is not supplied.

No unconditional fixed-coordinate vanishing or proof of RH is claimed.
Source: independent assembly of the user-specified repository results and
its existing finite Abel identities; no mathematical novelty claim.
