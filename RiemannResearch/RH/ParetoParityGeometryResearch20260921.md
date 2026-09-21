# Exact parity geometry and a solved relaxed arithmetic component

Research derivation, 21 September 2026. The accompanying Lean development
now verifies finite contrast extraction and the complete actual normalized
all-divisor sieve contrast limit. The infinite closed-space geometry below
is an ordinary mathematical derivation.
Nothing here proves RH or removes the remaining full-norm requirement.

## 1. Full two-coordinate energy, with the block means retained

Let H be the actual Pareto Hilbert space on physical j>=1, with
w_j=1/[j(j+1)], and H_tail its subspace vanishing at j=1.
For f in H_tail and p=2k+1>=3 put

    Δ_p f = f(p)-f(p-1),
    A_k f = ((k+1) f(2k)+k f(2k+1))/(2k+1).

Direct completion of a weighted square gives the exact equality

    w_(2k) f(2k)^2+w_(2k+1) f(2k+1)^2
      = [1/(2k(k+1))] (A_k f)^2 + (Δ_(2k+1)f)^2/[2(2k+1)^2].

Both sums are nonnegative, so summing and regrouping the summable original
energy is valid. Define B to be the closed subspace of H_tail consisting of
vectors equal on each pair (2k,2k+1). Its orthogonal projection replaces each
pair by A_k f. Consequently

    ||f||² = ||P_B f||² + (1/2) Σ_(odd p>=3) (Δ_p f)²/p².

The verified `ParetoParityContrast.lean` uses the existing actual orthogonal
vectors u_p=p(p+1)e_p-p(p-1)e_(p-1). For any finite collection of disjoint
pairs it proves the stronger useful finite statement with the exact Hilbert
remainder still present:

    ||f||² = Σ_p <u_p,f>²/(2p²) + ||f-P_M f||².

## 2. Arithmetic content of the contrasts

For F_c=Σ_(d>=2)c_d t_d set

    h=Σ_d c_d/d,
    J=Σ_(odd d>=3)c_d/d²,
    D_c(p)=Σ_(odd d|p,d>=3)c_d.

At each odd p>=3 the residue first-difference identity gives exactly

    Δ_p F_c=h-D_c(p).

Every even coefficient affects these contrasts only through the single
scalar h. No even coefficient changes D_c at an odd p. This includes all
odd composite moduli and all signed combinations.

Write Z=π²/8, S=Z-1, κ=Z/S. Absolute convergence for a finite coefficient
vector gives

    Σ_(odd p>=3) D_c(p)/p² = Z J,
    Σ_(odd p>=3) 1/p² = S.

It follows that the squared distance from F_c to the enlarged even space

    E₀=B+span(t₂)

is exactly

    dist(F_c,E₀)²=(1/2)Σ_(odd p>=3)(D_c(p)-κJ)²/p².

In particular, h=κJ is precisely the choice making the B-perpendicular
component orthogonal to the one extra contrast direction supplied by t₂.

## 3. An explicit normalized sieve closes this relaxed component

Let P be a nontrivial odd squarefree integer, for example the product of all
odd primes at most N, with N>=3. Define

    A_P=∏_(ℓ|P, prime)(1-ℓ^(-2)),
    a_P=1/(1-A_P),
    c_d=-a_P μ(d)  for d|P, d>1,

with all other odd coefficients zero. Inclusion-exclusion gives exactly

    J=1,
    D_c(p)=a_P · 1_{gcd(p,P)>1}  (odd p>=3).

Choose the modulus-two coefficient as c₂=2(κ-h_odd). This makes h=κ
exactly and does not change J or any odd divisor sum. Put

    R_P=Σ_(odd p>=3, gcd(p,P)=1)1/p²=Z A_P-1.

The existing project Euler-product identities cover this mass by replacing
P with 2P. The complete relaxed contrast energy is the exact scalar

    V_P = [(κ-a_P)²(S-R_P)+κ²R_P]/2
        = Z² R_P/[2 S(S-R_P)].

Every denominator is positive: P has an odd prime divisor, so the
noncoprime odd-site mass S-R_P is positive. As the odd primes exhaust,
the indicator gcd(p,P)=1 vanishes eventually for each fixed odd p>=3.
It is dominated by the summable sequence 1/p². Thus R_P -> 0, and the exact
formula proves V_P -> 0 unconditionally. No RH assumption, zero estimate,
Mertens cancellation estimate, or unproved rate is used.

Therefore the divisibility/contrast part of the parity relaxation is
constructively solvable. It is not the missing RH estimate.

## 4. Why this is not a full legal approximation

Let B_P=∏_(ℓ|P, prime)(1-1/ℓ). The odd reciprocal head equals

    h_odd=a_P(1-B_P).

The only even atom used in this particular construction is t₂, which
vanishes at physical site two. Thus the c₂ correction cannot change

    F_c(2)=2a_P(1-B_P).

For prime exhaustion A_P -> 1/Z, a_P -> κ, and B_P ->0, hence
F_c(2)->2κ. In particular this particular c₂-only family has a positive
full-energy obstruction, despite V_P->0. One does not need the limit
B_P->0 merely to see the problem: once 3|P, h_odd>=a_P/3>=1/3,
so ||F_c||²>=F_c(2)²/6>=2/27 for every such P.

There is an exact description of the remaining block means. For every
fixed physical j, sieve inclusion-exclusion shows that the number of
integers <=j coprime to P eventually equals the number of powers of two
<=j. Consequently the normalized vectors converge coordinatewise on the
tail to κ(1+floor(log₂j)), a pair-constant vector. This is a statement
about coordinatewise convergence only; Hilbert-norm convergence is not
asserted. Uncontrolled energy may also escape to larger sites.

## 5. Exact location of the still-open legal-space gap

Let W be the closed original legal residue span in H and T=T₂. The checked
dilation identity is

    T g_d=2 g_(2d)-(2/d)g₂,
    ||Tf||²=2||f||².

Thus the actual infinite even-tail span is

    E=T W+span(t₂),

whereas E₀=T H+span(t₂). Both sums are closed, since T has closed range and
adjoining a finite-dimensional space preserves closedness. Replacing E by
E₀ silently assumes away the important approximation problem.

Set L=T*/2, a=(I-P_B)t₂. Then

    ||a||²=S/8,
    z₂=(4/S)a,

the latter following coordinatewise from the existing inverse-square
coprime-certificate series. For an h=κJ normalized F, the exact gap is

    dist(F,E)² = ||(I-P_B)F||²
      + inf_(λ in R) { (S/8)λ² + 2 dist(LF-λLt₂,W)² }.

For arbitrary F the first term becomes dist(F,E₀)² and λ² becomes
(λ-λ₀)², with λ₀=2(h-κJ). This follows by first orthogonally separating
B and B-perpendicular, then minimizing over the remaining legal vector
in TW. All terms are retained.

The explicit sieve proves that the first term can vanish. No proof that
the second infimum vanishes has been found. At half scale its multiplier
is 2, so this expression does not furnish a contraction argument.

## 6. Formal-status boundary

The checked Lean development proves finite actual-Hilbert contrast extraction,
exact signed arithmetic observations, normalized-head energy completion,
and odd-divisor-sum invariance under even corrections. The coordinator
performed serialized verification. It additionally checked the actual
Möbius synthesis, its coprimality mask and exact finite odd moment, the
positive moment normalization, the complete summable contrast series and
its exact energy, and the factorial-sieve contrast limit zero. The reported
axiom audits contain only propext, Classical.choice and Quot.sound.

The infinite closed-space projection identities and the precise legal
closure gap remain ordinary mathematical derivations in this note. They
are not asserted to be kernel checked. The odd-only version's product
formula and its separate full-energy bounds remain ordinary derivations;
the all-divisor variant described next is the one attached to the checked
infinite contrast limit. RH remains open.

### Additional checked development and the remaining full-energy test

`ParetoParitySieveMass.lean` proves actual factorial coprime-mass exhaustion
and the exact scalar centered-variance limit. Both have passed the
coordinator's Lean check.

The checked `ParetoSieveMobiusBridge.lean` uses the slightly simpler all-divisor finite
coefficients -a μ(d), for d|P and d>1, then adds a modulus-two head correction.
The odd coefficients are identical to those above. Extra even coefficients
do not change an odd-site divisor mask, so the relaxed contrast energy is
identical. The module connects an actual finite legal Hilbert vector to
the coprimality mask, proves the finite odd moment M satisfies

    (1+S) M = S-R_(2P),

proves M>0 if 3|P, and normalizes the odd moment exactly with a=1/M.
Its finite contrast extraction is genuinely attached to synthesized
coefficients. The checked `ParetoSieveContrastClosure.lean` then establishes
summability and an exact evaluation of the entire actual contrast series,
and proves `factorial_sieve_fullOddPairContrast_tendsto_zero`.
The separate all-divisor family's pointwise
behavior is not the logarithmic behavior of the odd-only family described
in Section 4; the equality claimed between the families is only their
odd divisor masks and contrast energies after the common head normalization.

The all-divisor candidate also has a direct ordinary full-energy obstruction.
For even P let B_total=∏_(prime ℓ|P)(1-1/ℓ), M=(S-R_(2P))/(S+1), a=1/M.
Its raw reciprocal head is a(1-B_total), and its normalized coefficient at
modulus two is a+2(κ-a(1-B_total)). Therefore its actual value at site two is

    F(2)=a(1-2B_total).

When 6|P, B_total<=1/3 and 0<M<1, so F(2)>1/3 and ||F||²>1/54.
Thus the actual all-divisor construction cannot supply vanishing full-tail
energy either. This bound and the Euler product evaluation of its reciprocal
head are ordinary mathematical statements here. A separate
`ParetoSieveFullEnergy.lean` supplies the exact site-two identity
F(2)=2*sieveMobiusHead(P,a)-a and the complete-tail lower bound
(2*sieveMobiusHead(P,a)-a)^2/6 <= ||F||², without the Euler-product
evaluation of its head. Its candidate verification completed successfully together with the
other eight modules, with standard-foundation axiom audits; consult the
coordinator's final receipt for installed-module publication acceptance. No full-norm convergence or RH conclusion follows
from the checked vanishing contrast result.
