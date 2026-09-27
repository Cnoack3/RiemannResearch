# Full finite logarithmic bootstrap and endpoint propagation

Continuation of `ba20efab4f7d02ff2ed484f1de9b78909c74e009`.

The finite bootstrap has no fixed logarithmic-exponent ceiling. The new
arithmetic provider proves, for every fixed real `a`, a constant `B_a >= 0`
such that

```math
|M(x)|\le B_a x(6+\log x)^{-a}\qquad(x\ge1).
```

Every arithmetic premise is discharged by existing checked providers,
ultimately `Quantitative.MediumPNT`. Constants and thresholds may depend
on `a`. A uniform stretched-exponential Mertens rate is not asserted.

## Exact finite estimate and the old loss

Put `T=log N`, `L=log(N/Y)`, and `q=|M(N)|T/N`. For positive integers
`Y<=N` and unrestricted positive `J`, the finite signed identity gives

```math
q\le \frac YN+A+\frac1J+\frac1{YJ}+A(H_J+1)
 +\frac{3D}{(1+L)^p}+2A(L+\log4+5).
```

Here the two provider premises are

```math
|M(u)|\le Au\quad(u\ge Y),\qquad
|\psi(u)-u|\le \frac{Du}{(1+\log u)^{p+2}}\quad(u\ge1).
```

`R_inverseLogPower_bound` supplies the second premise for every natural
`p` from the full MediumPNT exponential estimate. The signed prime head
retains exponent `p` after reserving two inverse-log powers for the
summable reciprocal kernel; `M_log_bootstrap_finite_power` records the
resulting complete finite estimate.

The old choice `J=floor(sqrt T)+1` left the positive majorant term `1/J`.
Together with `H_J<=J` and the first-pass Mertens input, that choice stops
at the three-halves logarithm. Replacing only the prime-error provider
cannot remove this term. This observation is about the displayed
majorant, and is not a lower bound for the actual Mertens function.

## Optimized finite induction

Set `t=sqrt T` and use

```math
Y=\lfloor N e^{-t}\rfloor,\qquad J=\lfloor e^t\rfloor+1.
```

The finite theorem imposes no upper bound on `J`. The logarithmic harmonic
bound gives `H_J+1<=4t` for the large cutoffs in the proof. For every fixed
natural `p`, eventually `t^p<=e^t`, so

```math
Yt^p\le N,\quad t^p\le J,\quad
\tfrac12t^2\le\log Y,\quad
t\le1+L,\quad L+\log4+5\le9t.
```

If the preceding global Mertens bound supplies `A t^(p+1)<=C`, the exact
scalar theorem gives

```math
q t^p\le3+23C+3D,
\qquad |M(N)|t^{p+2}\le(3+23C+3D)N.
```

Thus each finite application increases the square-root-log exponent by
one. Induction on the exponent, seeded by the established three-halves
bound, proves every fixed exponent. Natural-to-real globalization and
absorption of finitely many small arguments are proved separately in the
same module. This is induction on an exponent, not a circular induction
on `N`: the tail hypothesis covers all real `u>=Y`, including future ones.

## Complete endpoint rate

Write `F_{epsilon,M}` for the complete arithmetic Hilbert cutoff,
`f=dampedMobiusHalfRangeLimit (1/2) le_rfl`, and `L(M)=6+log(M+1)`.
The new endpoint theorem proves, for every fixed real `a`,

```math
\exists C_a\ge0\quad\forall M\ge0,\qquad
\|F_{1/2,M}-f\|_P\le C_a L(M)^{-a}.
```

There is therefore no largest fixed logarithmic endpoint exponent in the
new verified family. The earlier quarter-log theorem remains a valid
special case, but is no longer the strongest available rate.

The proof includes both the finite physical head and the infinite tail.
For each natural `k`, signed Abel summation preserves the Mertens saving
in the half-weighted prefix and the reciprocal density tail. The shift
`6+4k` keeps the comparison derivative positive; it is converted back to
the fixed shift six by an exponent-dependent constant. The existing
general logarithmic hyperbola optimization then gives an envelope
uniform over every conductor cutoff,

```math
|F_{1/2,M}(n)|\le K_k\sqrt n\,(6+\log n)^{-k/2}
```

for all sufficiently large physical `n`. The coordinate limit has the
same bound. The exact finite-head density-tail identity supplies every
fixed logarithmic squared-error exponent. The generic norm transfer
factors the excess logarithmic powers out of a square-log summable tail;
no infinite physical tail is omitted.

## Moving below one half

For **every fixed** `c>=0`, uniformly throughout the band

```math
0\le\delta=\tfrac12-\epsilon,
\qquad \delta\log(M+1)\le c\log(6+\log(M+1)),
```

the full vectors converge to `f` and their complete squared norms converge
to the half-endpoint energy. There is no largest fixed coefficient `c`.

The old scalar multiplier bound assumes endpoint exponent below one; it
cannot simply be invoked with an arbitrary larger exponent. The new
proof instead splits the centered signed Abel errors. For increasing
nonnegative weights with `w_0=1`, global error bound `B`, and tail error
bound `R` beyond `J<=N`, the finite inequality is

```math
\left\|\sum_{n=0}^Nw_nu_n-f\right\|
\le B(w_J-1)+2w_NR.
```

Take the auxiliary cutoff

```math
J(M)=\left\lfloor\exp\sqrt{\log(M+1)}\right\rfloor.
```

The scalar cutoff theorem proves `J(M)+1<=M` eventually,
`(J(M)+1)^delta -> 1`, and, for any fixed `k>2c`,

```math
(M+1)^\delta(6+\log(J(M)+1))^{-k}\longrightarrow0.
```

The last two statements make the two terms of the signed Abel budget
vanish. Uniform convergence in the entire band is proved, not just
convergence along one prescribed damping sequence.

## What is still missing

No fixed `epsilon<1/2` has newly established finite energy. All these
bands approach one half. The estimates do not supply finite energy at
positive dampings tending to zero and do not prove RH.

A specified stretched-exponential Mertens rate needs uniform control
over the bootstrap depth, constants, and thresholds. The family above
does not provide that control. For example, the comparison profile
`e^{-(log T)^2}` obeys every inverse-power bound in `T`, by the exact
identity

```math
T^a e^{-(\log T)^2}
=e^{a^2/4}e^{-(\log T-a/2)^2}\le e^{a^2/4},
```

yet it is not bounded eventually by `C exp(-d T^beta)` for fixed positive
`d,beta,C`. This comparison illustrates the quantifier gap; it is not an
assertion about the actual Mertens function. Retaining the original
MediumPNT exponential through a uniform tail-envelope bootstrap is a
further analytic/formalization obligation, not a new arithmetic premise
silently assumed here.

## Principal declarations

| Declaration | Content |
|---|---|
| `R_inverseLogPower_bound` | Every fixed prime-error inverse-log power |
| `M_log_bootstrap_finite_power` | Complete generalized finite signed bootstrap |
| `M_shiftedLog_all_nat_powers` | Global natural logarithmic Mertens powers |
| `M_shiftedLog_all_powers` | Global real logarithmic Mertens exponents |
| `dampedMobius_half_cutoffs_all_log_rate` | Every fixed full endpoint norm exponent |
| `signedVector_increasing_weight_split_le` | Centered signed Abel head/tail budget |
| `sqrtLogCutoff_band_facts` | Explicit intermediate-cutoff asymptotics |

The arithmetic base is the checked compatibility adaptation of the pinned
PNT+ MediumPNT source. The new steps use finite signed identities,
elementary exponential comparison, Abel summation, and integral/tail
comparison. No mathematical novelty claim or additional arithmetic axiom
is made.

## Verification record

The complete arithmetic, analytic, and moving-band assembly was checked
in serialized Lean job `job_YyryxvBAnMHl5OXcK1YXaMuV8cv-UbxS`, which
returned `exit_code=0` and `verified=true`. The endpoint axiom audit
reported only `propext`, `Classical.choice`, and `Quot.sound`.
Project publication additionally validates the actual module imports and
affected reverse dependencies through the final checkpoint.
