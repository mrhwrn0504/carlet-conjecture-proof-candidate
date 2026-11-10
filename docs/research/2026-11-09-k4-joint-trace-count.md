# K4 joint trace-count route (2026-11-09)

## Status

**Mathematical reduction:** established in the current Lean branch.
**Large-degree analytic existence argument:** derived below from the rational-function Weil bound.
**Lean formalization of the character-sum estimate:** OPEN.
**Finite odd degrees 7, 9, 11:** explicit polynomial-basis witnesses are now checked by the reproducibility script, including all three Artin–Schreier equations for z,s,v; Lean verification remains OPEN.

This note does not change the status of the full Carlet theorem. It records a possible independent completion of the V7/K4 trace-witness branch.

## Target

For a finite field K of characteristic two, write Q = |K| and
`q(t) = t^2 + t`, `D(t) = q(t)^3 + q(t) + 1`.

Find t in K such that

- q(t) != 0,
- q(t) + 1 != 0,
- D(t) != 0, and
- Tr(1/D(t)) = Tr(q(t)^2/D(t)) = Tr(t^6/D(t)) = 0.

The existing theorem `Carlet.QuadraticV7.hasZeroSumSubspace_four_of_k4V7_traceWitness`
turns such a witness directly into `HasZeroSumSubspace K 4`.

## Large-degree count

Let
`T = {t in K : q(t) (q(t)+1) D(t) != 0}`.
The three excluded polynomials have degrees 2, 2, and 6, so
`|T| >= Q - 10`.

In characteristic two,
`D(t) = t^6 + t^5 + t^4 + t^3 + t^2 + t + 1`,
and
`D'(t) = (t^2+t+1)^2`.
If D and D' had a common root, then q(t)=1, which would give
`D(t)=1+1+1=1`, a contradiction. Thus D is square-free and has six distinct roots over the algebraic closure.

For each nonzero `(a,b,c) in F_2^3`, put
`N_{a,b,c}(t) = a + b q(t)^2 + c t^6`.
Since `q(t)^2=t^4+t^2`,
`N_{a,b,c}(t)=c t^6 + b t^4 + b t^2 + a`.
This polynomial is nonzero for nonzero (a,b,c), has degree at most six, and is not divisible by D:
- if its degree is less than six, divisibility is impossible;
- if its degree is six, divisibility would force it to equal the monic degree-six polynomial D, but its t^5 coefficient is zero whereas that of D is one.

Consequently, D has at least one root at which N_{a,b,c} is nonzero. Since D is square-free, the rational function
`r_{a,b,c}(t)=N_{a,b,c}(t)/D(t)`
has a simple pole over the algebraic closure.

A rational function of the form `h(t)^2-h(t)=h(t)^2+h(t)` cannot have a simple pole: at any pole of h of order m, h^2+h has pole order 2m. Hence every `r_{a,b,c}` is non-degenerate for the characteristic-two additive Weil bound.

### Imported Weil estimate

The exact rational-function estimate used here is **Theorem 2** of Carlos J. Moreno and Oscar Moreno, *Exponential Sums and Goppa Codes: I*, Proceedings of the American Mathematical Society 111(2) (1991), 523–531, DOI: 10.1090/S0002-9939-1991-1028291-1. In their notation, if `r=f/g` is not of the form `h^p-h` over the algebraic closure, and `t_g` is the number of distinct roots of `g` over the algebraic closure, then
`|sum_{x in F_Q, g(x)!=0} psi(r(x))| <= (max(deg f,deg g)+t_g^*-2) sqrt(Q) + delta`,
where `t_g^*=t_g` and `delta=1` when `deg f <= deg g`; otherwise `t_g^*=t_g+1` and `delta=0`.

The same statement is reproduced as Lemma 9 by Yuan and Ding, *Secret Sharing Schemes From Three Classes of Linear Codes*, IEEE Transactions on Information Theory 52(1) (2006), pp. 206–212, citing Moreno–Moreno as their reference [13]. See Theorem 2 in the original paper and Lemma 9, pp. 208–209, in the secondary source: https://www.cse.ust.hk/faculty/cding/JOURNALS/it061.pdf (PDF lines 137–156 in the extracted text).

Here `deg N <= deg D = 6` and `t_D=6`, so `t_g^*=6`, `delta=1`, and each of the seven nontrivial sums over `D(t)!=0` is bounded by
`10 sqrt(Q) + 1`.
Passing from `D(t)!=0` to T removes at most four further field elements (the roots of q and q+1). Thus each nontrivial sum over T is bounded by
`10 sqrt(Q) + 5`.

### Character orthogonality

Let `psi(x)=(-1)^Tr(x)`, where Tr is the absolute trace K -> F_2, and let M be the number of t in T satisfying all three trace-zero conditions. The three trace indicators give
`M = (1/8) sum_{(a,b,c) in F_2^3} sum_{t in T} psi((a+b q(t)^2+c t^6)/D(t))`.

The zero triple contributes |T|. The other seven triples have absolute value at most `10 sqrt(Q)+5`. Therefore
`M >= (|T| - 7(10 sqrt(Q)+5))/8 >= (Q - 70 sqrt(Q) - 45)/8`.

If `Q >= 2^13 = 8192`, then `sqrt(Q) <= Q/90`, and hence
`Q - 70 sqrt(Q) - 45 >= 2Q/9 - 45 > 0`.
Thus M > 0.

**Conditional-to-standard-theorem conclusion:** accepting the cited rational-function Weil estimate, the K4 trace witness exists for every finite field of characteristic two with `Q=2^n`, `n >= 13`. In particular, it exists for every odd n >= 13 in the original Carlet range.

## Small odd-degree witness candidates

The following are polynomial-basis certificates from direct finite-field arithmetic. Let alpha denote the residue class of X modulo the listed irreducible polynomial. The three displayed trace inputs are respectively `1/D`, `q^2/D`, and `t^6/D`; each has absolute trace zero.

| n | Irreducible polynomial | t | q=t^2+t | D=q^3+q+1 | (1/D, q^2/D, t^6/D) |
|---|---|---|---|---|---|
| 7 | X^7+X+1 | alpha | alpha^2+alpha | alpha^6+alpha^5+alpha^4+alpha^3+alpha^2+alpha+1 | (alpha^6, alpha^4+alpha^3+alpha^2+alpha, alpha^6+alpha^5) |
| 9 | X^9+X+1 | alpha^5+alpha^4+alpha^2 | alpha^8+alpha^5+alpha | alpha^8+alpha^3+alpha^2+alpha+1 | (alpha^8+alpha^7+alpha^5+alpha, alpha^8+alpha^7+alpha^3+alpha^2, alpha^8+alpha^7+alpha^5+alpha^4+alpha) |
| 11 | X^11+X^2+1 | alpha^6+alpha^3+alpha^2 | alpha^4+alpha^2+alpha | alpha^10+alpha^9+alpha^8+alpha^5+alpha^2+1 | (alpha^10+alpha^9+alpha^8+alpha^6+alpha^5+alpha^3+1, alpha^8+alpha^6+alpha^4+alpha^2, alpha^7+alpha^2) |

These certificates are computational leads, not yet Lean theorems. They can be checked by polynomial reduction modulo the displayed irreducible polynomial, followed by the trace sum
`Tr(x)=x+x^2+...+x^{2^{n-1}}`.

## Next formalization tasks

1. Formalize the characteristic-two rational Weil bound in a reusable form, or formalize the corresponding Artin–Schreier curve estimate with the exact constant above.
2. Prove the polynomial facts `D'= (q+1)^2`, `gcd(D,D')=1`, and `D does not divide N_{a,b,c}` uniformly for nonzero (a,b,c).
3. Formalize character orthogonality and the lower bound for M.
4. Add exact Lean certificates for n=7, 9, 11 and transfer them to arbitrary fields of the same cardinality.
5. Compose the resulting trace-witness theorem with the existing K4 bridge.

Do not mark the V7 trace-existence problem PROVED until steps 1–4 have been checked in Lean.

## Relationship to the already-proved K4 family

A further source audit found that the repository already proves the general odd-degree K4 existence theorem by a different route:

- `K4NormOneThetaBridgeProbe.lean` proves `k4NormOneTheta_hasZeroSum_four_large` for odd n >= 11 using a four-dimensional trace plane, norm-one pair counting, and elliptic-curve Hasse bounds.
- `K4AllOddDegreesProbe.lean` combines that result with the small odd-degree constructions and proves `hasZeroSumSubspace_four_of_odd_card` for every odd n >= 7.
- `K5NormOneConstructionProbe.lean` imports the low-dimensional assembly that uses this K4 result.

Therefore the joint rational-character-sum argument in this note is **not needed to establish the main Carlet conjecture's k=4 case**. Its value is narrower: it could independently prove the exact three rational trace conditions used by the V7 single-parameter K4 chain. Keep this V7 subproblem separate from the already-proved general K4 existence theorem.

The existing K4 proof is also quantitatively stronger for the general existence problem: its Hasse/trace-plane route starts at `n >= 11`, whereas the generic rational-function Weil estimate above gives `n >= 13`. The reason to retain this new route is not a better K4 threshold; it is that it targets the exact V7 one-parameter trace witness rather than merely producing some four-dimensional zero-sum subspace.

## Combined mathematical consequence and proof-status boundary

Combining the analytic estimate with the three finite certificates gives the following ordinary-mathematics conclusion:

> For every odd integer n >= 7 and every finite field K of characteristic two with |K| = 2^n, there exists t in K satisfying all three V7 rational trace-zero conditions and all three required nonvanishing conditions.

For n >= 13 this follows from the Moreno–Moreno rational-function estimate and the positive lower bound for M. For n = 7, 9, 11 it follows from the explicit polynomial-basis witnesses, after transporting them along a finite-field isomorphism.

This is a mathematical proof conditional only on the standard cited exponential-sum theorem and the finite arithmetic certificates. **It is not yet a Lean-verified theorem in this repository.** The Python script checks the finite certificates reproducibly, but does not replace a formal proof. The separate already-formalized general K4 existence theorem remains the current Lean result.


## Alternative large-degree proof: six-pole genus-five curves

A second derivation gives the same (10\sqrt Q+1) character-sum bound directly from the Hasse–Weil theorem for curves. Unlike the rational-function estimate above, this route identifies the exact genus of each of the seven Artin–Schreier covers.

Put (Q=2^n), (q(t)=t^2+t), and
[
D(t)=q(t)^3+q(t)+1=t^6+t^5+t^4+t^3+t^2+t+1.
]
For ((a,b,c)\in\mathbb F_2^3\setminus\{(0,0,0)\}), set
[
A_{a,b,c}(t)=a+bq(t)^2+ct^6,
\qquad
F_{a,b,c}(t)=A_{a,b,c}(t)/D(t).
]

### All six poles are simple

The denominator factors over (mathbb F_2) as
[
D(t)=(t^3+t+1)(t^3+t^2+1)=P_-(t)P_+(t).
]
Both cubic factors are irreducible over (mathbb F_2), since neither has a root in (mathbb F_2), and they are distinct. Thus (D) is square-free and has six distinct roots over the algebraic closure.

The following table gives the remainders of (A_{a,b,c}) modulo the two cubic factors. Every entry is nonzero, so (gcd(A_{a,b,c},D)=1) for every nonzero triple.

| ((a,b,c)) | (A_{a,b,c}\bmod P_-) | (A_{a,b,c}\bmod P_+) |
|---|---|---|
| 001 | (t^2+1) | (t^2+t) |
| 010 | (t) | (t+1) |
| 011 | (t^2+t+1) | (t^2+1) |
| 100 | (1) | (1) |
| 101 | (t^2) | (t^2+t+1) |
| 110 | (t+1) | (t) |
| 111 | (t^2+t) | (t^2) |

Also, (deg A_{a,b,c}\le6=deg D), so (F_{a,b,c}) has no pole at infinity. It has exactly six geometric poles, all simple.

Consider the Artin–Schreier curve
[
C_{a,b,c}:\quad y^2+y=F_{a,b,c}(t).
]
It is geometrically connected: a nonconstant function (h^2+h) cannot have a simple pole, because at a pole of (h) of order (m), its pole order is (2m). The Artin–Schreier genus formula therefore gives
[
g(C_{a,b,c})
=\frac{2-1}{2}\left(-2+6(1+1)\right)=5.
]
This is the standard genus formula for Artin–Schreier extensions; see Shawn Farnell, *Artin–Schreier Curves* (2010), Proposition 2.2.1 and Lemma 2.2.3, pp. 8–9:
https://api.mountainscholar.org/server/api/core/bitstreams/b29bf91f-4848-4aca-b33f-e67f23037554/content

### Convert the curve point count into the character-sum bound

Let (\psi(x)=(-1)^{\operatorname{Tr}_{\mathbb F_Q/\mathbb F_2}(x)}), and define
[
S_{a,b,c}=\sum_{t\in\mathbb F_Q,\ D(t)\ne0}\psi(F_{a,b,c}(t)).
]
Write (r=\#\{t\in\mathbb F_Q:D(t)=0\}), so (r\le6). For each non-pole finite (t), the equation (y^2+y=F(t)) has (1+\psi(F(t))) solutions. Each rational simple pole contributes exactly one point on the smooth projective model, because it is totally ramified. At infinity the cover is unramified and (F(\infty)=c\in\mathbb F_2), so its fibre has either zero or two rational points; call this number (e_\infty\in\{0,2\}).

Consequently,
[
\#C_{a,b,c}(\mathbb F_Q)=Q+S_{a,b,c}+e_\infty.
]
The Hasse–Weil bound for a genus-five curve gives
[
\left|\#C_{a,b,c}(\mathbb F_Q)-(Q+1)\right|
\le 2\cdot5\sqrt Q=10\sqrt Q.
]
Since (e_\infty\in\{0,2\}), it follows that
[
\boxed{|S_{a,b,c}|\le10\sqrt Q+1.}
]
The usual Hasse–Weil estimate for curves is also summarized in the course notes cited above, Corollary 23.1.4, pp. 107–108.

### Count the simultaneous trace-zero parameters

Let (N_n) count all (t\in\mathbb F_Q) with (D(t)\ne0) and
[
\operatorname{Tr}(D(t)^{-1})
=\operatorname{Tr}(q(t)^2D(t)^{-1})
=\operatorname{Tr}(t^6D(t)^{-1})=0.
]
Character orthogonality gives
[
8N_n=Q-r+
\sum_{(a,b,c)\ne(0,0,0)}S_{a,b,c}.
]
There are seven nonzero triples, so
[
\boxed{N_n\ge\frac{Q-70\sqrt Q-13}{8}.}
]
For (n\ge13), (Q\ge8192), hence (\sqrt Q>90) and
[
Q-70\sqrt Q-13
=(\sqrt Q)(\sqrt Q-70)-13
>90\cdot20-13>0.
]
Thus (N_n>0).

For odd (n), any such (t) automatically satisfies the other two nonvanishing conditions required by the K4 bridge:
- If (q(t)=0), then (t=0) or (1), (D(t)=1), and (operatorname{Tr}(D(t)^{-1})=\operatorname{Tr}(1)=1), contradiction.
- If (q(t)=1), then (t) is a root of (X^2+X+1), which lies in (mathbb F_4); (mathbb F_4\subseteq\mathbb F_{2^n}) only when (2\mid n), impossible for odd (n).

Therefore the three rational trace conditions have a witness for every odd (n\ge13), with (q(t)\ne0), (q(t)+1\ne0), and (D(t)\ne0).

### Corrected explicit Artin–Schreier roots in degrees 7, 9, 11

The original finite-field trace script checked the three traces but did not check the displayed roots (z,s,v). I independently recomputed those roots for the exact (t)-values in the script, then updated `scripts/verify_k4_small_witnesses.py` so it now checks all three equations
[
z^2+z=D^{-1},\qquad s^2+s=q(q+1)z,\qquad v^2+v=qs
]
as well as irreducibility, nonvanishing and the three traces.

Let (\alpha) be the residue class of (X) modulo the irreducible polynomial shown.

| (n) | (t) | (z) | (s) | (v) |
|---|---|---|---|---|
| 7 | (\alpha) | (\alpha^6+\alpha^5+\alpha^4+\alpha^3+\alpha) | (\alpha^6+\alpha^5+\alpha^4+\alpha^3) | (\alpha^4) |
| 9 | (\alpha^5+\alpha^4+\alpha^2) | (\alpha^8+\alpha^5+\alpha^4+\alpha^2) | (\alpha^8+\alpha^7+\alpha^6+\alpha^3+\alpha^2+\alpha) | (\alpha^8+\alpha^7+\alpha^6+\alpha^5+\alpha^4+\alpha^3+\alpha^2) |
| 11 | (\alpha^6+\alpha^3+\alpha^2) | (\alpha^{10}+\alpha^9+\alpha^8+\alpha^6+\alpha) | (\alpha^{10}+\alpha^9+\alpha^4+\alpha^3+\alpha^2) | (\alpha^9+\alpha^8+\alpha^7+\alpha^6+\alpha^5+\alpha^3+\alpha^2) |

The reproducibility script reports all three trace values as `[0, 0, 0]` and all three Artin–Schreier equations as true for each row. This is still a computational certificate, not yet a Lean theorem.

### What this closes, and what remains

**Ordinary mathematics:** the genus-five Hasse–Weil argument covers every odd (n\ge13); the corrected finite certificates cover (n=7,9,11). Together they establish the V7 three-trace existence statement for every odd (n\ge7), assuming the standard Artin–Schreier genus formula and Hasse–Weil theorem.

**Lean:** the exact trace-witness existence theorem remains OPEN until the genus/point-count/Weil estimate and the three small certificates are formalized and checked by Lean. The vendored AINTLIB Hasse-bound module in this repository is for elliptic curves (genus one), not arbitrary genus-five curves. A promising external reference is [AxiomMath/Weil](https://github.com/AxiomMath/Weil), which formalizes the general Weil conjectures, but it currently uses Lean `v4.34.0-rc2` and a Stacks dependency, while this repository is pinned to Lean `v4.33.0`. Treat that as a separate integration experiment, not a drop-in import.

This V7 result is a separate strengthening of the one-parameter construction. It does not change the proof-status boundary already recorded above: the repository's general odd-degree K4 existence theorem is established by a different norm-one/trace-plane route, and the main Carlet proof must be assessed independently of this V7 branch.
