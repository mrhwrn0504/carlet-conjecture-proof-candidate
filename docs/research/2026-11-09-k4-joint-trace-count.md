# K4 joint trace-count route (2026-11-09)

## Status

**Mathematical reduction:** established in the current Lean branch.
**Large-degree analytic existence argument:** derived below from the rational-function Weil bound.
**Lean formalization of the character-sum estimate:** OPEN.
**Finite odd degrees 7, 9, 11:** explicit polynomial-basis witnesses found computationally; these still need an independently checked Lean certificate before being labelled PROVED.

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

Yuan–Ding, *Secret Sharing Schemes From Three Classes of Linear Codes*, IEEE Transactions on Information Theory 52(1) (2006), Lemma 9, gives the following estimate. If `r=f/g` is not of the form `h^p-h` over the algebraic closure, t_g is the number of distinct roots of g over the algebraic closure, and `deg f <= deg g`, then
`|sum_{x in F_Q, g(x)!=0} psi(r(x))| <= (max(deg f,deg g)+t_g-2) sqrt(Q) + 1`.
Source: https://www.cse.ust.hk/faculty/cding/JOURNALS/it061.pdf (Lemma 9, pp. 208–209; PDF lines 139–156 in the extracted text).

Here `deg N <= deg D = 6` and `t_D=6`, so each of the seven nontrivial sums over `D(t)!=0` is bounded by
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

