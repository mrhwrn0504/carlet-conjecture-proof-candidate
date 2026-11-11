#!/usr/bin/env python3
"""Exact supplementary verifier for the Carlet proof-candidate manuscript.

Checks:
  * irreducibility of the n=29 and n=31 defining binary polynomials (Rabin criterion),
  * binary rank of each published basis,
  * complete subspace-polynomial coefficients via the standard recurrence,
  * exhaustive reciprocal sum over each nonzero subspace,
  * exact numerical inequalities used at k=16,17,18 and the analytic large-k gateway.

No floating point arithmetic is used for certificate verification.
"""
from math import comb
from fractions import Fraction


def deg(a: int) -> int:
    return a.bit_length() - 1


def poly_mod(a: int, mod: int) -> int:
    dm = deg(mod)
    while a and deg(a) >= dm:
        a ^= mod << (deg(a) - dm)
    return a


def poly_mul_raw(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
    return out


def poly_mul(a: int, b: int, mod: int) -> int:
    return poly_mod(poly_mul_raw(a, b), mod)


def poly_square(a: int, mod: int) -> int:
    return poly_mul(a, a, mod)


def poly_gcd(a: int, b: int) -> int:
    while b:
        a, b = b, poly_mod(a, b)
    return a


def gf_pow(a: int, e: int, mod: int) -> int:
    out = 1
    while e:
        if e & 1:
            out = poly_mul(out, a, mod)
        e >>= 1
        if e:
            a = poly_square(a, mod)
    return out


def gf_inv(a: int, n: int, mod: int) -> int:
    if a == 0:
        raise ZeroDivisionError
    return gf_pow(a, (1 << n) - 2, mod)


def irreducible_prime_degree(mod: int, n: int) -> bool:
    # For prime n, Rabin: x^(2^n)=x mod p and gcd(p, x^2-x)=1.
    x = 0b10
    y = x
    for _ in range(n):
        y = poly_square(y, mod)
    if y != x:
        return False
    x2_minus_x = poly_square(x, mod) ^ x
    return poly_gcd(mod, x2_minus_x) == 1


def binary_rank(vecs):
    pivots = {}
    for x in vecs:
        y = x
        while y:
            p = y.bit_length() - 1
            if p in pivots:
                y ^= pivots[p]
            else:
                pivots[p] = y
                break
    return len(pivots)


def linpoly_eval(coeffs, x, mod):
    # coeffs[i] * x^(2^i)
    y = x
    out = 0
    for c in coeffs:
        out ^= poly_mul(c, y, mod)
        y = poly_square(y, mod)
    return out


def subspace_polynomial(basis, mod):
    # Start L_{0}(X)=X => [1].
    coeffs = [1]
    for v in basis:
        s = linpoly_eval(coeffs, v, mod)
        # L^2 + s L. Squaring shifts Frobenius exponent and squares coeffs.
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] ^= poly_mul(s, c, mod)
            new[i+1] ^= poly_square(c, mod)
        coeffs = new
    return coeffs


def reciprocal_sum(basis, n, mod):
    total = 0
    k = len(basis)
    # Gray-code enumeration so each step toggles one basis element.
    x = 0
    prev_gray = 0
    for m in range(1, 1 << k):
        g = m ^ (m >> 1)
        diff = g ^ prev_gray
        idx = (diff & -diff).bit_length() - 1
        x ^= basis[idx]
        prev_gray = g
        total ^= gf_inv(x, n, mod)
    return total


CERTS = [
    {
        'name': 'E_29,13', 'n': 29, 'mod': (1<<29) | (1<<2) | 1,
        'basis': [
            0x00000001,0x0236c002,0x17b15004,0x16f41008,0x0aa45010,
            0x17b08020,0x178f8040,0x152d9080,0x0b024100,0x1ecb9200,
            0x11e0c400,0x092bd800,0x0561e000],
        'coeffs': [
            0x1a8d2e2f,0x00000000,0x0b39aa9c,0x0f919f54,0x06a764cc,
            0x0d93d023,0x0cfe406e,0x02d45aa5,0x03f76408,0x1bc649a2,
            0x10330d40,0x191ffaf2,0x0a266fda,0x00000001],
    },
    {
        'name': 'E_29,14', 'n': 29, 'mod': (1<<29) | (1<<2) | 1,
        'basis': [
            0x00000001,0x00538402,0x1abd8404,0x18eb0408,0x1aec0010,
            0x0d550020,0x15c60040,0x1f908480,0x14320500,0x04958200,
            0x13470800,0x0f4a1000,0x0f172000,0x14fe4000],
        'coeffs': [
            0x19ce08e7,0x00000000,0x08d8433a,0x04bd1933,0x121c9c05,
            0x1b5ac54f,0x046f1aa3,0x1b021f2d,0x1674a568,0x0eee40d5,
            0x037b879d,0x010d3c06,0x1b2e2c21,0x02427c2c,0x00000001],
    },
    {
        'name': 'E_31,14', 'n': 31, 'mod': (1<<31) | (1<<3) | 1,
        'basis': [
            0x00000001,0x3b088937,0x171012ec,0x6afce627,0x5e288246,
            0x4d96a9a8,0x4bf132d0,0x59374007,0x39117efd,0x460fc715,
            0x1beb9677,0x566e2dcd,0x19437aab,0x00058364],
        'coeffs': [
            0x1b99e28a,0x00000000,0x435fe9c9,0x04ecca32,0x148e3fe3,
            0x79802dca,0x32fcb2ff,0x0019ea0d,0x3038b402,0x7f441af6,
            0x18ecd503,0x347b8d50,0x285c194d,0x48766441,0x00000001],
    },
]


def N(k):
    return k*(k-1)//2 + 3*(k-1)


def beta_integer(k):
    return (1 << (N(k)+2)) * comb(N(k)-1, k-2)


def check_numerics():
    print('\nNumerical gateway checks')
    # Exact powers sufficient for manuscript inequalities.
    assert comb(183,15) < (1<<72)
    assert comb(164,14) < (1<<66)
    # k=17,n=35: beta < 2^258 and q^(15/2) squared = 2^(35*15).
    beta17 = beta_integer(17)
    assert beta17 < (1<<258)
    # Prove ratio < 1/16 without irrational arithmetic by squaring:
    # (beta/q^(15/2))^2 < 1/256 iff beta^2 * 256 < q^15.
    assert beta17*beta17*256 < (1 << (35*15))
    print('  k=17,n=35 middle ratio < 1/16: OK')

    beta16 = beta_integer(16)
    assert beta16 < (1<<233)
    # ratio beta/q^7 < 2^-26 at n=37.
    assert beta16 * (1<<26) < (1 << (37*7))
    print('  k=16,n=37 middle ratio < 2^-26: OK')

    # Analytic exponent gateway at k=18: -k^2/4+9k/2-2 = -2;
    # doubled to avoid fractions: -k^2/2+9k-4 <= -4 for k>=18.
    for k in range(18, 200):
        twice = -k*k//2 + 9*k - 4 if (k*k)%2==0 else None
        # k^2 even for k even, but use rational check generically.
        val = Fraction(-k*k, 4) + Fraction(9*k,2) - 2
        assert val <= -2
    print('  analytic exponent <= -2 for k>=18 (checked 18..199; derivative proof in paper): OK')


def main():
    seen_fields = set()
    for cert in CERTS:
        n, mod = cert['n'], cert['mod']
        if (n,mod) not in seen_fields:
            ok = irreducible_prime_degree(mod,n)
            print(f'GF(2^{n}) modulus irreducible: {ok}')
            assert ok
            seen_fields.add((n,mod))
        rank = binary_rank(cert['basis'])
        print(f"{cert['name']} rank = {rank}")
        assert rank == len(cert['basis'])
        coeffs = subspace_polynomial(cert['basis'],mod)
        assert coeffs == cert['coeffs'], (cert['name'], coeffs, cert['coeffs'])
        assert coeffs[1] == 0
        print(f"{cert['name']} subspace polynomial: exact match; X^2 coefficient = 0")
        s = reciprocal_sum(cert['basis'], n, mod)
        print(f"{cert['name']} exhaustive reciprocal sum = 0x{s:x}")
        assert s == 0
    check_numerics()
    print('\nALL CHECKS PASSED')

if __name__ == '__main__':
    main()
