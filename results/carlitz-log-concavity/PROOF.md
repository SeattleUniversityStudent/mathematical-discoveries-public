# A failure of log-concavity for Carlitz composition lengths

## Statement and definitions

Let a(n,k) be the number of ordered lists of k positive integers with sum n and unequal adjacent entries. Set a(0,0)=1 and a(n,0)=0 for n>0. A row is log-concave if a(n,k)^2 >= a(n,k-1)a(n,k+1) for every k.

For every integer m >= 104, the row with n=3m+2 fails this inequality at k=2m. In particular,

```
a(314,207) = 10094513
a(314,208) = 32552
a(314,209) = 105
32552^2 = 1059632704 < 1059923865 = 10094513 * 105.
```

The difference between the middle square and the neighbor product is -291161. No assertion of global least size is made. Unimodality, which is weaker than log-concavity, is not settled by this result.

## Three endpoint formulas

For every integer m >= 2, put n=3m+2. Then

```
A = a(n,2m+1) = m+1,
B = a(n,2m)   = m(3m+1),
C = a(n,2m-1) = (m^4+114m^3-277m^2+426m-312)/24.
```

Every unequal positive pair has sum at least 3. Pairing successive entries therefore gives minimum sum floor(3k/2) at length k; an alternating list starting with 1 attains it. Consequently 2m+1 is the largest feasible length at size 3m+2. The formula for C does not apply at m=1, where a(5,1)=1.

## Finite transfer argument

Group an even-length list into consecutive ordered pairs (u,v). Such a pair has u != v and excess r=u+v-3 >= 0. If the preceding pair ended in p, require p != u. Use initial state p=0 with no restriction.

To count total excess at most 4, every pair has sum at most 7, so every entry is at most 6. The states 0,1,...,6 are therefore sufficient exactly. State 0 is initial only.

For r=0,...,4 define the 7-by-7 matrix T_r by

```
T_r[p,v] = 1  if v>=1, u=r+3-v>=1, u!=v, and (p=0 or p!=u),
T_r[p,v] = 0  otherwise.
```

Let v_s(m) count lists of m pairs and total excess s, as a row vector indexed by the last entry. Set v_0(0)=e_0 and v_s(0)=0 for s>0. Appending the last pair gives

```
v_s(m+1) = sum_{r=0}^s v_{s-r}(m) T_r.
```

Each list has exactly one such pairing, so the recurrence neither omits nor repeats lists. With V_s(y)=sum_{m>=0} v_s(m)y^m it gives

```
V_s = delta_{s,0} e_0 + y sum_{r=0}^s V_{s-r} T_r.
```

The matrix T_0 is idempotent. Its rows 1 and 2 stay at their own states, and each other row goes once to each of states 1 and 2. Hence

```
(I-y T_0)^(-1) = I + y T_0/(1-y).
```

In particular V_s=N_s/(1-y)^(s+1) with finite polynomial row vectors N_s given by

```
N_0 = e_0 ((1-y)I+y T_0),
N_s = y sum_{r=1}^s N_{s-r} T_r ((1-y)I+y T_0)(1-y)^(r-1),  s>=1.
```

Put E_s(m)=a(3m+s,2m) and O_s(m)=a(3m+1+s,2m+1). Summing over the terminal state gives the even projection. An odd list appends c=r+1, with excess r, allowed precisely when the preceding state differs from c. Thus

```
sum_m E_s(m)y^m = sum_p V_s[p],
sum_m O_s(m)y^m = sum_{r=0}^s sum_{p!=r+1} V_{s-r}[p].
```

The initial state also handles m=0. Substitution in the finite recurrence gives the following numerator polynomials, all over (1-y)^(s+1):

| s | Even numerator | Odd numerator |
|---|---|---|
| 0 | 1+y | 1 |
| 1 | 2y+2y^2 | 1 |
| 2 | 4y+2y^2 | 1+4y-3y^2-y^3 |
| 3 | 4y+8y^2+4y^3-6y^4-2y^5 | 1+5y-y^3-4y^4 |
| 4 | 6y+16y^2-2y^3+4y^4-4y^5-10y^6 | 1+10y+3y^2-12y^3+2y^4-3y^5 |

The full matrices and state numerator vectors are in `algebra.json`. The file `certify.py` checks all 35 state identities

```
N_s = delta_{s,0} e_0 (1-y)^(s+1)
      + y sum_{r=0}^s N_{s-r} T_r (1-y)^r,
```

and all 10 projection identities using exact polynomial arithmetic. The recurrence has a unique solution in formal power series, since the right-hand transition term is multiplied by y. These finite identities establish the numerator formulas for every m; they do not extrapolate from finitely many evaluated coefficients.

Now A=O_1(m), B=E_2(m), and C=O_4(m-1). Extracting coefficients of the displayed rational functions gives A=m+1 and B=3m^2+m. For C it gives

```
C = binom(m+3,4) + 10 binom(m+2,4) + 3 binom(m+1,4)
    -12 binom(m,4) + 2 binom(m-1,4) -3 binom(m-2,4).
```

For m>=2 every top argument is nonnegative. The polynomial definition of binomial(t,4) agrees with the ordinary value, including zero for 0<=t<4. Expanding gives the stated quartic.

## Infinite family of violations

Substitution yields

```
24(AC-B^2) = m^5-101m^4-307m^3+125m^2+114m-312.
```

On writing m=104+t, the right side becomes

```
t^5+419t^4+65837t^3+4598485t^2+120548802t+6987864.
```

Every coefficient is positive. Thus AC>B^2 for every integer t>=0. At m=104 this gives the three explicit coefficients above.

## Reproducible exact computations

All three programs use only the Python standard library and arbitrary-precision integers or exact rational numbers. `RERUN.json` gives the commands and log filenames.

- `algebra.py` constructs the transfer matrices and state polynomials and compares 493 coefficients with the frozen reference rows through n=150.
- `verify_counterexample.py` computes the three target counts using a separate last-part dynamic program. If d(n,k,j) counts lists ending in j, its recurrence is d(n,k,j)=a(n-j,k-1)-d(n-j,k-1,j). This uses no paired-excess formulas.
- `certify.py` imports neither counting program. It reconstructs all 245 matrix entries by enumerating pairs, checks all 35 state identities and 10 projections, checks the three closed-form polynomials and the positive shifted polynomial, and compares with the last-part count. It also checks nonfailure for 1<=m<=103 within this particular triple family.

The frozen input `reference_coefficients.json` has 274188 bytes and SHA-256 `2197cb823c377b63524881cd6ec2748cf04773ef63501ff7a2284c8c133f5fe4`. This table is used only as an auxiliary finite check; the formal-series argument and target dynamic program do not rely on its correctness. All programs and checks come from the same author; they are not external review.

## Sources and limitations

1. A. Knopfmacher and H. Prodinger, *On Carlitz Compositions*, European Journal of Combinatorics 19 (1998), 579-589. DOI: [10.1006/eujc.1998.0216](https://doi.org/10.1006/eujc.1998.0216). [Accessible text](https://mathweb.ucsd.edu/~ebender/comp.papers/119-Carlitz_plus.pdf). The definition, last-part recurrence and bivariate generating function are established material. The eventual-unimodality discussion concerns a weaker property than the log-concavity tested here.
2. H. S. Wilf, *The distribution of run lengths in integer compositions*, Electronic Journal of Combinatorics 18(2) (2011), P23. DOI: [10.37236/2019](https://doi.org/10.37236/2019); [arXiv:0906.5196](https://arxiv.org/abs/0906.5196). The forbidden-run framework includes ordinary Carlitz enumeration. No finite log-concavity conclusion from that framework is assumed here.

The exact prior-art status of the negative result is undetermined. A bounded literature search is not a complete priority check. The separate fixed comparison catalogue was screened by keywords only; underlying manuscripts were not exhaustively compared. No global least counterexample, row unimodality result, human review, or formal proof-assistant compilation is supplied.
