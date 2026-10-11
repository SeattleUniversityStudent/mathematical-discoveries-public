#!/usr/bin/env python3
"""REV-B-RQ4-b independent statement-only exact checks.

Mathematical input: STATEMENTS.md only, SHA256
5c70c3bcc8e2a626343221e2b6f5bb076b4eaae29dde58285fa632ae54fb1fae.
No producer material is read. The count algorithm is built directly from
positive ordered compositions and the unequal-adjacent condition.
Finite count checks do not establish the formulas for every m.
"""
from fractions import Fraction
from math import comb
import json
import signal
import time

signal.alarm(100)
START = time.perf_counter()
MAX_M = 120
MAX_N = 3 * MAX_M + 2
MAX_K = 2 * MAX_M + 1
BRUTE_MAX_N = 18
failures = []

def require(condition, name, details=None):
    if not condition:
        failures.append({'check': name, 'details': details})

def claimed_values(m):
    return {
        'A': m + 1,
        'B': m * (3 * m + 1),
        'C': Fraction(m**4 + 114*m**3 - 277*m**2 + 426*m - 312, 24),
    }

# D_k(s,v) counts admissible lists of length k, sum s, last entry v.
# Appending v to a list with sum s-v allows all predecessor lists except
# those whose own last entry is v. Thus D_k(s,v) = T_{k-1}(s-v)
# - D_{k-1}(s-v,v). No closed form or minimum-sum claim is used.
t0 = time.perf_counter()
previous = [[0] * (s + 1) for s in range(MAX_N + 1)]
previous_totals = [0] * (MAX_N + 1)
previous_totals[0] = 1
small_rows = {n: [int(n == 0)] for n in range(BRUTE_MAX_N + 1)}
targets = {
    (3*m+2, 2*m+offset): (m, label)
    for m in range(2, MAX_M + 1)
    for offset, label in [(1, 'A'), (0, 'B'), (-1, 'C')]
}
actual = {m: {} for m in range(2, MAX_M + 1)}
recurrence_cells_visited = 0
for k in range(1, MAX_K + 1):
    current = [[0] * (s + 1) for s in range(MAX_N + 1)]
    totals = [0] * (MAX_N + 1)
    for s in range(k, MAX_N + 1):
        row = current[s]
        total = 0
        for v in range(1, s - k + 2):
            recurrence_cells_visited += 1
            p = s - v
            predecessor_total = previous_totals[p]
            if predecessor_total:
                value = predecessor_total - (previous[p][v] if v <= p else 0)
                if value < 0:
                    raise AssertionError(('negative recurrence count', s, k, v))
                row[v] = value
                total += value
        totals[s] = total
        key = (s, k)
        if key in targets:
            m, label = targets[key]
            actual[m][label] = total
    if k <= BRUTE_MAX_N:
        for n in range(BRUTE_MAX_N + 1):
            small_rows[n].append(totals[n])
    previous, previous_totals = current, totals
count_seconds = time.perf_counter() - t0

# Fully independent small case enumeration: a subset of n-1 cut positions
# specifies each positive composition exactly once. Materialize parts, then
# filter adjacent equality. This enumerates even the rejected compositions.
t0 = time.perf_counter()
brute_compositions_examined = 1
brute_valid_compositions = 1
brute_rows = {0: [1]}
small_case_mismatches = []
for n in range(1, BRUTE_MAX_N + 1):
    counts = [0] * (n + 1)
    for mask in range(1 << (n - 1)):
        parts = []
        run = 1
        for bit in range(n - 1):
            if mask & (1 << bit):
                parts.append(run)
                run = 1
            else:
                run += 1
        parts.append(run)
        brute_compositions_examined += 1
        if all(x != y for x, y in zip(parts, parts[1:])):
            counts[len(parts)] += 1
            brute_valid_compositions += 1
    brute_rows[n] = counts
    for k in range(n + 1):
        if counts[k] != small_rows[n][k]:
            small_case_mismatches.append({'n':n, 'k':k, 'enumerated':counts[k], 'dp':small_rows[n][k]})
require(small_rows[0][0] == 1, 'empty_list_base_case')
require(all(v == 0 for v in small_rows[0][1:]), 'positive_length_zero_sum')
require(not small_case_mismatches, 'dp_vs_exhaustive_enumeration', small_case_mismatches)
brute_seconds = time.perf_counter() - t0

formula_mismatches = []
checked_family = []
for m in range(2, MAX_M + 1):
    predicted = claimed_values(m)
    require(set(actual[m]) == {'A','B','C'}, 'all_three_counts_present', m)
    for label in ('A','B','C'):
        if actual[m][label] != predicted[label]:
            formula_mismatches.append({'m':m,'label':label,'direct':actual[m][label],'claimed':str(predicted[label])})
    a,b,c = (actual[m][label] for label in ('A','B','C'))
    delta = b*b - a*c
    checked_family.append({'m':m,'n':3*m+2,'A':a,'B':b,'C':c,'B_squared_minus_AC':delta})
require(not formula_mismatches, 'three_formulas_direct_counts', formula_mismatches)
direct_inequality_failures = [row for row in checked_family if row['m'] >= 104 and row['B_squared_minus_AC'] >= 0]
require(not direct_inequality_failures, 'strict_negative_difference_direct_counts_m104_to_m120', direct_inequality_failures)

stated = {'C':10094513,'B':32552,'A':105}
require(actual[104] == stated, 'three_explicit_counts_n314', actual[104])
require(32552**2 == 1059632704, 'explicit_square')
require(10094513*105 == 1059923865, 'explicit_neighbor_product')
require(32552**2 - 10094513*105 == -291161, 'explicit_difference')

# Exact symbolic consistency audit of the supplied formulas, not an assertion
# that the counting formulas hold outside the directly checked finite range.
# Polynomials use ascending coefficient order.
def poly_multiply(p, q):
    out = [0] * (len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += a*b
    return out

def poly_subtract(p, q):
    return [(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0)
            for i in range(max(len(p),len(q)))]

def poly_evaluate(p, x):
    value = 0
    for c in reversed(p):
        value = value*x+c
    return value

A_poly = [1,1]
B_poly = [0,1,3]
C_numerator_poly = [-312,426,-277,114,1]
delta_times_24_poly = poly_subtract([24*c for c in poly_multiply(B_poly,B_poly)], poly_multiply(A_poly,C_numerator_poly))
shifted_coefficients = [sum(c*comb(i,j)*104**(i-j) for i,c in enumerate(delta_times_24_poly) if i >= j)
                        for j in range(len(delta_times_24_poly))]
identity_samples = sorted(set(list(range(2,121)) + [1000,1000000,10**20]))
for m in identity_samples:
    v = claimed_values(m)
    expected = 24*(v['B']**2-v['A']*v['C'])
    require(poly_evaluate(delta_times_24_poly,m) == expected, 'polynomial_consistency', m)
    require(poly_evaluate(shifted_coefficients,m-104) == expected, 'polynomial_translation_consistency', m)
require(all(c < 0 for c in shifted_coefficients), 'conditional_universal_sign_via_shifted_coefficients', shifted_coefficients)

# A separate exact arithmetic sweep aims at a wrong threshold or exceptional
# integer case in the claimed expressions. It does not replace direct counting.
t0 = time.perf_counter()
expression_sweep_failures = []
expression_integrality_failures = []
for m in range(2,100001):
    numerator = m**4+114*m**3-277*m**2+426*m-312
    c,remainder = divmod(numerator,24)
    if remainder:
        expression_integrality_failures.append(m)
    d = (m*(3*m+1))**2-(m+1)*c
    if m >= 104 and d >= 0:
        expression_sweep_failures.append({'m':m,'difference':d})
require(not expression_integrality_failures,'expression_C_integrality_m2_to_m100000',expression_integrality_failures)
require(not expression_sweep_failures,'expression_strict_inequality_m104_to_m100000',expression_sweep_failures)
sweep_seconds = time.perf_counter()-t0

report = {
    'reviewer':'REV-B-RQ4-b',
    'stage':1,
    'mathematical_source':'STATEMENTS.md only',
    'source_sha256':'5c70c3bcc8e2a626343221e2b6f5bb076b4eaae29dde58285fa632ae54fb1fae',
    'producer_material_accessed':False,
    'excluded_topics_detected':False,
    'arithmetic':'Python arbitrary precision integers and Fraction; no floating point used for mathematical comparisons',
    'bounds':{'exhaustive_compositions_n_min':0,'exhaustive_compositions_n_max':BRUTE_MAX_N,'direct_formula_m_min':2,'direct_formula_m_max':MAX_M,'dp_n_max':MAX_N,'dp_k_max':MAX_K,'direct_inequality_m_min':104,'direct_inequality_m_max':MAX_M,'expression_sweep_m_min':2,'expression_sweep_m_max':100000},
    'counts':{'brute_compositions_examined_including_empty':brute_compositions_examined,'brute_valid_compositions':brute_valid_compositions,'dp_recurrence_cells_visited':recurrence_cells_visited,'individual_formula_values_checked':3*(MAX_M-1),'direct_inequality_values_checked':MAX_M-104+1,'symbolic_identity_samples':len(identity_samples)},
    'explicit_n314':actual[104],
    'explicit_n314_difference':actual[104]['B']**2-actual[104]['A']*actual[104]['C'],
    'difference_m103':next(r['B_squared_minus_AC'] for r in checked_family if r['m']==103),
    'first_negative_in_tested_family_m':next((r['m'] for r in checked_family if r['B_squared_minus_AC']<0),None),
    'symbolic_audit':{'twenty_four_times_difference_coefficients_low_to_high':delta_times_24_poly,'shift_m_equals_104_plus_x_coefficients_low_to_high':shifted_coefficients,'all_shifted_coefficients_strictly_negative':all(c<0 for c in shifted_coefficients),'interpretation':'The supplied formulas imply the claimed strict inequality for every real m >= 104. This is conditional on those formulas correctly representing the counts.'},
    'finite_small_rows':{str(n):brute_rows[n] for n in range(0,BRUTE_MAX_N+1)},
    'finite_family_counts':checked_family,
    'timings_seconds':{'direct_counting':count_seconds,'exhaustive_enumeration':brute_seconds,'expression_sweep':sweep_seconds,'total':time.perf_counter()-START},
    'failures':failures,
    'scope_limitations':['Direct count verification is finite, m=2..120; universal validity of A, B and C is not established at stage 1.','No producer proof, code, archive or logs were accessed.','No claim of global least size is assessed or made.','Unimodality is not assessed or settled.','The algebraic sign audit is conditional on the supplied count formulas.'],
    'outcome':'NO_COUNTEREXAMPLE_FOUND' if not failures else 'CHECK_FAILURE'
}
print(json.dumps(report,indent=2,sort_keys=True),flush=True)
raise SystemExit(bool(failures))
