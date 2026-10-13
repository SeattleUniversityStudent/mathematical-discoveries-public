"""Direct mex evaluation with the move bound retained in every state."""
from functools import lru_cache
from pathlib import Path
import hashlib, json, time

B = 20
CAP = 2 * B
started = time.monotonic()
edges = 0

@lru_cache(None)
def grundy(a, b, c, r):
    global edges
    seen = set()
    for i, heap in enumerate((a, b, c)):
        for amount in range(1, min(heap, r) + 1):
            child = [a, b, c]
            child[i] -= amount
            child.sort()
            edges += 1
            seen.add(grundy(*child, 2 * amount))
    answer = 0
    while answer in seen:
        answer += 1
    return answer

source = Path('fibonacci_thresholds.bin').read_bytes()
thresholds = {}
index = 0
for a in range(81):
    for b in range(a, 81):
        for c in range(b, 81):
            if c <= B:
                thresholds[a, b, c] = int.from_bytes(source[index:index+2], 'little')
            index += 2
assert index == len(source)
certificate = bytearray()
compared = 0
for a in range(B + 1):
    for b in range(a, B + 1):
        for c in range(b, B + 1):
            for r in range(1, CAP + 1):
                sg = grundy(a, b, c, r)
                assert (sg == 0) == (r < thresholds[a, b, c]), (a,b,c,r,sg)
                certificate.append(sg)
                compared += 1
Path('fibonacci_literal_certificate.bin').write_bytes(certificate)
witnesses = []
for n in (6, 20):
    r = 1
    root = [n, n, n, r]
    children = []
    for amount in range(1, min(n, r) + 1):
        q = [n-amount, n, n, 2*amount]
        responses = []
        for i, heap in enumerate(q[:3]):
            for t in range(1, min(heap, q[3])+1):
                child = q[:3]
                child[i] -= t
                child.sort()
                if grundy(*child, 2*t) == 0:
                    responses.append(dict(heap_index=i, amount=t, state=child+[2*t]))
        children.append(dict(state=q, grundy=grundy(*q), winning_responses=responses))
    witnesses.append(dict(root=root, grundy=grundy(*root),
                          single_heap_grundy=grundy(0,0,n,r), children=children))
receipt = dict(status='PASS', bound=B, bound_parameter_range=[1,CAP],
               states_compared=compared, cached_states=grundy.cache_info().currsize,
               literal_move_instances=edges, seconds=time.monotonic()-started,
               bytes=len(certificate), sha256=hashlib.sha256(certificate).hexdigest(),
               ordering='a=0..20, b=a..20, c=b..20, r=1..40; unsigned bytes',
               witnesses=witnesses,
               review='Different algorithm, same producer; no separate review.')
Path('fibonacci_literal_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
