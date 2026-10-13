"""Exact least-winning bounds for finite three-heap positions."""
import argparse, hashlib, json, time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--bound', type=int, default=80)
args = parser.parse_args()
B = args.bound
assert 1 <= B < 65534
started = time.monotonic()
INF = 65535
threshold = {}
attempts = 0
for a in range(B + 1):
    for b in range(a, B + 1):
        for c in range(b, B + 1):
            position = (a, b, c)
            value = INF
            for t in range(1, c + 1):
                found = False
                for i, heap in enumerate(position):
                    if heap < t:
                        continue
                    follower = list(position)
                    follower[i] -= t
                    follower = tuple(sorted(follower))
                    attempts += 1
                    if threshold[follower] > 2 * t:
                        value = t
                        found = True
                        break
                if found:
                    break
            threshold[position] = value

def smallest_fibonacci(n):
    if n == 0:
        return INF
    fs = [1, 2]
    while fs[-1] <= n:
        fs.append(sum(fs[-2:]))
    least = None
    for f in reversed(fs):
        if f <= n:
            n -= f
            least = f
    return least

rows = [dict(n=n, threshold=threshold[(n, n, n)], z1=smallest_fibonacci(n))
        for n in range(1, B + 1)]
payload = bytearray()
for value in threshold.values():
    payload.extend(value.to_bytes(2, 'little'))
Path('fibonacci_thresholds.bin').write_bytes(payload)
Path('fibonacci_equal_values.json').write_text(json.dumps(rows, indent=2) + '\n')
receipt = dict(bound=B, states=len(threshold), examined_move_instances=attempts,
               sentinel=INF, ordering='a=0..B, b=a..B, c=b..B; uint16 little-endian',
               seconds=time.monotonic()-started,
               bytes=len(payload), sha256=hashlib.sha256(payload).hexdigest(),
               equal_P_at_r1=[r['n'] for r in rows if r['threshold'] > 1],
               first_threshold_mismatch=next((r for r in rows if r['threshold'] != r['z1']), None),
               first_r1_mismatch=next((r for r in rows if (r['threshold'] > 1) != (r['z1'] > 1)), None))
Path('fibonacci_probe_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
