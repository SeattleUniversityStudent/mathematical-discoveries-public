#!/bin/bash
# Sequential clean build of the PRT-CAR-001 formalization; logs each module's exit code, seconds and peak RSS (KB).
# Requires the official Lean 4.34.0 binary as `lean` on PATH (see lean-toolchain); no Lake, no Mathlib, no network.
lean --version | grep -q 'version 4.34.0' || { echo "need Lean 4.34.0 on PATH"; exit 2; }
cd "$(dirname "$0")"; rm -rf build; mkdir -p build logs
for m in CarlitzSpec CarlitzCore CarlitzStates CarlitzSteps0 CarlitzSteps1 CarlitzSteps2 CarlitzSteps3 CarlitzSteps4 CarlitzSteps5 CarlitzSteps6 CarlitzSteps7 CarlitzSteps CarlitzMain; do
  s=$(date +%s)
  python3 - "$m" <<'PY'
import resource, subprocess, sys, os
m=sys.argv[1]
r=subprocess.run(["lean","-o",f"build/{m}.olean",f"{m}.lean"],env=dict(os.environ,LEAN_PATH="build"),capture_output=True,text=True)
open(f"logs/{m}.log","w").write(r.stdout+r.stderr)
print(m,"exit",r.returncode,"peakRSS_KB",resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
sys.exit(r.returncode)
PY
  rc=$?; echo "  seconds $(( $(date +%s) - s ))"
  [ $rc -ne 0 ] && { echo "BUILD FAILED at $m"; exit $rc; }
done
echo "BUILD OK"
