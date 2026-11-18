"""Regenerate the finite small-prime clean-seed CNF and LRAT certificates.

Run from the repository root with Python and CaDiCaL on PATH:
    python verification/small_prime_certificates.py 5
    python verification/small_prime_certificates.py 7

Lean checks both the generated propositional proof and definitional agreement
with SmallPrime.satFormula; this generator and the SAT solver are untrusted.
"""
from pathlib import Path
import argparse
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('prime', type=int, choices=[5, 7])
parser.add_argument('--cadical', default='cadical')
args = parser.parse_args()
p=args.prime;N=2*p+2;E=13+8*N
forms=[(a,b) for a in range(p) for b in range(p) if a or b]
lines=[(d,e) for d in range(9) for e in range(E)]
C=N*13*p;L=9*E*p*p
cell=lambda n,y,v: n*13*p+y*p+v+1
coeff=lambda d,e,a,b: C+d*E*p*p+e*p*p+a*p+b+1
bad=lambda d,e,n: C+L+d*E*N+e*N+n+1
clauses=[]
for n in range(N):
 for y in range(13):clauses.append([cell(n,y,v) for v in range(1,p)])
for n in range(N):
 for y in range(13):
  for u in range(p):
   for v in range(u+1,p):clauses.append([-cell(n,y,u),-cell(n,y,v)])
for d,e in lines:clauses.append([coeff(d,e,a,b) for a,b in forms])
for d,e in lines:
 for n in range(N):
  y=(d-4)*n+e-4*N
  if 0<=y<13:
   for a,b in forms:
    v=(a*n+b)%p
    if v:clauses.append([-coeff(d,e,a,b),cell(n,y,v)])
for d,e in lines:
 for n in range(N):
  y=(d-4)*n+e-4*N
  if 0<=y<13:
   for a,b in forms:
    v=(a*n+b)%p
    if v:clauses.append([-bad(d,e,n),-coeff(d,e,a,b)])
for h in [2,4]:
 pat=[(0,0,0),(0,2,0),(0,2,h),(0,3,h),(h//2,0,0),(h//2,2,h),(h//2,4,2*h),(h,2,0),(h,3,h),(h,4,2*h)]
 for r in range(N-4):
  for q in range(13-2*h):
   clauses.append([bad(d+4,q+j-d*(r+i)+4*N,r+i) for d,i,j in pat])
root=Path(__file__).resolve().parents[1]/'lean/TranslationTiling/SudokuArithmetic/Certificates'
out=root/f'seed{p}.cnf'
out.write_bytes(('p cnf '+str(C+L+9*E*N)+' '+str(len(clauses))+'\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n').encode())
print(p,len(clauses),out,flush=True)

result=subprocess.run([args.cadical, '--plain', '--lrat=true', '--no-binary',
                       str(out), str(root/f'seed{p}.lrat')], check=False)
if result.returncode != 20:
    raise SystemExit(f'expected UNSAT (exit 20), got {result.returncode}')
