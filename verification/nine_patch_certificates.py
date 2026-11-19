"""Regenerate one nine-column patch CNF deterministically.

Run from the repository root with arguments:
  5 9 7 6 0,1,2,3,4,5,6,7,10
  7 9 7 6 0,1,2,3,4,7,8,9,14
Generate an LRAT proof with CaDiCaL --lrat --no-binary, then prune it
with prune_nine_patch_lrat.py. Lean checks both the generated formula's
identity with NinePatch.formula and every inference in the proof.
"""
from pathlib import Path
import sys
p,N,H=map(int,sys.argv[1:4]);D=int(sys.argv[4]) if len(sys.argv)>4 else (H-1)//2
S=list(map(int,sys.argv[5].split(','))) if len(sys.argv)>5 else list(range(N));assert len(S)==N;forms=[(a,b) for a in range(p) for b in range(p) if a or b]
assert p in (5,7) and N==9 and H==7 and D==6
assert S==[0,1,2,3,4,p,p+1,p+2,2*p]
lines=[]
for d in range(-D,D+1):
 for e in range(-(H-1)*max(S),H+(H-1)*max(S)):
  entries=[(i,d*n+e) for i,n in enumerate(S) if 0<=d*n+e<H]
  if len(entries)>=2:lines.append((d,e,entries))
C=N*H*p
cell=lambda n,y,v:n*H*p+y*p+v+1
coeff=lambda i,j:C+i*len(forms)+j+1
cs=[]
for n in range(N):
 for y in range(H):
  cs.append([cell(n,y,v) for v in range(1,p)])
  for u in range(p):
   for v in range(u+1,p):cs.append([-cell(n,y,u),-cell(n,y,v)])
cs.append([cell(0,0,1)])
for i,(d,e,entries) in enumerate(lines):
 cs.append([coeff(i,j) for j in range(len(forms))])
 for j,(a,b) in enumerate(forms):
  for n,y in entries:
   v=(a*S[n]+b)%p
   if v:cs.append([-coeff(i,j),cell(n,y,v)])
# Exclude every nonzero global affine approximation on this finite board.
for A in range(p):
 for B in range(p):
  for c in range(p):
   if A==B==c==0:continue
   clause=[]
   for n,x in enumerate(S):
    for y in range(H):
     v=(A*x+B*y+c)%p
     if v:clause.append(-cell(n,y,v))
   cs.append(clause)
f=Path(f'lean/TranslationTiling/SudokuArithmetic/Certificates/ninepatch{p}.cnf')
f.write_bytes(('p cnf '+str(C+len(lines)*len(forms))+' '+str(len(cs))+'\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in cs)+'\n').encode())
