"""Regenerate the kernel-checked short-board Wang compiler prime tables.

Requires NumPy and SciPy. Run from the repository root. The assignment search
is not trusted: Lean checks primality, separation, positive representations,
support, order, mass, and volume for every emitted table.
"""
import math,json
from pathlib import Path
import numpy as np
from scipy.optimize import linear_sum_assignment

def primes(n):
 s=bytearray(b'\1')*(n+1);s[:2]=b'\0\0'
 for a in range(2,math.isqrt(n)+1):
  if s[a]:s[a*a::a]=b'\0'*(((n-a*a)//a)+1)
 return [a for a in range(2,n+1) if s[a]]
ps=primes(65536);K=2**24*549072*8003**4
out=[]
def profile(bs):
 w=len(bs);us=[p for p in ps if p not in [2,3,5,7]][:2*w]
 best=None
 for mode in ['reverse','parallel','adjacent']:
  pairs=list(zip(us[:w],us[w:][::-1] if mode=='reverse' else us[w:])) if mode!='adjacent' else list(zip(us[::2],us[1::2]))
  forbidden=set(us+[2,3,5,7,30631,30637,30649,30643]);qs=np.array([p for p in ps if p not in forbidden],dtype=np.int64)
  rows=[];coeffs=[]
  for (a,b),B in zip(pairs,bs):
   u=qs*pow(a,-1,b)%b;u=np.where(u==0,b,u);v=(qs-u*a)//b
   costs=np.where(v>0,np.log(qs),1e9)
   rows.extend([costs]*B);coeffs.append((u,v))
  rr,cc=linear_sum_assignment(np.array(rows));assert all(rows[r][c]<1e8 for r,c in zip(rr,cc))
  digits=[];coeff=[];idx=0
  for B,(u,v) in zip(bs,coeffs):
   take=cc[idx:idx+B];idx+=B;digits.append([int(qs[c]) for c in take]);coeff.append([[int(u[c]),int(v[c])] for c in take])
  pairs+= [(2,30631),(3,30637)];digits +=[[30649],[30643]];coeff +=[[[9,1]],[[2,1]]]
  tags=sum([list(p) for p in pairs],[])+sum(digits,[])
  assert len(tags)==len(set(tags)) and not set(tags)&{5,7}
  for (a,b),ds,uv in zip(pairs,digits,coeff):
   for q,(u,v) in zip(ds,uv):assert u>0 and v>0 and q==u*a+v*b
  r=[math.prod(ds) for ds in digits];V=175**2*math.prod(x*x*a*b for x,(a,b) in zip(r,pairs));J=175**2*math.prod(x*a*b for x,(a,b) in zip(r,pairs))
  H=max([175]+[32*x*(a*b)**2 for x,(a,b) in zip(r[:w],pairs[:w])]+[2*o*x*(a*b)**2*175**3 for o,x,(a,b) in zip([3,2],r[w:],pairs[w:])])
  W=math.prod(bs);X=max(3*W,max(w+2,256)**2);lam=(2*X).bit_length();L=132*X*X*lam
  assert max(w+2,256)**4<=X*X and H*H<=L*V
  e=(K*H*H*V*J*L*L).bit_length()
  z=dict(radices=bs,mode=mode,pairs=pairs,digits=digits,coefficients=coeff,H=str(H),V=str(V),J=str(J),L=str(L),W=str(W),exponent=e)
  if best is None or e<best['exponent']:best=z
 return best

zs=[]
for n in [4,5,6,10,20]:
 z=profile([4]*10+[6]*11+[n]*3)
 z['n']=n
 zs.append(z)
for z in zs:
 n=z['n']
 if n not in [4,5,6,10,20]:continue
 ar=z['radices']+[1,1];pairs=z['pairs'];digits=z['digits'];coef=z['coefficients']
 used={p for pair in pairs for p in pair}|set(sum(digits,[]));fill=[x for x in range(2,65537) if x not in used and x not in [5,7] and all(x%a for a in range(2,math.isqrt(x)+1))];f=iter(fill)
 ps=[a for a,b in pairs]+[b for a,b in pairs];ca=[];cb=[]
 for c in range(26):
  ps+=digits[c]+[next(f) for _ in range(20-ar[c])]
  ca +=[a for a,b in coef[c]]+[1]*(20-ar[c]);cb +=[b for a,b in coef[c]]+[1]*(20-ar[c])
 assert len(ps)==572 and len(ps)==len(set(ps))
 e={4:4700,5:4800,6:4900,10:5360,20:6600}[n]
 txt=f'''import TranslationTiling.FiniteCompiler.ShortParameters
import Mathlib.Tactic.NormNum.Prime

namespace TranslationTiling.FiniteCompiler.ShortParameters
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option exponentiation.threshold 20000

def profile{n} : Profile :=
  ⟨{n}, {ps}, {ca}, {cb}⟩

theorem profile{n}_valid : Valid profile{n} := by
  refine ⟨by decide +kernel,by decide +kernel,?_,by decide +kernel,by decide +kernel,by decide +kernel⟩
  simp (config := {{maxSteps := 1000000}}) only [profile{n},List.forall_mem_cons,List.forall_mem_nil]
  exact ⟨'''+', '.join(['by norm_num']*len(ps))+f''', by simp⟩

def horizontal{n} : ℕ := {z['H']}
def exponent{n} : ℕ := {e}

theorem support{n} : SupportValid profile{n} horizontal{n} := by decide +kernel

theorem wordCount{n} : 10000≤profile{n}.wordCount ∧ 256^2≤3*profile{n}.wordCount ∧
    Nat.log 2 (6*profile{n}.wordCount)+1≤192 := by decide +kernel

theorem volume{n} : horizontal{n}^2≤(2^15*(3*profile{n}.wordCount)^2)*profile{n}.order ∧
    (2^24*549072*8003^4)*horizontal{n}^2*profile{n}.order*profile{n}.mass*
      (2^15*(3*profile{n}.wordCount)^2)^2≤2^exponent{n} := by decide +kernel

end TranslationTiling.FiniteCompiler.ShortParameters
'''
 Path(f'lean/TranslationTiling/FiniteCompiler/ShortProfile{n}.lean').write_bytes(txt.encode())
