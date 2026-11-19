"""Regenerate the Lean prime tables for the projected word tests.

Lean checks primality, support, and volume for every generated table.
Run from the repository root.
"""
from pathlib import Path
import json, math
from functools import reduce

p = Path("lean/TranslationTiling/FiniteCompiler")
for z in json.loads(Path('verification/projected_prime_profiles.json').read_text()):
 n=z['n']; ar=z['radices']+[1,1]; pairs=z['pairs']; ds=z['digits'];uv=z['coefficients']
 used={p for pair in pairs for p in pair}|set(sum(ds,[]))
 f=iter(x for x in range(2,65537) if x not in used and x not in (5,7) and all(x%a for a in range(2,math.isqrt(x)+1)))
 ps=[a for a,b in pairs]+[b for a,b in pairs];ca=[];cb=[]
 for i in range(22):
  ps+=ds[i]+[next(f) for _ in range(44-ar[i])]
  ca +=[a for a,b in uv[i]]+[1]*(44-ar[i]);cb +=[b for a,b in uv[i]]+[1]*(44-ar[i])
 assert len(ps)==len(set(ps))==1012
 chunks=[ps[i:i+48] for i in range(0,len(ps),48)]
 names=[f'primes{n}Part{i}' for i in range(len(chunks))]
 s=f'''import TranslationTiling.FiniteCompiler.ProjectedParameters
import TranslationTiling.FiniteCompiler.ProjectedCap
import TranslationTiling.FiniteCompiler.DistinctPrimes
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.NormNum.Prime

namespace TranslationTiling.FiniteCompiler.ProjectedParameters
open PairSmall
set_option maxRecDepth 15000
set_option maxHeartbeats 6000000
set_option Elab.async false
set_option exponentiation.threshold 20000

'''
 for name,chunk in zip(names,chunks):
  s+=f'''private def {name} : List ℕ := {chunk}

private theorem {name}_valid : ∀ v∈{name}, v.Prime ∧ v≠5 ∧ v≠7 ∧ v≤65536 := by
  simp only [{name},List.forall_mem_cons,List.forall_mem_nil]
  exact ⟨'''+', '.join(['by norm_num']*len(chunk))+''', by simp⟩

'''
 s+=f'''def profile{n} : Profile :=
  ⟨{n}, {' ++ '.join(names)}, {ca}, {cb}⟩

private theorem nodup{n} : profile{n}.primes.Nodup := by
  exact (distinctCheck_sound (seen:=0) (ps:=profile{n}.primes) (by decide +kernel)).1

theorem profile{n}_valid : Valid profile{n} := by
  refine ⟨by decide +kernel,nodup{n},?_,by decide +kernel,by decide +kernel,by decide +kernel⟩
  simp only [profile{n},List.forall_mem_append]
  exact '''+reduce(lambda a,b: f'⟨{a},{b}⟩', (name+'_valid' for name in names))+f'''

def horizontal{n} : ℕ := {z["H"]}
def exponent{n} : ℕ := {z["projected_exponent"]}

theorem support{n} : SupportValid profile{n} horizontal{n} := by decide +kernel

theorem volume{n} :
    horizontal{n}^2≤(projectedCap {n})*profile{n}.order ∧
    (2^24*549072*8003^4)*horizontal{n}^2*profile{n}.order*profile{n}.mass*
      (projectedCap {n})^2≤2^exponent{n} := by decide +kernel

end TranslationTiling.FiniteCompiler.ProjectedParameters
'''
 (p/f'ProjectedProfile{n}.lean').write_bytes(s.encode())
