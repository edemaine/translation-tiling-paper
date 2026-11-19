"""Emit Lean certificates from the independently checked 21-channel profiles."""
import json,math
from pathlib import Path
zs=json.loads(Path('verification/nine_prime_profiles.json').read_text())
for z in zs:
 n=z['n']
 if n not in [4,5,6,10,20,30]:continue
 ar=z['radices']+[1,1];pairs=z['pairs'];digits=z['digits'];coef=z['coefficients']
 used={p for pair in pairs for p in pair}|set(sum(digits,[]));fill=[x for x in range(2,65537) if x not in used and x not in [5,7] and all(x%a for a in range(2,math.isqrt(x)+1))];f=iter(fill)
 ps=[a for a,b in pairs]+[b for a,b in pairs];ca=[];cb=[]
 for c in range(23):
  ps+=digits[c]+[next(f) for _ in range(30-ar[c])]
  ca +=[a for a,b in coef[c]]+[1]*(30-ar[c]);cb +=[b for a,b in coef[c]]+[1]*(30-ar[c])
 assert len(ps)==736 and len(ps)==len(set(ps))
 e={4:4010,5:4100,6:4200,10:4580,20:5670,30:6810}[n]
 txt=f'''import TranslationTiling.FiniteCompiler.NineParameters
import Mathlib.Tactic.NormNum.Prime

namespace TranslationTiling.FiniteCompiler.NineParameters
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

end TranslationTiling.FiniteCompiler.NineParameters
'''
 Path(f'lean/TranslationTiling/FiniteCompiler/NineProfile{n}.lean').write_bytes(txt.encode())
