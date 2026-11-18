"""Regenerate the small-Wang-tile certificate tables from the repository root.

Requires NumPy. This generator is not trusted by the formal proof: every
periodic witness and row-ranking obstruction is checked by Lean's kernel.
The checked tables cover all 128^2 pairs of rectangular three-letter matrices.
"""

from pathlib import Path
from itertools import product
import numpy as np
Z=512
side=np.full((Z,Z),-1,dtype=np.int8);codes=np.zeros((Z,Z),dtype=np.int64)
for width in [2,3]:
 for flat in product(range(3),repeat=width*width):
  H=V=0
  for y in range(width):
   for x in range(width):
    a=flat[y*width+x];H|=1<<(3*a+flat[y*width+(x+1)%width]);V|=1<<(3*a+flat[((y+1)%width)*width+x])
  if side[H,V]<0:
   side[H,V]=width;codes[H,V]=sum(v*3**i for i,v in enumerate(flat))
idx=np.arange(Z)
for axis in [0,1]:
 for bit in range(9):
  for hi in idx[(idx&(1<<bit))!=0]:
   lo=hi^(1<<bit)
   if axis==0:
    copy=(side[hi,:]<0)&(side[lo,:]>=0);side[hi,copy]=side[lo,copy];codes[hi,copy]=codes[lo,copy]
   else:
    copy=(side[:,hi]<0)&(side[:,lo]>=0);side[copy,hi]=side[copy,lo];codes[copy,hi]=codes[copy,lo]
masks=[]
for H in range(Z):
 rows=[H>>(3*i)&7 for i in range(3)]
 if all(not(a&b) or a==b for a,b in product(rows,repeat=2)):masks.append(H)
assert len(masks)==128
base=Path('lean/TranslationTiling/Compiler')
s='''import TranslationTiling.Compiler.SmallTileCertificate
namespace TranslationTiling.Compiler.SmallTile
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def masks : List ℕ := '''+str(masks)+'''
theorem masks_length : masks.length=128 := by decide +kernel
theorem matrixCode_mem : ∀ r : Matrix, Rectangular r → matrixCode r∈masks := by decide +kernel
end TranslationTiling.Compiler.SmallTile
'''
(base/'SmallTileMasks.lean').write_bytes(s.encode())
headers=[]
for block in range(16):
 s='''import TranslationTiling.Compiler.SmallTileMasks
namespace TranslationTiling.Compiler.SmallTile
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false
set_option exponentiation.threshold 20000
'''
 for H in masks[8*block:8*block+8]:
  rows=[r for r in product(range(3),repeat=4) if all(H&(1<<(3*r[x]+r[x+1])) for x in range(3))]
  rcs=[sum(v*3**i for i,v in enumerate(r)) for r in rows]
  req=[[sum({1<<(3*a[x]+b[x]) for x in range(4)}) for b in rows] for a in rows]
  certs=[]
  for V in masks:
   if side[H,V]>=0:certs.append(f'.periodic {str(side[H,V]==3).lower()} {codes[H,V]}');continue
   edges=[(i,j) for i in range(len(rows)) for j in range(len(rows)) if req[i][j]&~V==0]
   ranks=[0]*len(rows)
   for _ in range(3):
    nxt=ranks.copy()
    for i,j in edges:nxt[j]=max(nxt[j],ranks[i]+1)
    ranks=nxt
   assert all(r<3 for r in ranks)
   assert all(ranks[i]<ranks[j] for i,j in edges)
   rankCode=sum(v*3**a for a,v in zip(rcs,ranks))
   certs.append(f'.obstruction {rankCode}')
  s+=f'\ndef certificates{H} : List Certificate :=\n  ['+', '.join(certs)+']\n'
  s+=f'''theorem certificates{H}_valid : ∀ i : Fin 128,
    Valid {H} (masks.getD i.val 0) (certificates{H}.getD i.val (.obstruction 0))=true := by
  decide +kernel
'''
 s+='\nend TranslationTiling.Compiler.SmallTile\n'
 name=f'SmallTileData{block}';(base/(name+'.lean')).write_bytes(s.encode());headers.append(name)
s='\n'.join('import TranslationTiling.Compiler.'+x for x in headers)+'''
namespace TranslationTiling.Compiler.SmallTile
structure CheckedRow where
  mask : ℕ
  certificates : List Certificate
  valid : ∀ i : Fin 128, Valid mask (masks.getD i.val 0)
    (certificates.getD i.val (.obstruction 0))=true
def checkedRows : List CheckedRow :=
  ['''+',\n   '.join(f'⟨{h},certificates{h},certificates{h}_valid⟩' for h in masks)+''']
theorem checkedRows_masks : checkedRows.map CheckedRow.mask=masks := rfl
theorem exists_certificate {H V : ℕ} (hH : H∈masks) (hV : V∈masks) :
    ∃ c, Valid H V c=true := by
  rw [←checkedRows_masks] at hH
  obtain ⟨r,_,hr⟩ := List.mem_map.mp hH
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hV
  have hi' : i<128 := by simpa only [masks_length] using hi
  refine ⟨r.certificates.getD i (.obstruction 0),?_⟩
  rw [←hr,←he,←List.getD_eq_getElem _ _ hi]
  exact r.valid ⟨i,hi'⟩
end TranslationTiling.Compiler.SmallTile
'''
(base/'SmallTileChecked.lean').write_bytes(s.encode())
print('Generated 128 checked rows in 16 modules.')
