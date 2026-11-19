"""Emit untrusted clause data and LRAT traces, all checked by the Lean kernel."""
from pathlib import Path
from itertools import product,combinations
import json
root=Path('lean/TranslationTiling/Compiler');cert=root/'Certificates/FiveTiles';cert.mkdir(parents=True,exist_ok=True)
raw=Path('build/after800/split_all');summary=json.loads((raw/'selected_summary.json').read_text())
profiles=[]
cases=[]
for line in Path('build/after800/mincores.txt').read_text().splitlines():
 a=list(map(int,line.split()));H,V,w,h=a[:4];profiles.append((H,V,w,h,sum(c*5**i for i,c in enumerate(a[4:]))))
for z in summary:
 H=z['H'];w=z['width'];h=z['height'];index=z['index'];items=[]
 for a,b,c,d in product(range(5),repeat=4):items.append(f'.rectangular {a} {b} {c} {d}')
 for y,x in product(range(h),range(w)):
  items.append(f'.choice {x} {y}')
  for a,b in combinations(range(5),2):items.append(f'.distinct {x} {y} {a} {b}')
  for a,b in product(range(5),repeat=2):
   if x+1<w and not(H>>(5*a+b)&1):items.append(f'.horizontal {x} {y} {a} {b}')
   if y+1<h:items.append(f'.vertical {x} {y} {a} {b}')
 for A,B,pw,ph,code in profiles:
  if H&A==A:items.append(f'.exclude {A} {B} ⟨{pw},{ph},{code}⟩')
 assert len(items)==z['clauses']
 selected=[items[i] for i in z['inputIndices']]
 s='import TranslationTiling.Compiler.FiveTileCertificate\n\nnamespace TranslationTiling.Compiler.FiveTile.Cases\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 2000\n'
 s+=f'\ndef inputs{index} : List Input :=\n  ['+',\n   '.join(selected)+']\n'
 s+=f'\ntheorem inputs{index}_valid : (inputs{index}.all (Input.valid {H} {w} {h}))=true := by decide +kernel\n'
 s+=f'\ndef formula{index} : Sat.Fmla := inputs{index}.map (Input.clause {w})\n'
 s+=f'\nfive_tile_certificate {index}\n  (include_str "Certificates/FiveTiles/{index}.cnf")\n  (include_str "Certificates/FiveTiles/{index}.lrat")\n\nend TranslationTiling.Compiler.FiveTile.Cases\n'
 s=s.replace('end TranslationTiling.Compiler.FiveTile.Cases',f'def checked{index} : CheckedCase := ⟨{H}, plane_of_inputs inputs{index} inputs{index}_valid case{index}_unsat (by decide) (by decide)⟩'+chr(10)+chr(10)+'end TranslationTiling.Compiler.FiveTile.Cases')
 cases.append(s.split(chr(10),2)[2])
 prefix=raw/f"{index}_{w}_{h}"
 (cert/f'{index}.cnf').write_bytes(prefix.with_suffix('.selected.cnf').read_bytes())
 (cert/f'{index}.lrat').write_bytes(prefix.with_suffix('.selected.lrat').read_bytes())
# Group cases so Lean imports the certificate checker only once per block.
for block, start in enumerate(range(0, len(cases), 32)):
 block_cases = cases[start:start+32]
 names = ', '.join(f'Cases.checked{i}' for i in range(start,start+len(block_cases)))
 header = 'import TranslationTiling.Compiler.FiveTileCertificate'
 footer = f'''namespace TranslationTiling.Compiler.FiveTile

def caseBlock{block} : List CheckedCase := [{names}]

end TranslationTiling.Compiler.FiveTile
'''
 content = (chr(10)*2).join([header,*block_cases,footer])
 (root/f'FiveTileCaseBlock{block}.lean').write_bytes(content.encode())

# Keep the already-tested named-clause kernel checker, replacing only its interface.
s=Path('lean/TranslationTiling/SudokuArithmetic/NinePatchCertificate.lean').read_text()
s=s.replace('import TranslationTiling.SudokuArithmetic.NinePatchFormula','import TranslationTiling.Compiler.FiveTileInputs').replace('namespace TranslationTiling.Sudoku.NinePatch','namespace TranslationTiling.Compiler.FiveTile')
s=s.replace('"nine_patch_certificate "','"five_tile_certificate "').replace('  unless p=5 || p=7 do throwError "expected prime 5 or 7"\n','')
s=s.replace('s!"patch{p}"','s!"case{p}"').replace('(mkApp (mkConst ``formula) (mkNatLit p))','(mkConst (ns ++ Name.mkSimple s!"formula{p}"))').replace('s!"patch{p}_unsat"','s!"case{p}_unsat"')
s+='\nend TranslationTiling.Compiler.FiveTile\n'
(root/'FiveTileCertificate.lean').write_bytes(s.encode())
print('Emitted',len(summary),'kernel-checked case modules')
