"""Emit kernel-checked orbit coverage from the independently checked CNF traces."""
from pathlib import Path
from itertools import product
import json
root=Path('lean/TranslationTiling/Compiler');cert=root/'Certificates/FiveTiles';folder=Path('build/after800/cover');entries=json.loads(Path('build/after800/orbits.json').read_text());summary=json.loads((folder/'summary.json').read_text())
for z in summary:
 row=z['row'];items=[]
 for a,b,c,d in product(range(5),repeat=4):items.append(f'.rectangular {a} {b} {c} {d}')
 for b in range(5):items.append(f'.rowbit {b}')
 for e in entries:
  if e['mask']&31==row:items.append(f".exclude ⟨{e['mask']},{e['case']},{e['permutation']}⟩")
 selected=[items[i] for i in z['inputIndices']]
 s='import TranslationTiling.Compiler.FiveTileCoverCertificate\n\nnamespace TranslationTiling.Compiler.FiveTile.CoverCases\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
 s+=f'\ndef coverInputs{row} : List CoverInput :=\n  ['+',\n   '.join(selected)+']\n'
 s+=f'\ntheorem coverInputs{row}_valid : (coverInputs{row}.all CoverInput.valid)=true := by decide +kernel\n'
 s+=f'\ndef coverFormula{row} : Sat.Fmla := coverInputs{row}.map (CoverInput.clause {row})\n'
 s+=f'\nfive_cover_certificate {row}\n  (include_str "Certificates/FiveTiles/cover{row}.cnf")\n  (include_str "Certificates/FiveTiles/cover{row}.lrat")\n'
 s+=f'\ndef checkedCover{row} : CheckedCover := ⟨{row},fun cs hcs => plane_of_cover_inputs cs hcs {row} coverInputs{row} coverInputs{row}_valid cover{row}_unsat⟩\n\nend TranslationTiling.Compiler.FiveTile.CoverCases\n'
 (root/f'FiveTileCoverCase{row}.lean').write_bytes(s.encode())
 (cert/f'cover{row}.cnf').write_bytes((folder/f'{row}.selected.cnf').read_bytes());(cert/f'cover{row}.lrat').write_bytes((folder/f'{row}.selected.lrat').read_bytes())
s=(root/'FiveTileCertificate.lean').read_text().replace('import TranslationTiling.Compiler.FiveTileInputs','import TranslationTiling.Compiler.FiveTileCoverInputs').replace('"five_tile_certificate "','"five_cover_certificate "').replace('s!"case{p}"','s!"cover{p}"').replace('s!"formula{p}"','s!"coverFormula{p}"').replace('s!"case{p}_unsat"','s!"cover{p}_unsat"')
(root/'FiveTileCoverCertificate.lean').write_bytes(s.encode())
print('Emitted32 cover modules')
