#!/usr/bin/env python3
"""Extract imports and split lean/TranslationTiling/Abstract.lean into one snippet file per declaration
(doc comments and section comments removed; theorem proofs elided) in lean-snippets/, so the paper
typesets exactly the Lean code."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
src = root / "lean/TranslationTiling/Abstract.lean"
out = root / "lean-snippets"
out.mkdir(exist_ok=True)

text = src.read_text()
imports = re.match(r"(?:import [^\n]+\n)+", text)
if imports is None:
    sys.exit("cannot find the opening import block")
(out / "Imports.lean").write_text(imports.group())
body = text.split("namespace TranslationTiling.Abstract", 1)[1]
body = body.rsplit("end TranslationTiling.Abstract", 1)[0]
body = re.sub(r"/-!.*?-/", "", body, flags=re.S)   # section comments
body = re.sub(r"/--.*?-/\s*", "", body, flags=re.S)  # doc comments
names = ["Imports"]
for block in re.split(r"\n\s*\n", body):
    block = block.strip("\n")
    if not block.strip():
        continue
    m = re.match(r"(?:abbrev|def|theorem|lemma)\s+(\S+)", block)
    if not m:
        sys.exit(f"cannot name block:\n{block}")
    if block.startswith("theorem"):  # show the statement only, not the proof
        stmt = block.split(":=", 1)[0].rstrip()
        head, rest = stmt.split(" : ", 1)  # break after the name to avoid overflow
        block = f"{head} :\n  {rest} := ..."
    (out / f"{m.group(1)}.lean").write_text(block + "\n")
    names.append(m.group(1))
print(" ".join(names))
