"""Retain the dependency cone and actually used RUP hints of the empty clause.

The original DIMACS input is unchanged, so the Lean formula identity stays
unchanged. The resulting LRAT proof must be checked again independently.
"""
from pathlib import Path
import sys

cnf, proof, output = map(Path, sys.argv[1:])
db = {}
for line in cnf.read_text().splitlines():
    if line and line[0] not in 'cp':
        db[len(db) + 1] = tuple(map(int, line.split()[:-1]))
initial = len(db)
steps = {}
for line in proof.read_text().splitlines():
    z = line.split()
    if not z or z[0] == 'c' or z[1] == 'd':
        continue
    z = list(map(int, z))
    i = z[0]
    sep = z.index(0, 1)
    clause, hints = z[1:sep], z[sep + 1:-1]
    assert all(h > 0 for h in hints)
    assignments = {abs(x): x < 0 for x in clause}
    used = []
    conflict = False
    for h in hints:
        used.append(h)
        free = []
        satisfied = False
        for x in db[h]:
            v = assignments.get(abs(x))
            if v is None:
                free.append(x)
            elif v == (x > 0):
                satisfied = True
                break
        if satisfied:
            used.pop()
            continue
        if not free:
            conflict = True
            break
        assert len(free) == 1
        x = free[0]
        assignments[abs(x)] = x > 0
    assert conflict
    steps[i] = (clause, used)
    db[i] = tuple(clause)
    if not clause:
        last = i
needed = set()
todo = [last]
while todo:
    i = todo.pop()
    if i <= initial or i in needed:
        continue
    needed.add(i)
    todo.extend(steps[i][1])
output.write_bytes(('\n'.join(
    ' '.join(map(str, [i, *steps[i][0], 0, *steps[i][1], 0]))
    for i in sorted(needed)) + '\n').encode())
print(len(steps), 'additions ->', len(needed), 'additions;', output.stat().st_size, 'bytes')
