"""Independently check positive-hint RUP/LRAT proofs for the patch CNFs."""
from pathlib import Path
import sys,time
cnf,proof=map(Path,sys.argv[1:3]);db={};cl=[];n=0
for line in cnf.read_text().splitlines():
 if not line or line[0] in 'cp':continue
 for s in line.split():
  x=int(s)
  if x:cl.append(x)
  else:n+=1;db[n]=tuple(cl);cl=[]
assert not cl
adds=deletes=0;t=time.time();empty=False
for line in proof.read_text().splitlines():
 if not line.strip() or line.startswith('c'):continue
 z=line.split();i=int(z[0])
 if z[1]=='d':
  for s in z[2:-1]:db.pop(int(s),None)
  deletes+=1;continue
 z=list(map(int,z));sep=z.index(0,1);c=z[1:sep];h=z[sep+1:-1]
 assert all(x>0 for x in h),('RAT hint needs a different checker',i)
 assignments={};conflict=False
 for x in c:
  if assignments.get(abs(x))==(x>0):conflict=True;break
  assignments[abs(x)]=x<0
 if not conflict:
  for j in h:
   d=db[j];free=[];sat=False
   for x in d:
    v=assignments.get(abs(x))
    if v is None:free.append(x)
    elif v==(x>0):sat=True;break
   if sat:continue
   if not free:conflict=True;break
   assert len(free)==1,('hint is not unit',i,j,len(free))
   x=free[0];assignments[abs(x)]=x>0
 assert conflict,('RUP failed',i)
 db[i]=tuple(c);adds+=1
 if not c:empty=True
assert empty
print('Independent RUP/LRAT check passed:',adds,'additions,',deletes,'deletions;',round(time.time()-t,2),'seconds')
