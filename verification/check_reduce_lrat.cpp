// Independently check a positive-hint LRAT trace and discard unused RUP hints.
// Usage: check_reduce_lrat INPUT.cnf INPUT.lrat OUTPUT.lrat
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
int main(int argc,char**argv){try{
 if(argc!=4)throw runtime_error("expected CNF, input proof, output proof");
 ifstream cnf(argv[1]),proof(argv[2]);ofstream out(argv[3],ios::binary);
 if(!cnf||!proof||!out)throw runtime_error("cannot open a file");
 unordered_map<uint64_t,vector<int>>db;string line;uint64_t initial=0,steps=0;int variables=0;bool empty=false;
 while(getline(cnf,line)){if(line.empty()||line[0]=='c')continue;if(line[0]=='p'){istringstream s(line);string p,fmt;int clauses;s>>p>>fmt>>variables>>clauses;continue;}istringstream s(line);int x;vector<int>cl;while(s>>x&&x)cl.push_back(x);db[++initial]=move(cl);}
 vector<int8_t>assignment(variables+1,-1);
 while(getline(proof,line)){
  if(line.empty()||line[0]=='c')continue;istringstream s(line);uint64_t id;string second;s>>id>>second;
  if(second=="d"){uint64_t x;while(s>>x&&x)db.erase(x);continue;}
  s.clear();s.str(line);s>>id;int lit;vector<int>cl;while(s>>lit&&lit)cl.push_back(lit);
  fill(assignment.begin(),assignment.end(),-1);bool conflict=false;vector<uint64_t>used;
  for(int x:cl){if(abs(x)>variables)throw runtime_error("literal out of range");int8_t v=x<0;if(assignment[abs(x)]!=-1&&assignment[abs(x)]!=v)conflict=true;assignment[abs(x)]=v;}
  int64_t hint;
  while(s>>hint&&hint){
   if(conflict)break;if(hint<0)throw runtime_error("RAT hint unsupported");auto at=db.find(hint);if(at==db.end())throw runtime_error("missing hint "+to_string(hint));
   bool satisfied=false;int free=0,unit=0;
   for(int x:at->second){int8_t v=assignment[abs(x)];if(v==-1){free++;unit=x;}else if(v==(x>0)){satisfied=true;break;}}
   if(satisfied)continue;used.push_back(hint);
   if(free==0){conflict=true;break;}if(free!=1)throw runtime_error("non-unit hint at step "+to_string(id));assignment[abs(unit)]=unit>0;
  }
  if(!conflict)throw runtime_error("no RUP conflict at step "+to_string(id));
  out<<id;for(int x:cl)out<<' '<<x;out<<" 0";for(auto h:used)out<<' '<<h;out<<" 0\n";
  if(cl.empty())empty=true;db[id]=move(cl);steps++;
 }
 if(!empty)throw runtime_error("no empty clause");cout<<"Independent RUP check passed: "<<steps<<" additions; unused hints removed"<<endl;
}catch(const exception&e){cerr<<e.what()<<endl;return 1;}}
