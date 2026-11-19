// Keep the dependency cone of an LRAT refutation without loading the trace.
// Usage: prune_large_lrat INPUT_CLAUSE_COUNT INPUT.lrat OUTPUT.lrat
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){try{
 if(argc!=4)throw runtime_error("expected clause count, input, output");
 uint64_t initial=stoull(argv[1]),last=0,additions=0;ifstream input(argv[2],ios::binary);if(!input)throw runtime_error("input missing");
 vector<uint64_t>offset(1);string line;
 while(input){auto pos=input.tellg();if(!getline(input,line))break;istringstream s(line);uint64_t id;string second;if(!(s>>id>>second)||second=="d")continue;if(id>=offset.size())offset.resize(id+1);offset[id]=(uint64_t)pos+1;additions++;if(second=="0")last=id;}
 if(!last)throw runtime_error("no empty clause; input may still be running");
 vector<bool>needed(offset.size());priority_queue<uint64_t>todo;todo.push(last);needed[last]=true;uint64_t count=0;
 while(!todo.empty()){
  auto id=todo.top();todo.pop();if(!offset.at(id))throw runtime_error("missing proof dependency");input.clear();input.seekg(offset[id]-1);getline(input,line);istringstream s(line);uint64_t n;s>>n;int64_t x;while(s>>x&&x){}while(s>>x&&x){if(x<0)throw runtime_error("RAT hint unsupported");auto dep=(uint64_t)x;if(dep>=id)throw runtime_error("forward reference");if(dep>initial&&!needed.at(dep)){needed[dep]=true;todo.push(dep);}}count++;
 }
 input.clear();input.seekg(0);ofstream output(argv[3],ios::binary);if(!output)throw runtime_error("cannot open output");
 while(getline(input,line)){istringstream s(line);uint64_t id;string second;if(!(s>>id>>second)||second=="d")continue;if(needed.at(id))output<<line<<'\n';}
 cout<<additions<<" additions -> "<<count<<" dependency-cone additions"<<endl;
}catch(const exception&e){cerr<<e.what()<<endl;return 1;}}
