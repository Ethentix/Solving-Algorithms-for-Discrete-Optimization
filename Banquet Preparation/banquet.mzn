enum COOK;
enum DISH;
int: no_tasks;
set of int: TASK = 1..no_tasks;
array[DISH] of set of TASK: steps;
array[TASK, COOK] of int: time;

int: maxt = sum(array1d(time));
set of int: TIME = 0..maxt;
array[TASK] of var TIME: s;
array[TASK] of var TIME: e;
array[TASK] of var COOK: c;

constraint forall(t in TASK, p in COOK)(time[t,COOK[p]] = 0 -> c[t] != COOK[p]);

constraint forall(t in TASK)(e[t] = s[t] + time[t,c[t]]);

constraint forall(d in DISH,t1,t2 in TASK where t1 < t2)(t1 in steps[d] /\ t2 in steps[d] -> e[t1] <= s[t2]);

predicate nonoverlap(var int:s1, var int:d1,var int:s2, var int:d2) = s1 + d1 <= s2 \/ s2 + d2 <= s1;
constraint forall(t1, t2 in TASK where t1 < t2)(c[t1] = c[t2] -> nonoverlap(s[t1],time[t1,c[t1]],s[t2],time[t2,c[t2]]));

var TIME: obj;
constraint forall(t in TASK)(obj = max(e));

solve :: int_search(c, first_fail, indomain_random, complete)
      minimize obj;
      
output
  ["s = \(s);\n" ] ++
  ["c = \(c);\n"] ++
  ["obj = \(obj);\n"];
