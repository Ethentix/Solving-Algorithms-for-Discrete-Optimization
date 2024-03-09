int: n;
int: cols;
int: delta;
set of int: SOLDIER = 1..n;
set of int: SOLDIER0 = 0..n;
set of int: POS = 1..n;
array[SOLDIER] of int: height;
array[POS] of var SOLDIER: soldier;
array[SOLDIER] of var POS: pos;
include "inverse.mzn";
constraint inverse(pos,soldier);
int: rows = if (n-1) mod cols = 0 then (n-1) div cols else (n-1) div cols + 1 endif;
set of int: ROW = 1..rows;
set of int: COL = 1..cols;
array[ROW,COL] of var SOLDIER0: x;
constraint x[1,1] = 2;
constraint forall(i in 2..rows)(x[i,1] = x[i-1,1] + cols);
constraint forall(r in 1..rows,c in 2..cols)(if x[r,c-1] < n /\ x[r,c-1] > 0 
                  then x[r,c] = x[r,c-1] + 1 else x[r,c] = 0 endif);
constraint pos[1] = 1;
constraint forall(c in 1..cols,r1,r2 in 1..rows where r1 < r2)
                 (x[r2,c] > 0 -> pos[x[r1,c]] < pos[x[r2,c]]);
array[1..n-1] of var int: dif;
constraint forall(s in 1..n-1)(dif[s] = abs(height[soldier[s]] - height[soldier[s+1]]));
array[1..n-1] of var int: spot;
constraint forall(s in 1..n-1)(if dif[s] > delta then spot[s] = s else spot[s] = n endif);
var int: obj = min(spot);
solve :: int_search(soldier, first_fail, indomain_max, complete)
      maximize obj;
output ["obj=\(obj);\n"] ++
       ["pos=\(pos);\n"];
