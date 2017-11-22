/** ---------------------------------------------------------

EECS 3401 Assignment 3

Family name: Hasan

Given name: Sadman Sakib

Student number: 212497509



---------------------------------------------------------- */

/* load the three search algorithms */
:- ensure_loaded('astar.pl').
:- ensure_loaded('astarCC.pl').
:- ensure_loaded('idastar.pl').

/* ------------------------------------------------------- */

/* successors( +State, -Neighbors)

   Neighbors is a list of elements (Cost, NewState) where
   NewState is a state reachable from State by one action and
   Cost is the cost for that corresponding action (=1 in our
   case)
*/   
successors(S, NS) :-
  bagof(N, successors1(S, N), NS).

successors1(S, NS) :-
  move_right(S, N), NS = (1, N).

successors1(S, NS) :-
  move_left(S, N), NS = (1, N).

successors1(S, NS) :-
  move_below(S, N), NS = (1, N).

successors1(S, NS) :-
  move_above(S, N), NS = (1, N).

/* ------------------------------------------------------- */


/* equality(+S1, +S2)

   holds if and only S1 and S2 describe the same state
*/      
equality([], []).
equality([H1|T1], [H2|T2]) :-
    H1 = H2,
    equality(T1, T2).

/* ------------------------------------------------------- */

/* hfn_null( +State, -V)
   V is the null heuristic for State (=0 irrelevant of the state)
*/
hfn_null(_State, 0).

/* hfn_misplaced( +State, -V)
   V is the number of misplaced tiles in State   
*/
hfn_misplaced(S, 0) :- goal(S), !.  % base-case: if S is a goal state, then V is 0.
hfn_misplaced(S, V) :-
  flatten(S, T), length(T, V1), numlist(1, V1, L),
  compare_list(T, L, V2), V is V2 - 1.  % recursive-case: if S is not a goal state, flatten the state S into T, find the length of T and create an index list from 1 to the length of T. Using the helper function compare the two list T and L and return V as the value minus 1 (because blank tile needs to be excluded).

/* hfn_manhattan( +State, -V)

   V is the sum over the manhattan distances between the current
   and the designated position of each tile
*/
hfn_manhattan(S, 0) :- goal(S), !.  % base-case: if S is a goal state, then V is 0.
hfn_manhattan(S, V) :-
  flatten(S, T), length(T, N), build_goal(N, G), 
  coordinate_array(G, GC, 1), 
  coordinate_array(S, SC, 1),
  calculate_manhattan(SC, GC, V). % recursive-case: if S is not a goal state, flatten S into T, and build a goal state configuration G. Create a coordinate array of G and coordinate array of S and call the helper function to calculate the manhattan distance calculate_manhattan(SC, GC, V).

/* ------------------------------------------------------- */

/* init( +Name, -State)
   State is the initial state for problem Name
*/
init(a, [[1, 2, 3], [4, 8, 5], [blank, 7, 6]]). % the prolog atom "blank" represents the blank tile
init(b, [[8, 2, 6], [4, 1, 5], [blank, 7, 3]]). % the prolog atom "blank" represents the blank tile
init(c, [[blank, 2, 6], [4, 1, 5], [8, 7, 3]]). % the prolog atom "blank" represents the blank tile
init(d, [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, blank, 15], [13, 12, 11, 14]]). % the prolog atom "blank" represents the blank tile

/* ------------------------------------------------------- */

/* goal( +State )
   holds if and only if State is a goal state
*/
goal(S) :- flatten(S, T), last(blank, T), 
	select(blank, T, U), in_order(U). % definition of a goal state: flatten the state list, check the last element is blank, remove the blank tile and check if the rest of the elements are in increasing order.

/* ------------------------------------------------------- */

/** ---------------------------------------------------------
  calling the search algorithms
  ---------------------------------------------------------- */

go(ProblemName, HFN) :-
	init(ProblemName, Init),
	astar(Init, successors, goal, HFN, Path, equality),
	writeln(Path).

goCC(ProblemName, HFN) :-
	init(ProblemName, Init),
	astarCC(Init, successors, goal, HFN, Path, equality),
	writeln(Path).

goIDA(ProblemName, HFN) :-
	init(ProblemName, Init),
	idastar(Init, successors, goal, HFN, Path, equality),
	writeln(Path).

/* 
  Below are the helper predicates used for th N-Puzzle Game:
    - move_right(S, NS) -- move the blank tile right from state S to get a new state NS
    - move_left(S, NS)  -- move the blank tile left from state S to get a new state NS
    - move_below(S, NS) -- move the blank tile below from state S to get a new state NS
    - move_above(S, NS) -- move the blank tile above from state S to get a new state NS
    - just_left(X, Y, R)  -- if X is just left of Y in list R
    - just_right(X, Y, R) -- if X is just right of Y in list R
    - just_below(X, Y, R) -- if X is just below of Y in list R
    - just_above(X, Y, R) -- if X is just above of Y in list R
    - swap(X, Y, R, L)  -- swap the adjacent element X and Y in list R to return a new list L
    - replace(X, Y, R, L)  -- replace the first occurence of X with Y in list R to return a new list L
    - compare_list(L1, L2, C) -- compare two lists and return the number of different elements
    - calculate_manhattan(SC, GC, V) -- calculate the manhattan distance for a state to a goal state and return the distance V
    - build_goal(N, S) -- build a goal state of N elements and return it as S
    - break_list(N, L, R) -- break a list L into sub lists of N elements and return it as R
    - subtract(L1, L2, L) -- subtract list L2 from L1 and return the difference as L
    - take(N, L, L1) -- take the first N elements from L and return it as L1
    - coordinate_array(L1, L2, C) -- given a state array L1 return L2 as an coordinate configuration of L1 starting at index C
    - build_coordinate_array(L1, L2, Y) -- build a coordinate array from L1 as L2 with Y as the Y-axis
    - build_coordinates(L1, L2, Y, R) -- build coordinates of L1 from a coordinate array L2 with Y-axis and return it as R
    - in_order(L) -- if L is in an asceding order of elements where the relation between two adjancent element X and Y is X < Y - 1
    - last(E, L) -- return true if E is the last element of L
*/

% move_right(S, NS) predicate
% given a state S, NS returns the new state with the blank tile moved right.
move_right([F|R], NS) :-
  (is_list(F), member(blank, F)), !, 
  just_right(X, blank, [F|R]),
  swap(blank, X, F, R1), append([R1], R, NS). % base-case: if F is a list and blank is in F, find the right neighbor of blank, swap the neighbor with blank and return the new state.
move_right([F|R], NS) :-
  move_right(R, R1), append([F], R1, NS). % recursive-case: if F is not a list or blank is not in F, recusively call move_right(R, R1) and return the new state as F appended with R1.

% move_left(S, NS) predicate
% given a state S, NS returns the new state with the blank tile moved left.
move_left([F|R], NS) :-
  (is_list(F), member(blank, F)), !, 
  just_left(X, blank, [F|R]),
  swap(blank, X, F, R1), append([R1], R, NS). % base-case: if F is a list and blank is in F, find the left neighbor of blank, swap the neighbor with blank and return the new state.
move_left([F|R], NS) :-
  move_left(R, R1), append([F], R1, NS).  % recursive-case: if F is not a list or blank is not in F, recusively call move_left(R, R1) and return the new state as F appended with R1.

% move_below(S, NS) predicate
% given a state S, NS returns the new state with the blank tile moved below.
move_below([E, F|R], NS) :-
  (is_list(E), member(blank, E)), !, 
  just_below(X, blank, [E, F|R]),
  replace(blank, X, E, R1), 
  replace(X, blank, F, R2),
  append([R1], [R2], R3),
  append(R3, R, NS).  % base-case: if E is a list and blank is in E, find the neighbor directly under blank and replace the neighbor with blank and replace blank with the neighbor and return the new state as lists appended in order.
move_below([E, F|R], NS) :-
  move_below([F|R], R1), append([E], R1, NS). % recursive-case: if E is not a list or blank is not in E, recusively call move_below([F|R], R1) and return the new state as E appended with R1.

% move_above(S, NS) predicate
% given a state S, NS returns the new state with the blank tile moved above.
move_above([E, F|R], NS) :-
  (is_list(F), member(blank, F)), !, 
  just_above(X, blank, [E, F|R]),
  replace(X, blank, E, R1),
  replace(blank, X, F, R2), 
  append([R1], [R2], R3),
  append(R3, R, NS).  % base-case: if F is a list and blank is in F, find the neighbor directly above blank and replace the neighbor with blank and replace blank with the neighbor and return the new state as lists appended in order.
move_above([F|R], NS) :-
  move_above(R, R1), append([F], R1, NS). % recursive-case: if F is not a list or blank is not in F, recusively call move_above(R, R1) and return the new state as F appended with R1.

% just_left(X, Y, R)  predicate
% returns true if X is just left of Y in list R.
just_left(X, Y, [X, Y| _]). % base-case: if X is just left of Y in R.
just_left(X, Y, [F|_]) :-
  (is_list(F), member(Y, F)), !, just_left(X, Y, F).  % recursive-case: if F is a list and Y is in F, recusively call just_left(X, Y, F).
just_left(X, Y, [_|R]) :-
  just_left(X, Y, R). % recursive-case: if F is not a list or Y is not in F, recusively call just_left(X, Y, R).

% just_right(X, Y, R)  predicate
% returns true if X is just right of Y in list R.
just_right(X, Y, [Y, X| _]).  % base-case: if X is just right of Y in R.
just_right(X, Y, [F|_]) :-
  (is_list(F), member(Y, F)), !, just_right(X, Y, F). % recursive-case: if F is a list and Y is in F, recusively call just_right(X, Y, F).
just_right(X, Y, [_|R]) :-
  just_right(X, Y, R).  % recursive-case: if F is not a list or Y is not in F, recusively call just_right(X, Y, R).

% just_below(X, Y, R)  predicate
% returns true if X is just below Y in list R.
just_below(X, Y, [E, F|_]) :-
  (is_list(E), member(Y, E), nth0(I1, E, Y)), !, is_list(F), member(X, F), 
  nth0(I2, F, X), I1 = I2. % base-case: if E is a list and Y is in E with index I1, check if F is a list and X is in F with index I2, return the element.
just_below(X, Y, [_|R]) :-
  just_below(X, Y, R).  % recursive-case: if E is not a list or Y is not in E with index I1, recusively call just_below(X, Y, R).

% just_above(X, Y, R)  predicate
% returns true if X is just above Y in list R.
just_above(X, Y, [E, F|_]) :-
  (is_list(F), member(Y, F), nth0(I1, F, Y)), !, is_list(E), member(X, E), 
  nth0(I2, E, X), I1 = I2. % base-case: if E is a list and Y is in E with index I1, check if F is a list and X is in F with index I2, return the element.
just_above(X, Y, [_|R]) :-
  just_above(X, Y, R).  % recursive-case: if E is not a list or Y is not in E with index I1, recusively call just_below(X, Y, R).

% swap(X, Y, R, L)  predicate
% swap two adjacent elements X and Y in list R to return a new list L.
swap(X, Y, [X, Y | R], [Y, X | R]). % base-case: if X and Y are adjacent, swap and return L as Y, X followed by the rest.
swap(X, Y, [Y, X | R], [X, Y | R]). % base-case: if Y and X are adjacent, swap and return L as X, Y followed by the rest.
swap(X, Y, [F | R], L) :-
  member(X, R), member(Y, R), swap(X, Y, R, R1), append([F], R1, L).  % recursive-case: if X and Y are in R, swap(X, Y, R, R1) and return L as F appended with R1.

% replace(X, Y, R, L)
% replace the first occurence of X with Y in list R to return a new list L.
replace(X, Y, [X | R], [Y | R]).  % base-case: X is the first element, return L with Y as the first element followed by the rest of the list.
replace(X, Y, [F | R], L) :-
  replace(X, Y, R, R1), append([F], R1, L). % recursive-case: if X is not the first element, recusively call replace(X, Y, R, R1) and return L as F appended with R1.

% compare_list(L1, L2, C)
compare_list([], [], 0).  % base-case: if both lists are empty, the number of different elements are 0.
compare_list([X|Y], [A|B], C) :-
  not(X = A), !, compare_list(Y, B, C1), C is C1 + 1. % recursive-case: if X is not equal to A, call compare_list(Y, B, C1) and increment C with C1.
compare_list([_|Y], [_|B], C) :-
  compare_list(Y, B, C).  % recursive-case: if X is equal to A, then just call compare_list(Y, B, C).

% calculate_manhattan(SC, GC, V)
calculate_manhattan([], _, 0).  % base-case: if SC is empty, V is 0
calculate_manhattan([(V1, X1, Y1) | R1], [(V2, X2, Y2) | R2], T) :-
  (not(V1 = blank), nth1(_, [(V2, X2, Y2) | R2], (V1, XN, YN)),
  (not(X1 = XN); not(Y1 = YN))), !, 
  T1 is ((X1 - XN) + (Y1 - YN)), T2 is abs(T1), 
  calculate_manhattan(R1, [(V2, X2, Y2) | R2], T3),
  T is T2 + T3. % recursive-case: if SC is not empty, check if for each tile in SC the X and Y values match. If either does not match, calculate the manhattan distance |X1 - X2| + |Y1-Y2|, then recursively call calculate_manhattan(R1, [(V2, X2, Y2) | R2], T3) and return T as T2 + T3.
calculate_manhattan([(_, _, _) | R1], L2, T) :-
  calculate_manhattan(R1, L2, T). % if both of X and Y values match, that means they are in the correct position according to the goal configuration. Then recursively call calculate_manhattan(R1, L2, T).

% build_goal(N, S)
build_goal(N, S) :- N1 is N - 1, numlist(1, N1, L), append(L, [blank], L1),
  X is round(sqrt(N)), break_list(X, L1, S).  % create a number list from 1 to N - 1 as L, append blank to L to get L1 and then break the list into X parts where X is the square root of N.

% break_list(N, L, R)
break_list(_, [], []) :- !. % base-case: if L is empty, R is empty.
break_list(N, L, R) :-
  take(N, L, L1), subtract(L, L1, L2), break_list(N, L2, L3), append([L1], L3, R). % base-case: take the first N elements of L as L1, subtracttract L from L1 to get L2, recursively call break_list(N, L2, L3) and return R has [L1] appended with L3.

%  subtract(L1, L2, L)
subtract(L, [], L). % base-case: subtracting empty list from List returns List.
subtract(L, [X|Y], R) :- 
  select(X, L, R1), subtract(R1, Y, R). % recursive-case: select X from L remaining with R1 and then recursively call subtract(R1, Y, R).

% take(N, L, L1)
take(N, _, L1) :- 
  N =< 0, !, N =:= 0, L1 = [].  % base-case: if N is less than 0, then L1 is empty.
take(_, [], []).  % base-case: if L is empty, L1 is empty.
take(N, [X|R1], [X|R2]) :- 
  M is N-1, take(M, R1, R2). % recursive-case: decrement N by 1 and recursively call take(M, R1, R2) where M is N - 1.

% coordinate_array(L1, L2, C)
coordinate_array([X], L, C) :- 
  is_list(X), !, build_coordinate_array(X, L, C).  % base-case: if X is the only list, make a coordinate array with X starting at index C and return it as L.
coordinate_array([X|R], L, C) :-
  is_list(X), !, build_coordinate_array(X, L1, C), 
  C1 is C + 1, coordinate_array(R, L2, C1), append(L1, L2, L).  % recursive-case: if X is not the only list, make a coordinate array with X starting at index C, return it as L1 and call coordinate_array(R, L2, C1) and return L as L1 appended with L2.

% build_coordinate_array(L1, L2, Y)
build_coordinate_array([F|R], L2, Y) :-
  length([F|R], V), numlist(1, V, L3), build_coordinates([F|R], L3, Y, L2).  % find the length of L1, create an index array L3 and call build_coordinates([F|R], L3, Y, L2).

% build_coordinates(L1, L2, Y, R)
build_coordinates([A], [X], Y, [(A, X, Y)]).  % base-case: if A is an element on the list, X is the x-coordinate for A and Y is the y-coordinate for A, return a coordinate list (A, X, Y).
build_coordinates([H1|T1], [X|T2], Y, [(H1, X, Y) | R]) :-
  build_coordinates(T1, T2, Y, R).  % recursive-case: for every element E, build a coordinate (E, X, Y) recursively.

% in_order(L)
in_order(L) :- foreach((member(X, L), nth1(I, L, X)), (X is I)). % check for every element X in L with an index I (1 based), X is equal to I.

% last(E, L)
last(X,[X]).  % base-case: X is the last element of a single element list that just has X.
last(X,[_|Z]) :- last(X,Z). % recursive-case: if X is not the last element, call last(X, Z) with the rest of the elements.
