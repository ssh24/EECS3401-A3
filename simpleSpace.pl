%% Simple example
%% States are positive integers.
%% we can move from n to n+1 and n+2, both with cost 1
%% equality is arithmetic equality.
%% the goal is reaching 15 
%% The hval is the difference with 10 divided by two.
%%
%% We need to set up the following functions in order to use Astar


% 1. Successor state function, returns list of successors of a state,
%    annotated by cost.  
%
%    Note structure of neighbours list, a list of pair of the form (Cost,State),
%    where Cost is the cost of getting to State from the current state.

successors(X,[(1,Y), (1,Z)]) :- Y is X +1, Z is X+2.  

% 2. Goal test function. 
goal(X) :- X=15.

%% We simply pass astar "goal", and use setGoalState to dynamically
%% alter the current goal.

%3. Heuristic functions.

hfn(X,Val) :- goal(Y), Z is (X-Y)//2, abs(Z,Val).
hfnUniform(_,0).              % causes breadth first search.


abs(X,Y) :- X < 0, !, Y is -X.
abs(X,X).

%%Sample Searches

% ?- astar(0, successors, goal, hfn, Path, =).

%%Note that astarCC requires a state equality function, in this case
%%the built in "=" works.

% ?- astarCC(0, successors, goal, hfn, Path, =).

% ?- idastar(0, successors, goal, hfn, Path, =).
