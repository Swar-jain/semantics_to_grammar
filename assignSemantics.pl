:- table term/3, expr/3.
% Program block DCG
program(X) --> block(X),[.].
block(t_k(X,Y)) --> [begin], dl(X), [;], cl(Y), [end].

% Program block evaluator
program_eval(P, X, Y, Val):-
    update(x, X, [], Env1), update(y, Y, Env1, Env2), 
    eval_k(P, Env2, Env), 
    lookup(z, Env, Val).

eval_k(t_k(X,Y), Env, Val):-
    eval_dl(X, Env,Val1), 
    eval_cl(Y, Val1, Val).

%DCG for declarations and declaration list
dl(t_decl_List(X,Y)) --> decl(X),[;], dl(Y).
dl(t_decl_List(X))--> decl(X).
decl(t_d_const(X,Y)) --> [const], id(X), [=], num(Y).
decl(t_d_var(X)) --> [var], id(X).

%Evaluators for declarations and declaration list
eval_dl(t_decl_List(X,Y), Env, Res):- 
    eval_decl(X, Env, Env1),eval_dl(Y, Env1, Res). 
eval_dl(t_decl_List(X), Env, Env1):- 
    eval_decl(X, Env, Env1).
eval_decl(t_d_const(X,Y), Env, EnvOut) :- 
    \+search(X,Env), update(X,Y,Env,EnvOut).
eval_decl(t_d_var(X), Env, EnvOut) :- 
    \+search(X,Env), update(X,0,Env,EnvOut).
eval_decl(t_d_var(X),Env, Env) :- 
    search(X,Env).
eval_decl(t_d_const(X),Env, Env) :- 
    search(X,Env).

%DCG for condition list consisting of many conditions
cl(t_cl(X,Y))--> command(X),[;], cl(Y).
cl(t_cl(X))--> command(X).
command(t_c_assign(X,Y))-->id(X),[':='],expr(Y).
command(t_c_if(X,Y,Z))-->['if'], boolean(X),['then'],cl(Y),['else'],cl(Z),['endif']. 
command(t_c_while(X,Y))-->['while'],boolean(X),['do'],cl(Y),['endwhile']. 
command(X)--> block(X).

%Evaluator for condition list consisting many conditions
eval_cl(t_cl(X,Y), Env, EnvOut):-
    eval_command(X, Env, Env1) ,eval_cl(Y, Env1, EnvOut). 
eval_cl(t_cl(X), Env, Env1):- eval_command(X, Env, Env1).
eval_command(t_c_if(X,Y,_), Env, EnvOut) :- 
    eval_boolean(X,Env,true), 
    eval_cl(Y,Env,EnvOut).
eval_command(t_c_if(X,_,Z), Env, EnvOut) :- 
    eval_boolean(X,Env,false), 
    eval_cl(Z,Env,EnvOut).
eval_command(t_c_while(X,Y), Env, EnvOut):- 
    eval_boolean(X,Env,Val), 
    Val = true,eval_cl(Y,Env,Env1),
    eval_command(t_c_while(X,Y), Env1, EnvOut).
eval_command(t_c_while(X,_), Env, Env):-
    eval_boolean(X, Env, Val), Val = false.
eval_command(t_c_assign(X,Y), Env,Env2) :- 
    eval_expr(Y,Env,Env1,Val), search(X,Env1),update(X,Val,Env1,Env2).
eval_command(t_k(X,Y), Env, Val) :- 
    eval_k(t_k(X,Y), Env,Val).

%DCG for boolean expressions
boolean(t_b(true))-->['true'].
boolean(t_b(false))-->['false'].
boolean(t_b(X,Y))-->expr(X),['='],expr(Y).
boolean(t_not(Y))-->['not'],boolean(Y).

%Evaluator for boolean expressions
eval_boolean(t_b(true), _, true).
eval_boolean(t_b(false), _, false).
eval_boolean(t_not(B), Env, Val):-
    eval_boolean(B, Env, Val1),  not(Val1, Val).
eval_boolean(t_b(E1, E2), Env, true):-
    eval_expr(E1, Env, Env1, Val), eval_expr(E2, Env1,_, Val).
eval_boolean(t_b(E1, E2), Env, false):-
    eval_expr(E1, Env, Env1, Val1), eval_expr(E2, Env1,_, Val2),
    Val1 \= Val2.
not(true, false).
not(false, true).

%DCG for expressions
expr(t_assign(X,Y))--> id(X),[':='],expr(Y).
expr(t_add(X,Y))-->expr(X), ['+'], term(Y).
expr(t_sub(X,Y))-->expr(X),['-'],term(Y).
expr(X)-->term(X).

term(t_mul(X,Y))-->term(X),['*'],num(Y).
term(t_div(X,Y))-->term(X),['/'],num(Y).
term(X)--> num(X).

%The following lines are for braces, number and variables. 
num(X) --> ['('], expr(X), [')'].
num(X) --> [X], {number(X)}.
num(I)-->[I], {atom(I)}.
id(I)-->[I], {atom(I)}.

%Evaluator for expressions
%assignment
eval_expr(t_assign(X,Y), Env, EnvOut, Val):- 
    eval_expr(Y,Env,Env1, Val), search(X, Env1), 
    update(X,Val,Env1,EnvOut).
%Addition and subtraction
eval_expr(t_add(X,Y), Env, Env2, Val):- 
    eval_expr(X, Env,EnvOut,Val1),
    eval_expr(Y, EnvOut,Env2, Val2),
    Val is Val1 + Val2. 
eval_expr(t_sub(X,Y), Env, EnvOut, Val):- 
    eval_expr(X, Env,Env1, Val1), 
    eval_expr(Y, Env1, EnvOut, Val2),
    Val is Val1 - Val2. 
%Evaluator for division and multiplication
eval_expr(t_mul(X,Y), Env,EnvOut, Val):-
    eval_expr(X, Env, Env1, Val1), 
    eval_expr(Y, Env1,EnvOut, Val2),
    Val is Val1 * Val2. 
eval_expr(t_div(X,Y), Env,EnvOut, Val):-
    eval_expr(X, Env,Env1, Val1), 
    eval_expr(Y, Env1,EnvOut, Val2),
    Val is Val1 / Val2. 

%Evaluator for number and variables
eval_expr(X,Env,Env,X) :- number(X).
eval_expr(I,Env,Env, Val):- 
    lookup(I, Env, Val). 

lookup(Id, [(Id, Val)|_], Val).
lookup(Id, [_|T], Val) :- lookup(Id, T, Val).

update(Id, Val, [], [(Id, Val)]).
update(Id, Val, [(Id,_)|T],[(Id, Val)|T]).
update(Id, Val, [H|T], [H|R]):- H\= (Id,_), update(Id, Val, T, R).

search(Id, [(Id,_)|_]).
search(Id, [H|T]):- H\=(Id,_), search(Id, T).
