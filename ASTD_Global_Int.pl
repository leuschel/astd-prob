% ASTD with Global State and Delta Updates

% The following predicates are defined in individual ASTD files, which include this interpreter:
% astd_sync_style/1 (b or c; defined before consulting/including this interpreter)
% start/1
% automata_trans/3
% initial_automata_state/2
% final_automata_state/2
% data_type_value/2
% possibly: prob_pragma_string/2 e.g. for LTL properties

% XTL transition definition used by ProB:
trans(Trans,state(S1,G1),state(S2,G2)) :- 
    atrans(S1,G1,Trans,S2,U2), % reorder args for Prolog indexing
    apply_global_updates(G1,U2,G2).

% properties shown in ProB Animator:
prop(state(A,_),A).
prop(state(_,G),'='(Var,Val)) :- member('/'(Var,Val),G).
prop(state(_,G),limit_reached) :- member('/'(nbloans,3),G).
prop(state(_,G),unsafe) :- member('/'(warnings,[_,_|_]),G).
prop(state(A,_),'-->'(Name,S)) :- active_sub_astd(A,aut(Name,FullState)), get_state(FullState,S).
prop(state(A,_),'-->'(Name,'INIT')) :- active_sub_astd(A,aut(Name)).

% extract active sub ASTDs to display in ProB's property pane:
active_sub_astd(S,S).
active_sub_astd('|||'(L),Res) :- member(Sub,L), active_sub_astd(Sub,Res).
active_sub_astd('||'(_,L),Res) :- member(Sub,L), active_sub_astd(Sub,Res).
active_sub_astd('||'(L),Res) :- member(Sub,L), active_sub_astd(Sub,Res).
active_sub_astd(seq([Sub|_]),Res) :- active_sub_astd(Sub,Res).
active_sub_astd(seq([A|T]),Res) :- is_final_astd(A),active_sub_astd(seq(T),Res).
active_sub_astd(aut(_,compound(_,Sub)),Res) :- active_sub_astd(Sub,Res).
active_sub_astd(afork(A,B),R) :- (active_sub_astd(A,R) ; active_sub_astd(B,R)).

get_state(A,A) :- atomic(A).
get_state(compound(S,_),S).

% GENERIC PART:
% --------------

% Automata states are either atomic or compound(Name,InnerState)
% ASTD operators are
% kleene(E) for Kleene Closure of ASTD expression E
% seq(List) for sequential composition of list of ASTD expressions
% '|'(List) for external choice of list of ASTD expressions
% '|||'(List) for interleaving of list of ASTD expressions
% '||'(List) for full synchronised execution of list of ASTD expressions
% '||'(SyncPatterns,List) for synchronised execution of list of ASTD expressions
% List of AST expressions can either be written as:
%  [A1,...,A2]       as explicit list
%  repl(Para,Set,A)  in replicated fashion; Para must be Prolog Variable

atrans(aut(Name),G1,Trans,S2,G2) :- !,
   if(initial_automata_state(Name,S1), atrans(aut(Name,S1),G1,Trans,S2,G2), add_astd_err(no_initial(Name))).
atrans(kleene(S1),G1,Trans,seq([S2,kleene(S1)]),G2) :- !, atrans(S1,G1,Trans,S2,G2).
atrans(seq([A1|T]),G1,Trans,S2,G2) :- !,
    aseq_trans(A1,T,G1,Trans,S2,G2).
atrans('|'(X1),G1,Trans,A2,G2) :- !, choose_process(X1,A1), atrans(A1,G1,Trans,A2,G2).
atrans(afork(A1,B1),G1,Trans,afork(A2,B2),G5) :- !,
    % asymetric fork: process 1 drives process 2, process 2 cannot work on its own
    atrans(A1,G1,Trans,A2,G2),
    thread_sync_state(G1,G2,G3),
    if(atrans(B1,G3,Trans,B2,G4),
       merge_sync_states(fork,G2,G4,G5),
       (B2,G5)=(B1,G2)).
atrans('||'(X1),G1,Trans,'||'(X2),G2) :- !, synchronised_trans(X1,G1,Trans,X2,G2).
atrans('|||'(X1),G1,Trans,'|||'(X2),G2) :- !, interleaved_trans(X1,G1,Trans,X2,G2).
atrans('||'(Sync,X1),G1,Trans,'||'(Sync,X2),G2) :- !,
    async_trans(Sync,X1,G1,Trans,X2,G2).
%atrans('||'(Sync,[A1|T1]),G1,Trans,'||'(Sync,[A2|T2]),G3) :- atrans(A1,G1,Trans,A2,G2),
%    (is_synchronised(Sync,Trans) -> synchronised_trans(T1,G2,Trans,T2,G3) ; T1=T2,G2=G3).
%atrans('||'(Sync,[A1|T1]),G1,Trans,'||'(Sync,[A1|T2]),G2) :-
%    is_not_synchronised(Sync,Trans),interleaved_trans(T1,G1,Trans,T2,G2).
atrans(aut(Aut,S1),G1,Trans,aut(Aut,S2),G2) :- !,
    atrans_aut(Aut,S1,G1,Trans,S2,G2).
atrans(compound(Name,S1),G1,Trans,compound(Name,S2),G2) :- !, atrans(S1,G1,Trans,S2,G2).
atrans(Other,_,_,_,_) :- add_astd_err('Illegal ASTD construct:'(Other)).

aseq_trans(A1,[A2|T],G1,Trans,S2,G2) :- % if A1 is final: allow to skip to rest of sequence
    is_final_astd(A1), %(is_final_astd(A1) -> true ; print(not_final(A1)),nl,fail),
    aseq_trans(A2,T,G1,Trans,S2,G2).
aseq_trans(A1,T,G1,Trans,S2,G2) :-  % allow first process to evolve
    atrans(A1,G1,Trans,A2,G2),
    create_seq(A2,T,S2).

async_trans(Sync,X1,G1,Trans,X2,G2) :- 
   is_synchronised(Sync,Trans),
   synchronised_trans(X1,G1,Trans,X2,G2).
async_trans(Sync,X1,G1,Trans,X2,G2) :- 
   is_not_synchronised(Sync,Trans),
   interleaved_trans(X1,G1,Trans,X2,G2).

atrans_aut(Aut,S1,G1,Trans,S2,G2) :- % is_final_astd(S1) to be checked for final transitions in automata_trans
    automata_trans(Aut,S1,G1,Trans,S2,G2).
atrans_aut(_Aut,S1,G1,Trans,S2,G2) :- compound(S1), % S1 is a nested ASTD: make progress there
    atrans(S1,G1,Trans,S2,G2).

% perform a single interleaved transition of a list of ASTD processes:
interleaved_trans(X1,G1,Trans,X2,G2) :- expand_repl(X1,EX1),
    %print(expanded_repl(EX1)),nl,
    interleaved_trans2(EX1,G1,Trans,X2,G2).
interleaved_trans2([A1|Rest],G1,Trans,[A2|Rest],G2) :- atrans(A1,G1,Trans,A2,G2).
interleaved_trans2([A1|Rest1],G1,Trans,[A1|Rest2],G2) :- interleaved_trans2(Rest1,G1,Trans,Rest2,G2).
% TO DO: optimisation to quickly find relevant process A1 if parameter determines process
% TO DO: for large interleavings: only store state for started processes

create_seq(A1,Tail,Res) :- Tail=[],!,Res=A1.
create_seq(A1,Tail,Res) :- 
   quick_is_final_deadlocked(A1), Tail=[A2|T2], % also does a/the Kleene optimisation on-the-fly
   !,
   create_seq(A2,T2,Res).
create_seq(A1,Tail,seq([A1|Tail])).

% perform synchronised transition of a list of ASTD processes:
synchronised_trans(X1,G1,Trans,X2,G2) :- expand_repl(X1,EX1), EX1 \= [],
   synchronised_trans1(EX1,G1,Trans,X2,G2).
synchronised_trans1([],G1,_,[],G2) :- execute_skip(G1,G2).
synchronised_trans1([A1|T1],G1,Trans,[A2|T2],G5) :-
   atrans(A1,G1,Trans,A2,G2), % <--- G2 is passed to rest; we could also pass G1 to rest and combine the results and check for update collisions here
   thread_sync_state(G1,G2,G3),
   synchronised_trans1(T1,G3,Trans,T2,G4),
   merge_sync_states(A1,G2,G4,G5).

% choosing an ASTD process in a list or replicated construction:
choose_process([H|T],Choice) :- !, member(Choice,[H|T]).
choose_process(repl(Para,Set,Astd),Result) :- !,
   make_non_ground_single_var(Para,repl(Para,Set,Astd),repl(P,S,Result)),
   choose_value(S,P).
choose_process(Other,_) :- add_astd_err(illegal_process_list(Other)).

choose_value([H|T],Choice) :- !,member(Choice,[H|T]).
choose_value(DT,Choice) :- data_type_value(DT,Choice).
%choose_value(int,Choice) :- ...
% TO DO: expand for other sets as needed by ASTD;

% expanding replicated constructions to full lists:
expand_repl([],R) :- !, R=[].
expand_repl([H|T],R) :- !, R=[H|T].
expand_repl(repl(GVar,GL,GObj),Res) :- !,
   make_non_ground_single_var(GVar,repl(GVar,GL,GObj),repl(Var,L,Obj)),
   findall(Obj,choose_value(L,Var),Res).
expand_repl(R,_) :- add_astd_err(cannot_expand_illegal_list(R)).

:- block is_synchronised(?,-).
is_synchronised([H|T],Event) :- member(Template,[H|T]),match_event(Template,Event).
:- block is_not_synchronised(?,-).
is_not_synchronised(L,Event) :- \+ is_synchronised(L,Event). % TO DO: assumes Event fully instantiated for compound templates

% matching events againts synchronisation templates of sync operator
match_event(Name,Event) :- atomic(Name), !, functor(Event,Name,_).
match_event(Template,Event) :- make_non_ground(Template,Event). %\+ \+ Event=Template.

% rules for determining whether an ASTD is final or not:
is_final_astd(seq([])).
is_final_astd(seq([H|T])) :- is_final_astd(H), is_final_astd(seq(T)).
is_final_astd(aut(Aut)) :- initial_automata_state(Aut,S),final_automata_state(Aut,S).
is_final_astd(aut(Aut,S)) :- final_automata_state(Aut,S).
is_final_astd(compound(_,S)) :- is_final_astd(S).
is_final_astd('|'(L)) :- choose_process(L,A1), is_final_astd(A1).
is_final_astd('|||'(L)) :- \+ (choose_process(L,A1), \+ is_final_astd(A1)).
is_final_astd('||'(L)) :- \+ (choose_process(L,A1), \+ is_final_astd(A1)).
is_final_astd('||'(_,L)) :- \+ (choose_process(L,A1), \+ is_final_astd(A1)).
is_final_astd(kleene(_)).
%is_final_astd(kleene(S,_)) :- is_final_astd(S).
is_final_or_atomic(S) :- is_final_astd(S).
is_final_or_atomic(A) :- atomic(A).

% quickly detect some deadlocked final constructs, for optimising seq/kleene
quick_is_final_deadlocked(seq([])).
quick_is_final_deadlocked(aut(Aut,S)) :-
   atomic(S),
   final_automata_state(Aut,S),
   \+ automata_trans(Aut,S,[],_,_,_). % assumes no predicates need to be evaluated !



% ------------------------
% UTILITIES

add_astd_err(M) :- %trace,
                   add_error(astd_interpreter,'*** ASTD Error: ',M),fail.


% utility to read terms from file:
read_terms(File,Terms) :- open(File,read,Stream), read_loop(0,Stream,Terms).

read_loop(Nr,Stream,Terms) :-
  read_term(Stream, Term, []), %print(read(Term)),nl,
  (Term=end_of_file -> Terms = [],close(Stream) ,format('Read ~w terms from file~n',[Nr])
   ; Terms = [Term|T], N1 is Nr+1, read_loop(N1,Stream,T)).
   

% allows setting values from ProB commandline if present, otherwise default used
    
argv_set_argument(Nr,Res,Default) :- external_functions:'ARGC'(int(Args)), % print(argc(Args)),nl,
  Nr =< Args,
  external_functions:'ARGV'(int(Nr),string(S)),!, 
  (number(Default) -> atom_codes(S,C),number_codes(Res,C) ; Res=S).
argv_set_argument(_,S,S).


%:- use_module(library(ordsets)).
% interpreter for actions
execute(V,Env,_) :- var(V),!, add_astd_err(variable_action(V,Env)).
execute(skip,Env,OutEnv) :- !, execute_skip(Env,OutEnv).
execute(inc(Var),Env,OutEnv) :- !,
   (lookup(Var,Env,Val) -> V1 is Val+1 ; V1=1),
   execute_individual_update(Env,Var,V1,OutEnv).
execute(iinc(Var),Env,OutEnv) :- !, % a version that generates fresh variable if needed
   (lookup(Var,Env,Val,no_errors) -> V1 is Val+1 ; V1=1),
   execute_individual_update(Env,Var,V1,OutEnv).
execute(add(Var,Element),Env,OutEnv) :- !, % add element to set
    eval(Element,Env,El),
   (lookup(Var,Env,Val) -> ord_add_element(Val,El,V1) ; V1=[El]),
   execute_individual_update(Env,Var,V1,OutEnv).
execute(':='(Var,Element),Env,OutEnv) :- !,
    eval(Element,Env,Val),
    execute_individual_update(Env,Var,Val,OutEnv).
% execute(if) -> we need reified version of test_pred
execute(';'(Stmt1,Stmt2),Env1,OutEnv) :- !,
   % will be sequential in C mode, parallel in B mode
   execute(Stmt1,Env1,U1),
   thread_sync_state(Env1,U1,Env2),
   execute(Stmt2,Env2,U2),
   merge_sync_states(';',U1,U2,OutEnv).
execute(E,_,_) :- add_astd_err(unknown_action(E)).

debug_test_pred(V,Env) :- 
    if(test_pred(V,Env), format('Test successful: ~w~n',[V]),
       (format('Test FAILS: ~w~n',[V]),fail)).

% interpreter for predicates, TO DO not_test_pred, co-routines
test_pred(V,Env) :- var(V),!, add_astd_err(variable_predicate(V,Env)).
test_pred(not(P),Env) :- !, test_not_pred(P,Env).
test_pred('<'(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_op(<,V1,V2).
test_pred('>='(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_op(>=,V1,V2).
test_pred('='(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), V1=V2.
test_pred(member(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_member(V1,V2).
test_pred(contains(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_contains(V1,V2).
test_pred(E,_) :- add_astd_err(unknown_pred(E)).

test_not_pred(V,Env) :- var(V),!, add_astd_err(variable_negated_predicate(V,Env)).
test_not_pred(not(P),Env) :- !, test_pred(P,Env).
test_not_pred('<'(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_op(>=,V1,V2).
test_not_pred('>='(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_op(<,V1,V2).
test_not_pred('='(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_op(\=,V1,V2).
test_not_pred(member(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_not_member(V1,V2).
test_not_pred(contains(E1,E2),Env) :- !, eval(E1,Env,V1),eval(E2,Env,V2), check_not_contains(V1,V2).
test_not_pred(E,_) :- add_astd_err(unknown_negated_pred(E)).

:- block check_op(?,-,?), check_op(?,?,-).
check_op(<,X,Y) :- X<Y.
check_op(>,X,Y) :- X>Y.
check_op(=<,X,Y) :- X=<Y.
check_op(>=,X,Y) :- X>=Y.
check_op(=,X,Y) :- X=Y.
check_op(\=,X,Y) :- X\=Y.

:- block check_contains(-,?), check_contains(?,-).
check_contains(Sequence,SubSeq) :- atom_codes(SubSeq,S1),atom_codes(Sequence,S0),append(S1,_,S2),append(_,S2,S0). % list sub-sequence
:- block check_not_contains(-,?), check_not_contains(?,-).
check_not_contains(Sequence,SubSeq) :- \+ check_contains(Sequence,SubSeq).

:- block check_member(-,?), check_member(?,-).
check_member(V1,V2) :- ord_member(V1,V2). % membership
:- block check_not_member(-,?), check_not_member(?,-).
check_not_member(V1,V2) :- \+ ord_member(V1,V2).

% interpreter for expressions
% basic values are integers, atoms, rec(.) and lists
:- block eval(-,?,?).
eval(V,Env,Res) :- if(eval2(V,Env,Res),true,add_astd_err(eval_failed(V,Env))).
eval2(V,Env,_) :- var(V),!, add_astd_err(variable_expression(V,Env)).
eval2(Nr,_,Res) :- number(Nr),!, Res=Nr.
eval2('+'(E1,E2),Env,Res) :- !, eval(E1,Env,V1),eval(E2,Env,V2), eval_op(+,V1,V2,Res).
eval2('$'(ID),Env,Res) :-  !,lookup(ID,Env,Res).
eval2(ID,_Env,Res) :- atom(ID),!,Res=ID.
eval2('->'(Rec,Field),Env,Res) :- atom(Field), !, 
   eval(Rec,Env,rec(Fields)),
   if(member(Field/Res,Fields),true, add_astd_err(unknown_field(Field,Fields))).
eval2(rec(Fields),_,Res) :- !, Res=rec(Fields). % TO DO: eval-fields
eval2([],_,Res) :- !,Res=[].
eval2([H|T],_,Res) :- !,Res=[H|T].
eval2(E,_,_) :- add_astd_err(unknown_expr(E)).

:- block eval_op(?,?,-,?), eval_op(?,-,?,?).
eval_op(+,X,Y,Res) :- Res is X+Y.

apply_updates(_,Upd,_) :- var(Upd),!, add_astd_err(var_updates(Upd)).
apply_updates(Env,Upd,NewEnv) :- sort(Upd,SUpd), store_updates(SUpd,Env,NewEnv).
store_updates([],S,S).
store_updates([K/Val,K/Val2|_T],_,_) :- !, add_astd_err(conflicting_update(K,Val,Val2)).
store_updates([K/Val|T],S1,S3) :- store(S1,K,Val,S2),
   store_updates(T,S2,S3).

merge_updates(ASTD,U1,U2,SRes) :- append(U1,U2,Res), sort(Res,SRes), check_updates(SRes,ASTD).

% check udpates for conflict
check_updates([],_).
check_updates([K/Val,K/Val2|_T],ASTD) :- !,add_astd_err(conflicting_update(K,Val,Val2,ASTD)).
check_updates([_|T],A) :- check_updates(T,A).

/* Store(OldEnv, VariableName, NewValue, NewEnv) */
store([],Key,Value,[Key/Value]) :- 
   print(assigning_undefined_var(Key,Value)),nl.
store([Key/_Value2|T],Key,Value,[Key/Value|T]).
store([Key2/Value2|T],Key,Value,[Key2/Value2|BT]) :-
   Key \== Key2, store(T,Key,Value,BT).

/* lookup(VariableName, Env, CurrentValue) */
lookup(Key,Env,Val) :- lookup(Key,Env,Val,generate_errors).
lookup(Key,[],_,generate_errors) :- add_astd_err(lookup_var_not_found_error(Key)).
lookup(Key,[Key/Value|_T],Value,_).
lookup(Key,[Key2/_Value2|T],Value,GenErr) :-
   Key \== Key2,
   lookup(Key,T,Value,GenErr).

def(Env,Key,[Key/undefined|Env]).


/* --------------------------------------------------------- */
/* make_non_ground(GroundRepOfExpr,NonGroundRepOfExpr) */
/* --------------------------------------------------------- */

/* ex. ?-make_non_ground(pos(term(f,[var(1),var(2),var(1)])),X). */

make_non_ground(G,NG) :-
	mkng(G,NG,[],_Sub).

mkng(avar,_,L1,L2) :- !,L1=L2. % anonymous variable
mkng(var(N),X,L1,L2) :- !,mkng_var(L1,N,X,L2).
mkng(X1,X2,InSub,OutSub) :- X1=..[F|Args],
	l_mkng(Args,IArgs,InSub,OutSub), X2 =.. [F|IArgs].

mkng_var([],N,X,[sub(N,X)]).
mkng_var([sub(N1,X1)|T1],N,X,[sub(N1,X1)|T2]) :-
   (N=N1 -> X1=X,T1=T2 ; mkng_var(T1,N,X,T2)).

l_mkng([],[],Sub,Sub).
l_mkng([H|T],[IH|IT],InSub,OutSub) :-
	mkng(H,IH,InSub,IntSub), l_mkng(T,IT,IntSub,OutSub).

/* ex. ?- make_non_ground_single_var(var(1),pos(term(f,[var(1),var(2),var(1)])),X). */
% only make non-ground known vars:
make_non_ground_single_var(var(Nr),G,NG) :-
	mkng_kv(G,NG,[sub(Nr,_)]).

mkng_kv(avar,_,_) :- !. % anonymous variable
mkng_kv(var(N),X,L1) :- !,mkng_known_var(L1,N,X).
mkng_kv(X1,X2,InSub) :- X1=..[F|Args],
	l_mkng_kv(Args,IArgs,InSub), X2 =.. [F|IArgs].

mkng_known_var([],N,var(N)).
mkng_known_var([sub(N1,X1)|T1],N,X) :-
   (N=N1 -> X1=X ; mkng_known_var(T1,N,X)).

l_mkng_kv([],[],_Sub).
l_mkng_kv([H|T],[IH|IT],InSub) :-
	mkng_kv(H,IH,InSub), l_mkng_kv(T,IT,InSub).

% ---------------------
% UTILITIES for semantic choice
% you can switch the definitions below from B/ASM to C 

% atrans(A1,G1,Trans,A2,G2)  --> G2 is either full global state or Delta Update

:-if(astd_sync_style(b)).

% B STYLE: collect updates and apply at the end:
execute_skip(_,[]).
thread_sync_state(G1,_G2,G1). % ASM/B style parallel: second process sees same initial state as first process
merge_sync_states(ASTD,G1,G2,G3) :-
   if(merge_updates(ASTD,G1,G2,G3),true, add_astd_err(merge_failed(ASTD,G1,G2,G3))).
%execute_individual_update(Env,Var,Val,G2) :-  print(execute_individual_update(Env,Var,Val,G2)),nl,fail.
execute_individual_update(_,Var,Val,[Var/Val]).
apply_global_updates(G1,Upd,G2) :- 
   if(apply_updates(G1,Upd,G2),true,add_astd_err(apply_failed(G1,Upd,G2))).

:- else.

% C STYLE/Interleaving: apply updates immediately
execute_skip(G,G).
thread_sync_state(_G1,G2,G2). % interleaving parallel: second process sees changes made by first processte_c(G1,G2,G3).
merge_sync_states(_ASTD,G1,G2,G3) :- G2=G3.
execute_individual_update(Env,Var,Val,G2) :- 
   store(Env,Var,Val,G2).
apply_global_updates(_G1,Upd,G2) :- G2=Upd. % updates already applied

:-endif.


