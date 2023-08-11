-module(dnf_ty_tuple).
-vsn({1,1,0}).

-define(P, {bdd_bool, ty_tuple}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1]).

-export([tuple/1]).

-type dnf_tuple() :: term().
-type ty_tuple() :: dnf_tuple(). % ty_tuple:type()
-type dnf_ty_tuple() :: term().

-spec tuple(ty_tuple()) -> dnf_ty_tuple().
tuple(TyTuple) -> gen_bdd:element(?P, TyTuple).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

eval(B) -> gen_bdd:eval(?P, B).
is_any(B) -> gen_bdd:is_any(?P, B).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

is_empty(B) -> is_empty(
  B,
  ty_rec:any(), ty_rec:any(),
  [], [], []
).

is_empty(0, _Left, _Right, _Negated, _PVar, _NVar) -> true;
is_empty(_, _Left, _Right, _Negated, _PVar, _NVar) -> erlang:error("TODO").



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               LISTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%is_empty_list({bdd, 1}, Left, Right, Negated, [], [], SymTab, Memo) ->
%%  % no more variables
%%
%%  (is_empty(Left, SymTab, Memo)
%%    orelse is_empty(Right, SymTab, Memo)
%%    orelse explore_list(Left, Right, Negated, SymTab, Memo));
%%
%%is_empty_list({bdd, 1}, Left, Right, Negated, PVars, [Var | NVars], SymTab, Memo) ->
%%  logger:debug("Removing negative variable from list clause: substitute in both positive and negative tuples:~n !~p => ~p", [Var, Var]),
%%
%%  Map = #{ Var => stdtypes:tnegate(Var) },
%%  NsWithoutNegativeVars = [ {bdd_list, substitute_bdd(Map, A), substitute_bdd(Map, B)} || {bdd_list, A, B} <- Negated ],
%%  is_empty_list({bdd, 1}, substitute_bdd(Map, Left), substitute_bdd(Map, Right), NsWithoutNegativeVars, PVars, NVars, SymTab, Memo);
%%is_empty_list({bdd, 1}, Left, Right, Negated, [StdVar | PVars], [], SymTab, Memo) ->
%%  logger:debug("Removing positive variable from list clause~nsubstitute toplevel positive: ~n~p => (y1..yn)~nsubstitute negative and positive components: ~n~p => (y1..yn) U ~p", [StdVar, StdVar, StdVar]),
%%
%%  {Avar, Bvar} = {fresh_variable(StdVar), fresh_variable(StdVar)},
%%  SubstitutionStdMap = #{StdVar => stdtypes:tunion([StdVar, stdtypes:tlist_improper(Avar, Bvar)]) },
%%
%%  % covariance of lists: intersect left/right with (v1, v2)
%%  LeftNew = intersect(norm(Avar), Left),
%%  RightNew = intersect(norm(Bvar), Right),
%%
%%  NNoVars = [ {bdd_list, substitute_bdd(SubstitutionStdMap, S), substitute_bdd(SubstitutionStdMap, T)}
%%    || {bdd_list, S, T} <- Negated ],
%%
%%  % continue removing positive variables
%%  is_empty_list({bdd, 1}, LeftNew, RightNew, NNoVars, PVars, [], SymTab, Memo);
%%
%%is_empty_list({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, LL, RR, Negated, PVar, NVar, SymTab, Memo) ->
%%  Ty = find_ty(Ref, Args, list, SymTab),
%%
%%  is_empty_list(bdd_lazy:intersect(Left, Ty), LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_list(Middle, LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_list(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), LL, RR, Negated, PVar, NVar, SymTab, Memo);
%%% collecting variables
%%is_empty_list({bdd, {bdd_var, Var}, Left, Middle, Right}, LL, RR, Negated, PVar, NVar, SymTab, Memo) ->
%%  is_empty_list(Left, LL, RR, Negated, PVar ++ [stdtypes:tvar(Var)], NVar, SymTab, Memo) andalso
%%    is_empty_list(Middle, LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_list(Right, LL, RR, Negated, PVar, NVar ++ [stdtypes:tvar(Var)], SymTab, Memo);
%%is_empty_list({bdd, {bdd_list, A, B}, Left, Middle, Right}, LL, RR, Negated, PVar, NVar, SymTab, Memo) ->
%%  %% norming
%%  is_empty_list(Left, intersect(A, LL), intersect(B, RR), Negated, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_list(Middle, LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_list(Right, LL, RR, Negated ++ [{bdd_list, A, B}], PVar, NVar, SymTab, Memo).
%%
%%explore_list(_S1, _S2, [], _SymTab, _Memo) -> false;
%%explore_list(S1, S2, [{bdd_list, T1, T2} | N], Symtab, Memo) ->
%%  ((subty:is_subty_bdd(S1, T1, Symtab, Memo) orelse explore_list(ty_rec:diff(S1, T1), S2, N, Symtab, Memo))
%%    andalso
%%    (subty:is_subty_bdd(S2, T2, Symtab, Memo) orelse explore_list(S1, ty_rec:diff(S2, T2), N, Symtab, Memo))).
%%
%%



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  %   (int, int) ^ (1, 2)
  TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIc = ty_rec:interval(dnf_var_int:int(ty_interval:interval(1, 1))),
  TId = ty_rec:interval(dnf_var_int:int(ty_interval:interval(2, 2))),

  Ty_TupleA = ty_tuple:tuple(TIa, TIb),
  Ty_TupleB = ty_tuple:tuple(TIc, TId),

  B1 = dnf_ty_tuple:tuple(Ty_TupleA),
  B2 = dnf_ty_tuple:tuple(Ty_TupleB),

  Bdd = dnf_ty_tuple:intersect(B1, B2),

  io:format(user, "~p~n", [Bdd]),

  ok.
-endif.
