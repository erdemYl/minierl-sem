-module(dnf_var_ty_tuple).
-vsn({2,1,0}).

-define(P, {dnf_ty_tuple, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/3, substitute/3]).

-export([var/1, tuple/1, all_variables/1, has_ref/2, to_singletons/1]).

-type dnf_tuple() :: term().
-type ty_tuple() :: dnf_tuple(). % ty_tuple:type()
-type variable() :: term(). % variable:type()
-type dnf_var_tuple() :: term().

-spec tuple(ty_tuple()) -> dnf_var_tuple().
tuple(Tuple) -> gen_bdd:terminal(?P, Tuple).

-spec var(variable()) -> dnf_var_tuple().
var(Var) -> gen_bdd:element(?P, Var).

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


is_empty(0) -> true;
is_empty({terminal, Tuple}) ->
  dnf_ty_tuple:is_empty(Tuple);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    and is_empty(NegativeEdge).

normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize(0, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Tuple}, PVar, NVar, Fixed, M) ->
  case ty_ref:is_normalized_memoized(Tuple, Fixed, M) of
    true ->
      % TODO test case
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_tuple:normalize(Tuple, PVar, NVar, Fixed, sets:union(M, sets:from_list([Tuple])))
  end;
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).


substitute(T, M, Memo) -> substitute(T, M, Memo, [], []).

substitute(0, _, _, _, _) -> 0;
substitute({terminal, Tuple}, Map, Memo, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      ty_rec:pi(tuple, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(tuple, NewNeg)
    end, Neg),

  lists:foldl(fun(Current, All) -> intersect(Current, All) end, tuple(dnf_ty_tuple:substitute(Tuple, Map, Memo)), AllPos ++ AllNeg);

substitute({node, Variable, PositiveEdge, NegativeEdge}, Map, Memo, P, N) ->

  LBdd = substitute(PositiveEdge, Map, Memo, [Variable | P], N),
  RBdd = substitute(NegativeEdge, Map, Memo, P, [Variable | N]),

  union(LBdd, RBdd).

has_ref(0, _) -> false;
has_ref({terminal, Tuple}, Ref) ->
  dnf_ty_tuple:has_ref(Tuple, Ref);
has_ref({node, _Variable, PositiveEdge, NegativeEdge}, Ref) ->
  has_ref(PositiveEdge, Ref) orelse has_ref(NegativeEdge, Ref).

all_variables(0) -> [];
all_variables({terminal, Tuple}) -> dnf_ty_tuple:all_variables(Tuple);
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).


to_singletons(0) -> [];
to_singletons({terminal, TyTuple}) -> dnf_ty_tuple:to_singletons(TyTuple);
to_singletons({node, _Variable, _, _}) -> [].


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  %   a1 ^ (int, int)
  TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  Ty_Tuple = ty_tuple:tuple(TIa, TIb),

  VarA = ty_variable:new("a1"),

  Dnf_Ty_Tuple = dnf_ty_tuple:tuple(Ty_Tuple),

  BVar1 = dnf_var_ty_tuple:var(VarA),
  BTupleA = dnf_var_ty_tuple:tuple(Dnf_Ty_Tuple),

  Bdd = dnf_var_ty_tuple:intersect(BVar1, BTupleA),

  false = dnf_var_int:is_empty(Bdd),
%%  io:format(user, "~p~n", [Bdd]),

  ok.

-endif.
