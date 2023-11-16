-module(dnf_var_ty_map).
-vsn({2,2,1}).

-define(P, {dnf_ty_map, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/3, substitute/3]).

-export([var/1, map/1, all_variables/1]).

-type dnf_map() :: term().
-type ty_map() :: dnf_map(). % ty_map:type()
-type variable() :: term(). % variable:type()
-type dnf_var_map() :: term().

-spec map(ty_map()) -> dnf_var_map().
map(Map) -> gen_bdd:terminal(?P, Map).

-spec var(variable()) -> dnf_var_map().
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
is_empty({terminal, Map}) ->
  dnf_ty_map:is_empty(Map);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    and is_empty(NegativeEdge).

normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize(0, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Map}, PVar, NVar, Fixed, M) ->
  case ty_ref:is_normalized_memoized(Map, Fixed, M) of
    true ->
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_map:normalize(Map, PVar, NVar, Fixed, sets:union(M, sets:from_list([Map])))
  end;
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).

substitute(T, M, Memo) -> substitute(T, M, Memo, [], []).

substitute(0, _, _, _, _) -> 0;
substitute({terminal, Map}, SubstituteMap, Memo, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, SubstituteMap, ty_rec:variable(Var)),
      ty_rec:pi(map, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, SubstituteMap, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(map, NewNeg)
    end, Neg),

  lists:foldl(fun intersect/2, map(dnf_ty_map:substitute(Map, SubstituteMap, Memo)), AllPos ++ AllNeg);

substitute({node, Variable, PositiveEdge, NegativeEdge}, Map, Memo, P, N) ->
  LBdd = substitute(PositiveEdge, Map, Memo, [Variable | P], N),
  RBdd = substitute(NegativeEdge, Map, Memo, P, [Variable | N]),
  union(LBdd, RBdd).


all_variables(0) -> [];
all_variables({terminal, Map}) -> dnf_ty_map:all_variables(Map);
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).
