-module(dnf_var_ty_atom).
-vsn({2,1,0}).

-define(P, {ty_atom, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/3, substitute/2]).

-export([ty_var/1, ty_atom/1, all_variables/1, to_singletons/1]).

-type ty_atom() :: term().
-type ty_variable() :: term(). % variable:type()
-type dnf_var_ty_atom() :: term().

-spec ty_atom(ty_atom()) -> dnf_var_ty_atom().
ty_atom(Atom) -> gen_bdd:terminal(?P, Atom).

-spec ty_var(ty_variable()) -> dnf_var_ty_atom().
ty_var(Var) -> gen_bdd:element(?P, Var).

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


% ==
% Emptiness for variable atom DNFs
% ==

is_empty(0) -> true;
is_empty({terminal, Atom}) ->
  ty_atom:is_empty(Atom);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    andalso is_empty(NegativeEdge).


normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize(0, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Atom}, PVar, NVar, Fixed, M) ->
  ty_atom:normalize(Atom, PVar, NVar, Fixed, M);
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).

substitute(T, M) -> substitute(T, M, [], []).

substitute(0, _, _, _) -> 0;
substitute({terminal, Atom}, Map, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      ty_rec:pi(atom, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(atom, NewNeg)
    end, Neg),

  lists:foldl(fun(Current, All) -> intersect(Current, All) end, ty_atom(Atom), AllPos ++ AllNeg);

substitute({node, Variable, PositiveEdge, NegativeEdge}, Map, P, N) ->

  LBdd = substitute(PositiveEdge, Map, [Variable | P], N),
  RBdd = substitute(NegativeEdge, Map, P, [Variable | N]),

  union(LBdd, RBdd).


all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
[Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).


to_singletons(0) -> [];
to_singletons({terminal, TyAtom}) -> ty_atom:to_singletons(TyAtom);
to_singletons({node, _Variable, _, _}) -> [].
