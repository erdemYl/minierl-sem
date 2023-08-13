-module(dnf_ty_function).
-vsn({1,3,1}).

-define(P, {bdd_bool, ty_function}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1]).

-export([function/1]).

-type ty_ref() :: {ty_ref, integer()}.
-type dnf_function() :: term().
-type ty_function() :: dnf_function(). % ty_function:type()
-type dnf_ty_function() :: term().

-spec function(ty_function()) -> dnf_ty_function().
function(TyFunction) -> gen_bdd:element(?P, TyFunction).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() ->
  gen_bdd:any(?P).

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

is_empty(TyDnf) ->
  is_empty(
    TyDnf,
    ty_rec:empty(), [], []
  ).

is_empty(0, _, _, _) -> true;
is_empty({terminal, 1}, _, _, []) -> false;
is_empty({terminal, 1}, S, P, [Function | N]) ->
  T1 = ty_function:domain(Function),
  T2 = ty_function:codomain(Function),
  (
  %% ∃ T1-->T2 ∈ N s.t.
  %%    T1 is in the domain of the function
  %%    S is the union of all domains of the positive function intersections
  ty_rec:is_subtype(T1, S)
    andalso
    explore_function(T1, ty_rec:negate(T2), P)
  )
  %% Continue searching for another arrow ∈ N
    orelse
    is_empty({terminal, 1}, S, P, N)
  ;
is_empty({node, Function, L_BDD, R_BDD}, S, P, N) ->
  T1 = ty_function:domain(Function),
  is_empty(L_BDD, ty_rec:union(S, T1), [Function | P], N)
  andalso
    is_empty(R_BDD, S, P, [Function | N])
.

% optimized phi' (4.10) from paper covariance and contravariance
% justification for this version of phi can be found in `prop_phi_function.erl`
-spec explore_function(ty_ref(), ty_ref(), [term()]) -> boolean().
explore_function(T1, T2, []) ->
  ty_rec:is_empty(T2) orelse ty_rec:is_empty(T1);
explore_function(T1, T2, [Function | P]) ->
  ty_rec:is_empty(T1) orelse ty_rec:is_empty(T2)
  orelse
  begin
    S1 = ty_function:domain(Function),
    S2 = ty_function:codomain(Function),
    explore_function(T1, ty_rec:intersect(T2, S2), P)
      andalso
      explore_function(ty_rec:diff(T1, S1), T2, P)
      end.





-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  %   (int -> int) ^ (1 -> 2)
  TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIc = ty_rec:interval(dnf_var_int:int(ty_interval:interval(1, 1))),
  TId = ty_rec:interval(dnf_var_int:int(ty_interval:interval(2, 2))),

  Ty_FunctionA = ty_function:function(TIa, TIb),
  Ty_FunctionB = ty_function:function(TIc, TId),

  B1 = dnf_ty_function:function(Ty_FunctionA),
  B2 = dnf_ty_function:function(Ty_FunctionB),

  Bdd = dnf_ty_function:intersect(B1, B2),

  false = dnf_ty_function:is_empty(Bdd),
%%  io:format(user, "~p~n", [Bdd]),

  ok.
-endif.
