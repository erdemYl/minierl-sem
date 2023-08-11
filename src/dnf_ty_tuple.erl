-module(dnf_ty_tuple).
-vsn({1,2,0}).

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

is_empty(TyRef) -> is_empty(
  TyRef,
  _PiLeftCollected = ty_rec:any(), _PiRightCollected = ty_rec:any(),
  _NegatedTuples = []
).

is_empty(0, _Left, _Right, _Negated) -> true;
is_empty({terminal, 1}, Left, Right, Negated) ->
  ty_rec:is_empty(Left)
  orelse ty_rec:is_empty(Right)
  orelse explore_tuple(Left, Right, Negated);
is_empty({node, Ty, L_BDD, R_BDD}, LeftSum, RightSum, Negated) ->
  LRef = ty_tuple:pi1(Ty),
  RRef = ty_tuple:pi2(Ty),

  NewLeftSum  = ty_rec:intersect(LRef, LeftSum),
  NewRightSum  = ty_rec:intersect(RRef, RightSum),
  is_empty(L_BDD, NewLeftSum, NewRightSum, Negated)
  andalso
    is_empty(R_BDD, LeftSum, RightSum, [Ty | Negated]).

explore_tuple(_, _, []) -> false;
explore_tuple(Left, Right, [Ty | N]) ->
  T1 = ty_tuple:pi1(Ty),
  T2 = ty_tuple:pi2(Ty),

  (ty_rec:is_subtype(Left, T1) orelse explore_tuple(ty_rec:diff(Left,T1), Right, N))
  andalso
    (ty_rec:is_subtype(Right, T2) orelse explore_tuple(Left, ty_rec:diff(Right,T2), N)).



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

%%  io:format(user, "~p~n", [Bdd]),
  false = dnf_ty_tuple:is_empty(Bdd),

  ok.
-endif.
