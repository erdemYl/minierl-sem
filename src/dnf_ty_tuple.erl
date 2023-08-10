-module(dnf_ty_tuple).
-vsn({1,0,0}).

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
is_empty(B) -> gen_bdd:is_empty(?P, B).
is_any(B) -> gen_bdd:is_any(?P, B).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).



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
