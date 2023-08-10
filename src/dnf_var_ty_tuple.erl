-module(dnf_var_ty_tuple).
-vsn({1,0,0}).

-define(P, {dnf_ty_tuple, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1]).

-export([var/1, tuple/1]).

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
  %   a1 ^ (int, int)
  TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  Ty_Tuple = ty_tuple:tuple(TIa, TIb),

  VarA = ty_variable:new("a1"),

  Dnf_Ty_Tuple = dnf_ty_tuple:tuple(Ty_Tuple),

  BVar1 = dnf_var_ty_tuple:var(VarA),
  BTupleA = dnf_var_ty_tuple:tuple(Dnf_Ty_Tuple),

  Bdd = dnf_var_ty_tuple:intersect(BVar1, BTupleA),

  io:format(user, "~p~n", [Bdd]),

  ok.

-endif.
