-module(dnf_var_int).
-vsn({1,0,0}).

-define(P, {ty_interval, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1]).

-export([var/1, int/1]).

-type interval() :: term(). % interval:type()
-type variable() :: term(). % variable:type()
-type dnf_var_int() :: term().

-spec int(interval()) -> dnf_var_int().
int(Interval) -> gen_bdd:terminal(?P, Interval).

-spec var(variable()) -> dnf_var_int().
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
  %   a1 ^ !a3 ^ 2-10
  % U a1 ^ 1-10
  % U !a2 ^ 5-8
  Ia = ty_interval:interval(2, 10),
  Ib = ty_interval:interval(1, 10),
  Ic = ty_interval:interval(5, 8),

  VarA = ty_variable:new("a1"),
  VarB = ty_variable:new("a2"),
  VarC = ty_variable:new("a3"),

  BIntA = dnf_var_int:int(Ia),
  BVar1 = dnf_var_int:var(VarA),
  BVar2 = dnf_var_int:var(VarB),
  BVar3 = dnf_var_int:var(VarC),
  BIntB = dnf_var_int:int(Ib),
  BIntC = dnf_var_int:int(Ic),

  U1 = dnf_var_int:intersect(dnf_var_int:intersect(BIntA, BVar1), dnf_var_int:negate(BVar3)),
  U2 = dnf_var_int:intersect(BVar1, BIntB),
  U3 = dnf_var_int:intersect(BIntC, dnf_var_int:negate(BVar2)),

  Bdd = dnf_var_int:union(dnf_var_int:union(U1, U2), U3),

  io:format(user, "~p~n", [Bdd]),

  ok.

compact_ints_test() ->
  %   1-5
  % U 6-10 -> 1-10
  Ia = ty_interval:interval(1, 5),
  Ib = ty_interval:interval(6, 10),

  BIntA = dnf_var_int:int(Ia),
  BIntB = dnf_var_int:int(Ib),

  Bdd = dnf_var_int:union(BIntA, BIntB),

  io:format(user, "~p~n", [Bdd]),

  ok.

-endif.
