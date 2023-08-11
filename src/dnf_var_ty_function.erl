-module(dnf_var_ty_function).
-vsn({1,2,0}).

-define(P, {dnf_ty_function, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1]).

-export([var/1, function/1]).

-type dnf_function() :: term().
-type ty_function() :: dnf_function(). % ty_function:type()
-type variable() :: term(). % variable:type()
-type dnf_var_function() :: term().

-spec function(ty_function()) -> dnf_var_function().
function(Tuple) -> gen_bdd:terminal(?P, Tuple).

-spec var(variable()) -> dnf_var_function().
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


% TODO memoize α1∧…∧αn ∧ ¬β1∧…∧¬βm ∧ t
is_empty(0) -> true;
is_empty({terminal, Function}) ->
  dnf_ty_function:is_empty(Function);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    and is_empty(NegativeEdge).



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  %   a1 ^ (int -> int)
  TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
  Ty_Function = ty_function:function(TIa, TIb),

  VarA = ty_variable:new("a1"),

  Dnf_Ty_Function = dnf_ty_function:function(Ty_Function),

  BVar1 = dnf_var_ty_function:var(VarA),
  BFunctionA = dnf_var_ty_function:function(Dnf_Ty_Function),

  Bdd = dnf_var_ty_function:intersect(BVar1, BFunctionA),

  false = dnf_var_ty_function:is_empty(Bdd),
%%  io:format(user, "~p~n", [Bdd]),

  ok.

-endif.
