-module(dnf_var_ty_atom).
-vsn({1,2,0}).

-define(P, {ty_atom, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1]).

-export([ty_var/1, ty_atom/1]).

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
