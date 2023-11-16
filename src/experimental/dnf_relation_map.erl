-module(dnf_relation_map).
-vsn({2,0,0}).

-define(P, {bdd_bool, relation_map}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/5]).

-export([map/1]).

% ==
% type interface
% ==
map(TyMap) -> gen_bdd:element(?P, TyMap).
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

is_empty(TyDnf) ->
  traverse_dnf(TyDnf, relation_map:b_anymap(), _NegatedMaps = [], fun phi/2).

traverse_dnf(0, _, _, _) -> true;
traverse_dnf({terminal, 1}, P, Ns, Phi) ->
  Phi(P, Ns);
traverse_dnf({node, RelMap, Left, Right}, P, Ns, Phi) ->
  {OptPos, ManPos} = relation_map:pi_fields(P),
  {Opt, Man} = relation_map:pi_fields(RelMap),
  NewMap = relation_map:map(
    dnf_ty_tuple:intersect(OptPos, Opt),
    dnf_ty_function:intersect(ManPos, Man)
  ),
  traverse_dnf(Left, NewMap, Ns, Phi)
    andalso traverse_dnf(Right, P, [RelMap | Ns], Phi).

phi(_, []) -> false;
phi(P, [N | Ns]) ->
  {OptPos, ManPos} = relation_map:pi_fields(P),
  {OptNeg, ManNeg} = relation_map:pi_fields(N),
  OptDiff = dnf_ty_tuple:diff(OptPos, OptNeg),
  ManDiff = dnf_ty_function:diff(ManPos, ManNeg),

  (dnf_ty_tuple:is_empty(OptDiff)
    andalso dnf_ty_function:is_empty(ManDiff)) orelse phi(P, Ns).


normalize(TyMap, [], [], Fixed, M) ->
  normalize_no_vars(TyMap, relation_map:b_anymap(), _NegatedMaps = [], Fixed, M);
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:relmap(dnf_var_relation_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:relmap(dnf_var_relation_map:var(Var)) end, M).

normalize_no_vars(_TyMap, _P, _N, _Fixed, _M) -> [].

