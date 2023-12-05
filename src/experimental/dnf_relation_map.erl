-module(dnf_relation_map).
-vsn({2,0,0}).

-define(P, {bdd_bool, relation_map}).
-define(F(Z), fun() -> Z end).

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
  traverse_dnf(TyDnf, relation_map:anymap(), _NegatedMaps = [], fun phi/2).

traverse_dnf(0, _, _, Phi) -> Phi(relation_map:empty(), []);
traverse_dnf({terminal, 1}, P, Ns, Phi) ->
  Phi(P, Ns);
traverse_dnf({node, RelMap, Left, Right}, P, Ns, Phi) ->
  andalso_(
  ?F(traverse_dnf(Left, relation_map:intersect(RelMap, P), Ns, Phi)),
  ?F(traverse_dnf(Right, P, [RelMap | Ns], Phi))).

phi(P, []) ->
  {Opt, Man} = relation_map:pi_fields(P),
  dnf_ty_tuple:is_empty(Opt) andalso not dnf_ty_function:is_any(Man);
phi(P, [N | Ns]) ->
  {OptPos, ManPos} = relation_map:pi_fields(P),
  {OptNeg, ManNeg} = relation_map:pi_fields(N),
  OptDiff = dnf_ty_tuple:diff(OptPos, OptNeg),
  ManDiff = dnf_ty_function:diff(ManPos, ManNeg),

  (dnf_ty_tuple:is_empty(OptDiff)
    andalso dnf_ty_function:is_empty(ManDiff)) orelse phi(P, Ns).

%%% relation x relation
%%phi_2(Ps, Ns) ->
%%  {PosOpts, PosMans} = lists:unzip(lists:map(fun relation_map:pi_fields/1, Ps)),
%%  BigInt = lists:foldr(fun dnf_ty_tuple:intersect/2, dnf_ty_tuple:any(), PosOpts),
%%
%%  LargerNs = lists:filter(fun(N) ->
%%    {OptNeg, _} = relation_map:pi_fields(N),
%%    dnf_ty_tuple:is_empty(dnf_ty_tuple:diff(BigInt, OptNeg))
%%                          end, Ns),
%%
%%  lists:any(fun(N) ->
%%    {_, ManNeg} = relation_map:pi_fields(N),
%%    lists:any(fun(Man) -> dnf_ty_tuple:is_empty(dnf_ty_tuple:diff(Man, ManNeg)) end, PosMans)
%%            end, LargerNs).


normalize(DnfRelMap, [], [], Fixed, M) ->
  normalize_no_vars(DnfRelMap, relation_map:anymap(), _NegatedMaps = [], Fixed, M);
normalize(DnfRelMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:relmap(dnf_var_relation_map:map(DnfRelMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:relmap(dnf_var_relation_map:var(Var)) end, M).

normalize_no_vars(DnfRelMap, P, Ns, Fixed, M) ->
  traverse_dnf(DnfRelMap, P, Ns, phi_norm(Fixed, M)).

phi_norm(Fixed, M) ->
  fun
    Norm(P, []) ->
      {Opt, Man} = relation_map:pi_fields(P),
      X = ?F(dnf_ty_tuple:normalize(Opt, [], [], Fixed, M)),
      Y = ?F(dnf_ty_function:normalize(Man, [], [], Fixed, M)),
      constraint_set:meet(X, Y);
    Norm(P, [N | Ns]) ->
      {OptPos, ManPos} = relation_map:pi_fields(P),
      {OptNeg, ManNeg} = relation_map:pi_fields(N),
      OptDiff = dnf_ty_tuple:diff(OptPos, OptNeg),
      ManDiff = dnf_ty_function:diff(ManPos, ManNeg),
      OptC = ?F(dnf_ty_tuple:normalize(OptDiff, [], [], Fixed, M)),
      ManC = ?F(dnf_ty_function:normalize(ManDiff, [], [], Fixed, M)),
      constraint_set:join(?F(constraint_set:meet(OptC, ManC)), ?F(Norm(P, Ns)))
  end.

%%% relation x relation
%%phi_norm_2(Fixed, M) ->
%%  fun(Ps, Ns) ->
%%    {PosOpts, PosMans} = lists:unzip(lists:map(fun relation_map:pi_fields/1, Ps)),
%%    BigInt = lists:foldr(fun dnf_ty_tuple:intersect/2, dnf_ty_tuple:any(), PosOpts),
%%
%%    FindN = lists:map(fun(N) ->
%%      {OptNeg, _} = relation_map:pi_fields(N),
%%      Normed = ?F(dnf_ty_tuple:normalize(dnf_ty_tuple:diff(BigInt, OptNeg), [], [], Fixed, M)),
%%      {N, Normed}
%%                      end, Ns),
%%
%%    FindP = lists:flatten(lists:map(fun({N, Nrm}) ->
%%      {_, ManNeg} = relation_map:pi_fields(N),
%%      lists:map(fun(Man) ->
%%        Normed = ?F(dnf_ty_tuple:normalize(dnf_ty_tuple:diff(Man, ManNeg), [], [], Fixed, M)),
%%        ?F(constraint_set:meet(Nrm, Normed))
%%                end, PosMans)
%%                                    end, FindN)),
%%
%%    join_all(FindP)
%%  end.
%%join_all(Cs) -> lists:foldr(fun(C, A) -> constraint_set:join(C, ?F(A)) end, [], Cs).

andalso_(L, R) ->
  case L() of
    true -> R(); false -> false;
    [[]] -> R(); [] -> [];
    CSets -> constraint_set:merge_and_meet(CSets, R())
  end.

