-module(dnf_ty_map).
-vsn({2,1,0}).

-define(P, {bdd_bool, ty_map}).
-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).
-define(NORM, fun ty_rec:normalize/3).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/5, substitute/3]).

-export([map/1, all_variables/1]).

-type dnf_map() :: term().
-type ty_map() :: dnf_map(). % ty_map:type()
-type dnf_ty_map() :: term().

-spec map(ty_map()) -> dnf_ty_map().
map(TyMap) -> gen_bdd:element(?P, TyMap).

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

is_empty(TyDnf) ->
  is_empty(TyDnf, ty_map:anymap(), _NegatedMaps = []).


is_empty(0, _, _) -> true;
is_empty({terminal, 1}, P, Ns) ->
  phi(P, Ns);
is_empty({node, TyMap, L_BDD, R_BDD}, P, Ns) ->
  is_empty(L_BDD, ty_map:intersect(TyMap, P), Ns)
    andalso
    is_empty(R_BDD, P, [TyMap | Ns]).

phi(_, []) -> false;
phi(P, [N | Ns]) ->
  StepsDiff = ty_map:diff_steps(P, N),
  W1Diff = ty_map:diff_w1(P, N),
  % ∀ 𝑘 . def(P)𝑘 \ def(N)𝑘 ≤ 0  ∧  def(P)Ω1 \ def(N)Ω1 ≤ 0  ∧  def(P)Ω2 \ def(N)Ω2 ≤ 0
  case lists:all(fun ty_rec:is_empty/1, [W1Diff | maps:values(StepsDiff)]) of
    true ->
      % ∀ ℓ ∈ L . P(ℓ) \ N(ℓ) <> 0
      Rest = filter_empty_labels(ty_map:diff_labels(P, N)),
      % ∀ ℓ ∈ Rest . Φ(P ∧ {ℓ : ¬N(ℓ)}, Ns)
      lists:all(
        fun(I) -> phi(I, Ns) end,
        [ty_map:intersect(P, anymap(AL, TyRef))  || AL := TyRef <- Rest]
      );
    false -> phi(P, Ns)
  end.


normalize(TyMap, [], [], Fixed, M) ->
  % nmap rule
  normalize_no_vars(TyMap, ty_map:anymap(), _NegatedMaps = [], Fixed, M);
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).

normalize_no_vars(0, _, _, _Fixed, _M) -> [[]]; % empty
normalize_no_vars({terminal, 1}, P, Ns, Fixed, M) ->
  phi_norm(P, Ns, Fixed, M);
normalize_no_vars({node, TyMap, L_BDD, R_BDD}, P, Ns, Fixed, M) ->
  X1 = ?F(normalize_no_vars(L_BDD, ty_map:intersect(TyMap, P), Ns, Fixed, M)),
  X2 = ?F(normalize_no_vars(R_BDD, P, [TyMap | Ns], Fixed, M)),
  constraint_set:meet(X1, X2).


phi_norm(_, [], _, _) -> [];
phi_norm(P, [N | Ns], Fixed, M) ->
  StepsDiff = ty_map:diff_steps(P, N),
  W1Diff = ty_map:diff_w1(P, N),
  LabelsDiff = ty_map:diff_labels(P, N),

  NormedKeyVars = ?F(norm_key_variables(
    ty_map:key_variable_suite(P), ty_map:key_variable_suite(N),
    Fixed,
    M
  )),
  NormedSteps = [?F(?NORM(TyRef, Fixed, M)) || TyRef <- [W1Diff | maps:values(StepsDiff)]],
  NormedLabels = [begin
                    X = ?F(elim_assoc_conflict(?NORM(TyRef, Fixed, M), A)),
                    Y = ?F(phi_norm(ty_map:intersect(P, anymap(AL, TyRef)), Ns, Fixed, M)),
                    ?F(constraint_set:join(X, Y))
                  end || {AL = {A, _}, TyRef} <- maps:to_list(LabelsDiff)],

  X1 = ?F(meet_all([NormedKeyVars | NormedSteps ++ NormedLabels])),
  X2 = ?F(phi_norm(P, Ns, Fixed, M)),
  constraint_set:join(X1, X2).


norm_key_variables({O1, O2, PosManU, PosOptU}, {O11, O22, NegManU, NegOptU}, Fixed, M) ->
  Bound = fun(VarUnion, Lower, Upper) ->
    % this case (needed) resembles a null check, maybe get rid of it
    case ty_rec:is_empty(VarUnion) of
      true -> [[]]; % escape
      false -> % actual bounding
        constraint_set:meet(
          ?F(?NORM(ty_rec:diff(Lower, VarUnion), Fixed, M)),
          ?F(?NORM(ty_rec:diff(VarUnion, Upper), Fixed, M)))
    end
          end,
  {PosO1, PosO2} = {ty_rec:diff(O1, O11), ty_rec:diff(O2, O22)},
  {NegO1, NegO2} = {ty_rec:diff(O11, O1), ty_rec:diff(O22, O2)},

  meet_all([
    ?F(Bound(PosManU, PosO1, PosO1)),
    ?F(Bound(PosOptU, PosO2, PosO2)),
    ?F(Bound(NegManU, NegO1, NegO1)),
    ?F(Bound(NegOptU, NegO2, NegO2))
  ]).


substitute(0, _, _) -> 0;
substitute({terminal, 1}, _, _) ->
  {terminal, 1};
substitute({node, TyMap, L_BDD, R_BDD}, SubstituteMap, Memo) ->
  NewTyMap = ty_map:substitute(TyMap, SubstituteMap, Memo),
  union(
    intersect(map(NewTyMap), substitute(L_BDD, SubstituteMap, Memo)),
    intersect(negate(map(NewTyMap)), substitute(R_BDD, SubstituteMap, Memo))
  ).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, TyMap, PositiveEdge, NegativeEdge}) ->
  ty_map:all_variables(TyMap) ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).


anymap(AL, TyRef) ->
  ty_map:map(#{AL => TyRef}, maps:from_keys(ty_map:step_names(), ty_rec:any())).
filter_empty_labels(Labels) -> maps:filter(
  fun({?OPT, _}, _) -> true;
     ({?MAN, _}, TyRef) -> not ty_rec:is_empty(TyRef)
  end, Labels).
elim_assoc_conflict(_Constraints = C, _Association = A) ->
  case {C, A} of
    {[[]], ?OPT} -> []; % [[]] must only occur with mandatory
    {[], ?OPT} -> [[]]; % ⊥ exists as solution
    _ -> C
  end.
meet_all(Cs) -> lists:foldr(fun(C, Rest) -> constraint_set:meet(C, ?F(Rest)) end, [[]], Cs).