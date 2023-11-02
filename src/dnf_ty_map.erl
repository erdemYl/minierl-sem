-module(dnf_ty_map).
-vsn({2,6,0}).

-define(P, {bdd_bool, ty_map}).
-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([is_any/1, eval/1, is_empty/1, empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([map/1, to_unf/1, normalize/5, all_variables/1]).

-import(ty_map, [map/2, pi/2, pi_var/2]).
-import(maps, [values/1, is_key/2, merge_with/3, filtermap/2]).

-type dnf_map() :: term().
-type ty_map() :: dnf_map(). % ty_map:type()
-type dnf_ty_map() :: term().
-type unf_map() :: term().

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


-spec to_unf(dnf_map()) -> unf_map().
to_unf(0) -> ty_unf_map:empty();
to_unf({terminal, 1}) -> ty_unf_map:any();
to_unf(TyDnf) ->
  traverse_dnf(TyDnf, ty_map:b_anymap(), _NegatedMaps = [],
    fun(P, Ns) ->
      lists:foldr(
        fun(Neg, Pos) -> ty_unf_map:diff(Pos, Neg) end,
        ty_unf_map:map(P),
        [ty_unf_map:map(N) || N <- Ns])
    end
).

is_empty(TyDnf) -> traverse_dnf(
  TyDnf,
  ty_map:b_anymap(),
  _NegatedMaps = [],
  fun phi/2
).

traverse_dnf(0, _, _, Phi) -> Phi(ty_map:b_empty(), []);
traverse_dnf({terminal, 1}, P, N, Phi) ->
  Phi(P, N);
traverse_dnf({node, TyMap, Left, Right}, PosTyMap = {_, PosLs, PosSt}, N, Phi) ->
  andalso_(
    ?F(traverse_dnf(Left, ty_map:b_intersect(TyMap, PosTyMap), N, Phi)),
    ?F(traverse_dnf(Right, ty_map:map(PosLs, PosSt), [TyMap | N], Phi))
  ).

andalso_(L, R) ->
  case L() of
    true -> R(); false -> false;
    [[]] -> R(); [] -> [];
    CSets -> constraint_set:merge_and_meet(CSets, R())
  end.

phi({_, Labels, Steps}, []) ->
  #{} == filter_empty_labels(Labels) andalso
    #{} == Steps;
phi(P, [N]) ->
  {_, LsDiff, StD} = ty_map:b_diff(P, N),
  StDiff = maps:filter(fun(_, TyRef) -> not ty_rec:is_empty(TyRef) end, StD),
  phi(map(LsDiff, StDiff), []);
phi(P = {_, Labels, Steps}, [N | Ns]) ->
  % ∀ ℓ ∈ L . P(ℓ) \ N(ℓ)
  % ∀ 𝑘 ∈ Steps . (def(P))𝑘 \ (def(N))𝑘
  {_, LsDiff, StDiff} = ty_map:b_diff(P, N),

  #{atom_key := StepAtom,
    integer_key := StepInt,
    tuple_key := StepTuple} = StDiff,

  % ∀ 𝑘 . (def(P))𝑘 \ (def(N))𝑘 ~ 0
  case ty_rec:is_empty(StepAtom)
    andalso ty_rec:is_empty(StepInt)
    andalso ty_rec:is_empty(StepTuple)
  of
    true ->
      % ∀ ℓ ∈ L . P(ℓ) \ N(ℓ) <> 0
      Rest = filter_empty_labels(LsDiff),
      #{} == Rest orelse
        % ∀ ℓ ∈ Rest . Φ(P ∧ {ℓ : ¬N(ℓ)}, Ns)
        lists:all(
          fun({AL, DiffTyRef}) ->
            phi(map(Labels#{AL => DiffTyRef}, Steps), Ns)
          end,
          maps:to_list(Rest))
    ;
    false -> phi(P, Ns)
  end.

filter_empty_labels(Ls) ->
  maps:filter(fun({A, _}, TyRef) ->
    case A of
      ?OPT -> true;
      ?MAN -> not ty_rec:is_empty(TyRef)
    end
              end, Ls).


normalize(TyMap, [], [], Fixed, M) ->
  % nmap rule
  normalize_no_vars(TyMap, ty_map:b_anymap(), _NegatedMaps = [], Fixed, M);
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).

normalize_no_vars(TyMap, P, N, Fixed, M) ->
  traverse_dnf(TyMap, P, N, phi_norm(Fixed, M)).

phi_norm(Fixed, M) -> fun
    Norm(P = {_, Labels, Steps}, []) ->
      case P == ty_map:b_empty() of
        true -> [[]]; % satisfied
        false ->
          KeyC = constrain_key_vars(P, Fixed, M),
          C1 = [?F(ty_rec:normalize(TyRef, Fixed, M)) || _ := TyRef <- Steps],
          C2 = [?F(ty_rec:normalize(TyRef2, Fixed, M)) || _ := TyRef2 <- Labels],
          (lazy_meet([KeyC | C1 ++ C2]))()
      end;
    Norm(P = {_, Labels, Steps}, [N | Ns]) -> {_, NegLabels, NegSteps} = N,
      KeyC1 = constrain_key_vars(N, Fixed, M),
      KeyC2 = constrain_key_vars(P, N, Fixed, M),

      % ∀ 𝑘 ∈ Steps . (def'(P))𝑘 \ (def'(N))𝑘
      StDiff = var_steps_diff(Labels, Steps, NegLabels, NegSteps),
      % ∀ ℓ ∈ L . P(ℓ)' \ N(ℓ)'
      {_, LsDiff, _} = ty_map:b_diff(P, N),

      StepConstraints  = [?F(ty_rec:normalize(TyRef, Fixed, M)) || _ := TyRef <- StDiff],
      LabelConstraints = [
        begin
          X = ?F(elim_lbl_conflict(ty_rec:normalize(TyRef, Fixed, M), A)),
          Y = ?F(elim_lbl_conflict(Norm(map(Labels#{AL => TyRef}, Steps), Ns), A)),
          ?F(constraint_set:join(X, Y))
        end
        || AL = {A, _} := TyRef <- LsDiff
      ],
      Constraints = lazy_meet([KeyC1, KeyC2 | StepConstraints ++ LabelConstraints]),
      constraint_set:join(Constraints, ?F(Norm(P, Ns)))
                      end.

var_steps_diff(Labels, Steps, NegLabels, NegSteps) ->
  Empty = ty_rec:empty(),
  VarValues1 = [Ty || {A, {Tag, _}} := Ty <- Labels, optional == A andalso var_key == Tag],
  VarValues2 = [Ty || {A, {Tag, _}} := Ty <- NegLabels, optional == A andalso var_key == Tag],
  #{S => begin
           #{S := T2} = NegSteps,
           T22 = u([T2 | VarValues2]),
           case T22 of
             _ when T22 == Empty -> T1;
             _ -> ty_rec:diff(u([T1 | VarValues1]), T22)
           end
         end
    || S := T1 <- Steps}.

%% Set upper bound for var labels in Map
constrain_key_vars(Map = {_, Labels, _}, Fixed, M) ->
  UndefinedKeys = ty_rec:diff(ty_map:key_domain(), ty_map:key_domain(Map, false)),
  lazy_meet(
    [case A of
       optional ->
         Upper = ty_rec:diff(TyVar, UndefinedKeys),
         ?F(ty_rec:normalize(Upper, Fixed, M));
       mandatory ->
         LabelKeys = u([TyRef || {_, {T, TyRef}} := _ <- Labels, var_key =/= T]),
         Upper = ty_rec:diff(TyVar, ty_rec:negate(LabelKeys)),
         ?F(ty_rec:normalize(Upper, Fixed, M))
     end
      || {A, {Tag, TyVar}} := _ <- Labels, var_key == Tag]
  ).

%% Set lower bound for var labels in Map1 with respect to Map2 and vice versa
constrain_key_vars(TyMap1, TyMap2, Fixed, M) ->
  DefinedKeys1 = ty_map:key_domain(TyMap1, true),
  DefinedKeys2 = ty_map:key_domain(TyMap2, true),
  Constrain = fun({_, Labels1, _}, {_, Labels2, _}, Flag) ->
    lazy_meet(
    [case A of
       optional ->
         Lower = case Flag of 1 -> ty_rec:diff(TyVar, DefinedKeys2); 2 -> ty_rec:diff(DefinedKeys1, TyVar) end,
         ?F(ty_rec:normalize(Lower, Fixed, M));
       mandatory ->
         case [TyRef || {AA, {_, TyRef}} := _ <- Labels2, mandatory == AA] of
           [] when Flag == 1 -> ?F([[]]); % case: no mandatory keys in neg map
           [] when Flag == 2 -> ?F([]); % case: no mandatory keys in pos map
           X ->
             LabelKeys = u(X),
             Lower = ty_rec:diff(LabelKeys, TyVar),
             Upper = ty_rec:diff(TyVar, LabelKeys),
             ?F(constraint_set:meet(
               ?F(ty_rec:normalize(Lower, Fixed, M)),
               ?F(ty_rec:normalize(Upper, Fixed, M))
             ))
         end
     end
      || {A, {Tag, TyVar}} := _ <- Labels1, var_key == Tag]
    )
              end,
  _Constrain_Map1_With_Map2 = C1 = Constrain(TyMap1, TyMap2, 1),
  _Constrain_Map2_With_Map1 = C2 = Constrain(TyMap2, TyMap1, 2),
  ?F(constraint_set:meet(C1, C2)).

elim_lbl_conflict(_Constraints = C, _Association = A) ->
  case {C, A} of
    {[[]], ?OPT} -> []; % !must! be mandatory
    {[], ?OPT} -> [[]]; % ⊥ exists as solution
    _ -> C
  end.

lazy_meet(Cs) -> lists:foldr(fun(F, A) -> ?F(constraint_set:meet(F, A)) end, ?F([[]]), Cs).
u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, {_, Labels, Steps}, PositiveEdge, NegativeEdge}) ->
  TyRefsSteps = [T || _ := T <- Steps],
  TyRefsLabelKey = [T || {_, {_, T}} := _ <- Labels],
  TyRefsLabelValue = [T || _ := T <- Labels],

  [ty_rec:all_variables(T) || T <- TyRefsSteps ++ TyRefsLabelKey ++ TyRefsLabelValue]
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).
