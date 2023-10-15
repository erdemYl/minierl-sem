-module(dnf_ty_map).
-vsn({2,4,0}).

-define(P, {bdd_bool, ty_map}).
-define(F(Z), fun() -> Z end).
-define(MRG(F, M1, M2), merge_with(fun(_, X, Y) -> F(X, Y) end, M1, M2)).
-define(Pi, fun({_, L}, Map) -> {_, Ref} = pi(L, Map), Ref end).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([is_any/1, eval/1, is_empty/1, empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([map/1, normalize/5, all_variables/1]).

-import(ty_map, [map/2, pi/2, pi_var/2]).
-import(maps, [values/1, is_key/2, merge_with/3, filtermap/2]).

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
  {_, Ls, St} = TyMap,
  NewSteps = ?MRG(fun ty_rec:intersect/2, St, PosSt),
  LsInt    = #{AL => ty_rec:intersect(TyRef, ?Pi(AL, PosTyMap)) || AL := TyRef <- Ls},
  PosLsInt = #{AL => ty_rec:intersect(TyRef, ?Pi(AL, TyMap)) || AL := TyRef <- PosLs},
  % can contain opposites
  RawMerge = maps:merge(LsInt, PosLsInt),
  % mandatory is there for all labels
  % optional is there if not the same label as mandatory present
   _Without_Opposite_Associations = NewLabels = maps:filter(fun({A, L}, _) ->
     case A of
       mandatory -> true;
       _ -> not is_key({mandatory, L}, RawMerge) end end, RawMerge),
  andalso_(
    ?F(traverse_dnf(Left, map(NewLabels, NewSteps), N, Phi)),
    ?F(traverse_dnf(Right, map(PosLs, PosSt), [TyMap | N], Phi))
  ).

andalso_(L, R) -> case L() of
    true -> R(); false -> false;
    [[]] -> R(); [] -> [];
    CSets -> constraint_set:merge_and_meet(CSets, R())
  end.


phi({_, Labels, Steps}, []) ->
  lists:all(fun ty_rec:is_empty/1, values(Labels))
  andalso #{} == Steps;
phi(P = {_, _, Steps}, [N]) ->
  {_, _, NegSteps} = N,
  {LsDiff, Conflict} = labels_diff(P, N),
  S = steps_diff(Steps, NegSteps),
  not Conflict andalso phi(map(LsDiff, S), []);

phi(P = {_, Labels, Steps}, [N | Ns]) ->
  {_, _, NegSteps} = N,
  % ∀ 𝑘 ∈ Steps . (def(P))𝑘 \ (def(N))𝑘
  #{atom_key := StepAtom, integer_key := StepInt, tuple_key := StepTuple} = ?MRG(fun ty_rec:diff/2, Steps, NegSteps),
  % ∀ 𝑘 . (def(P))𝑘 \ (def(N))𝑘 ~ 0
  case ty_rec:is_empty(StepAtom)
    andalso ty_rec:is_empty(StepInt)
    andalso ty_rec:is_empty(StepTuple)
  of
    true ->
      {LsDiff, Conflict} = labels_diff(P, N),
      Rest = [{AL, TyRef} || AL := TyRef <- LsDiff, not ty_rec:is_empty(TyRef)],
      not Conflict andalso
        (
          [] == Rest orelse
                  % ∀ ℓ ∈ Rest . Φ(P ∧ {ℓ : ¬N(ℓ)}, Ns)  -- important point to test
                  % with P = (Labels, Steps)
                  lists:all(
                    fun({AL, DiffTyRef}) ->
                      phi(map(Labels#{AL => DiffTyRef}, Steps), Ns) end, Rest)
        );
    false -> phi(P, Ns)
  end.

steps_diff(Steps, NegSteps) ->
  % empty steps discarded
  maps:filter(fun(S, TyRef1) ->
      #{S := TyRef2} = NegSteps,
      not ty_rec:is_empty(ty_rec:diff(TyRef1, TyRef2)) end, Steps).

labels_diff(TyMapPos = {_, Labels, _}, TyMapNeg = {_, NegLabels, _}) ->
  L1 = [L || {_, L} := _ <- Labels],
  L2 = [L || {_, L} := _ <- NegLabels],
  Ls = lists:uniq(L1 ++ L2),
  % labels l with A1 = optional, A2 = mandatory discarded
  % such associations cannot be empty
  LsDiff = #{
    {A1, L} => ty_rec:diff(ty_rec:union(TyRef1, VarPart1), ty_rec:union(TyRef2, VarPart2)) || L <- Ls,
    begin
      {A1, TyRef1} = pi(L, TyMapPos), VarPart1 = pi_var({A1, L}, TyMapPos),
      {A2, TyRef2} = pi(L, TyMapNeg), VarPart2 = pi_var({A2, L}, TyMapNeg),
      A1 == A2 orelse A2 == optional
    end
  },
  AssociationConflict = maps:size(LsDiff) < length(Ls),
  {LsDiff, AssociationConflict}.


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
        _ ->
          KeyC = constrain_key_vars(P, Fixed, M),
          C1 = [?F(ty_rec:normalize(TyRef, Fixed, M)) || _ := TyRef <- Steps],
          C2 = [?F(ty_rec:normalize(TyRef2, Fixed, M)) || _ := TyRef2 <- Labels],
          andalso_(KeyC, lazy_meet(C1 ++ C2))
      end;
    Norm(P = {_, Labels, Steps}, [N | Ns]) -> {_, NegLabels, NegSteps} = N,
      KeyC1 = constrain_key_vars(N, Fixed, M),
      KeyC2 = constrain_key_vars(P, N, Fixed, M),
      KeyC = ?F(andalso_(KeyC1, KeyC2)),

      % ∀ 𝑘 ∈ Steps . (def'(P))𝑘 \ (def'(N))𝑘
      StepsDiff = ?MRG(fun ty_rec:diff/2,
        var_steps_def(Labels, Steps),
        var_steps_def(NegLabels, NegSteps)
      ),
      CSteps = [?F(ty_rec:normalize(TyRef, Fixed, M)) || _ := TyRef <- StepsDiff],

      {LsDiff, Conflict} = labels_diff(P, N),
      case Conflict of
        true -> []; % unsatisfied
        _ ->
          CLabels = [
            ?F(constraint_set:join(
              ?F(ty_rec:normalize(TyRef, Fixed, M)),
              ?F(Norm(map(Labels#{AL => TyRef}, Steps), Ns)))) || AL := TyRef <- LsDiff
          ],
          constraint_set:join(
            ?F(andalso_(KeyC, lazy_meet(CSteps ++ CLabels))),
            ?F(Norm(P, Ns))
          )
      end
                      end.

var_steps_def(Labels, Steps) -> Empty = ty_rec:empty(),
  #{S => case TyRef == Empty of
           true -> u([Ty || {A, {Tag, _}} := Ty <- Labels, optional == A andalso var_key == Tag]);
           false -> TyRef
         end
    || S := TyRef <- Steps}.


%% Set upper bound for var labels in Map
constrain_key_vars(Map = {_, Labels, _}, Fixed, M) ->
  UndefinedKeys = ty_rec:diff(ty_map:key_domain(), ty_map:key_domain(Map)),
  lazy_meet(
    [case A of
       optional ->
         Upper = ty_rec:diff(TyVar, UndefinedKeys),
         ?F(ty_rec:normalize(Upper, Fixed, M));
       _ ->
         LabelKeys = u([TyRef || {_, {T, TyRef}} := _ <- Labels, var_key =/= T]),
         Upper = ty_rec:diff(TyVar, ty_rec:negate(LabelKeys)),
         ?F(ty_rec:normalize(Upper, Fixed, M))
     end
      || {A, {Tag, TyVar}} := _ <- Labels, var_key == Tag]
  ).

%% Set lower bound for var labels in NegMap with respect to PosMap
constrain_key_vars(TyMapPos = {_, Labels, _}, _TyMapNeg = {_, NegLabels, _}, Fixed, M) ->
  DefinedKeys = ty_map:key_domain(TyMapPos),
  lazy_meet(
    [case Assoc of
       optional ->
         Lower = ty_rec:diff(DefinedKeys, NegTyVar),
         ?F(ty_rec:normalize(Lower, Fixed, M));
       _ ->
         LabelKeys = u([TyRef || {A, {T, TyRef}} := _ <- Labels, mandatory == A andalso var_key =/= T]),
         case LabelKeys == ty_rec:empty() of
           true -> ?F([]);
           false ->
             Lower = ty_rec:diff(LabelKeys, NegTyVar),
             Upper = ty_rec:diff(NegTyVar, LabelKeys),
             ?F(andalso_(
               ?F(ty_rec:normalize(Lower, Fixed, M)),
               ?F(ty_rec:normalize(Upper, Fixed, M))))
         end
     end
      || {Assoc, {Tag, NegTyVar}} := _ <- NegLabels, var_key == Tag]
  ).

lazy_meet(Cs) -> lists:foldr(fun(F, A) -> ?F(constraint_set:meet(F, A)) end, ?F([[]]), Cs).
u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, {_, Labels, Steps}, PositiveEdge, NegativeEdge}) ->
  TyRefsSteps = [T || _ := T <- Steps],
  VarLabels = [T || {_, {Tag, T}} := _ <- Labels, var_key == Tag],
  TyRefsLabelValue = [T || _ := T <- Labels],

  VarLabels ++ [ty_rec:all_variables(T) || T <- TyRefsSteps ++ TyRefsLabelValue]
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).
