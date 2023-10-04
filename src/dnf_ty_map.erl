-module(dnf_ty_map).
-vsn({2,1,4}).

-define(P, {bdd_bool, ty_map}).
-define(Get, fun(K) -> fun(#{K := V}) -> V end end).
% why not fun(K, #{K := V}) -> V end. ? --- because key variable K must be bound beforehand
% this is different than fun(K, {K, V}) -> V end.

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([is_any/1, eval/1, is_empty/1, empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([map/1, all_variables/1]).

-import(ty_map, [map/3, pi/2]).

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


is_empty(TyDnf) -> is_empty(
  TyDnf,
  ty_map:b_any(),
  _NegatedMaps = []
).

is_empty(0, _, _) -> true;
is_empty({terminal, 1}, {_, X, _, _} = P, N) ->
  not X andalso phi(P, N);
is_empty({node, TyMap, Left, Right}, PosTyMap = {_, X, PosLs, PosSt}, N) ->
  {_, Y, Ls, St} = TyMap,
  NewSteps = #{S => ty_rec:intersect(TyRef, (?Get(S))(PosSt))
    || S := TyRef <- St},
  LsInt = #{L => ty_rec:intersect(TyRef, pi(L, PosTyMap))
    || L := TyRef <- Ls},
  PosLsInt = #{L => ty_rec:intersect(TyRef, pi(L, TyMap))
    || L := TyRef <- PosLs},
  NewLabels = maps:merge(LsInt, PosLsInt),

  is_empty(Left, map(X and Y, NewLabels, NewSteps), N)
    andalso
    is_empty(Right, map(X and not Y, PosLs, PosSt), [TyMap | N]).


phi({_, _, Labels, Steps}, []) when Labels == #{} -> Steps == #{};
phi({_, _, Labels, Steps}, []) when Steps  == #{} -> #{} =/= #{a => a || _ := X <- Labels, ty_rec:is_empty(X)};
phi(_,                     []) -> false;
phi(P = {_, _, Labels, Steps}, [N]) ->
  S = optional_diff(Steps, ty_map:steps(N)),
  L1 = #{L => ty_rec:diff(TyRef, pi(L, N)) || L := TyRef <- Labels},
  L2 = #{L => ty_rec:diff(pi(L, P), TyRef) || L := TyRef <- ty_map:labels(N)},
  EmptyBypassed = map(false, maps:merge(L1, L2), S),
  phi(EmptyBypassed, []);

phi(P = {_, _, Labels, Steps}, [N | Ns]) ->
  NegLabels = ty_map:labels(N),
  NegSteps = ty_map:steps(N),

  % ∀ 𝑘 ∈ Steps . (def(R))𝑘 \ (def(N))𝑘
  #{atom_key := StepAtom,
    integer_key := StepInt,
    tuple_key := StepTuple} = #{S => ty_rec:diff(TyRef, (?Get(S))(NegSteps))
                                || S := TyRef <- Steps},
  % ∀ 𝑘 . (def(R))𝑘 \ (def(N))𝑘 ~ 0
  case ty_rec:is_empty(StepAtom)
    andalso ty_rec:is_empty(StepInt)
    andalso ty_rec:is_empty(StepTuple)
  of
    true ->
      LsDiff1 = #{L => ty_rec:diff(TyRef, pi(L, N)) || L := TyRef <- Labels},
      LsDiff2 = #{L => ty_rec:diff(pi(L, P), TyRef) || L := TyRef <- NegLabels},
      Rest = [{L, TyRef} || L := TyRef <- maps:merge(LsDiff1, LsDiff2), not ty_rec:is_empty(TyRef)],
      [] == Rest
        orelse (begin
                  % ∀ ℓ ∈ Rest . Φ(R ∧ {ℓ : ¬N(ℓ)}, Ns)  -- important point to test
                  % with R = (Labels, Steps)
                  lists:all(
                    fun({L, DiffTyRef}) ->
                      EmptyBypassed = map(false, Labels#{L => DiffTyRef}, Steps),
                      phi(EmptyBypassed, Ns) end, Rest)
                end)
    ;
    false -> phi(P, Ns)
  end.


optional_diff(Steps, NegSteps) ->
  % empty steps discarded
  #{S => TyRef || S := TyRef <- Steps,
    not
      ty_rec:is_empty(ty_rec:diff(TyRef, (?Get(S))(NegSteps)))}.


all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Map, PositiveEdge, NegativeEdge}) ->
  TyRefsSteps = [T || _ := T <- ty_map:steps(Map)],
  TyRefsLabelKey = [T || {_, T} := _ <- ty_map:labels(Map)],
  TyRefsLabelValue = [T || _ := T <- ty_map:labels(Map)],

  [ty_rec:all_variables(T) || T <- TyRefsSteps ++ TyRefsLabelKey ++ TyRefsLabelValue]
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).
