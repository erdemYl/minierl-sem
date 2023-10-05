-module(dnf_ty_map).
-vsn({2,2,0}).

-define(P, {bdd_bool, ty_map}).
-define(Get, fun (X) -> fun (#{X := Y}) -> Y end end).
-define(Pi, fun ({_, L}, Map) -> {_, Ref} = pi(L, Map), Ref end).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([is_any/1, eval/1, is_empty/1, empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([map/1, all_variables/1]).

-import(ty_map, [map/2, pi/2]).

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
is_empty({terminal, 1}, P, N) ->
  phi(P, N);
is_empty({node, TyMap, Left, Right}, PosTyMap = {_, PosLs, PosSt}, N) ->
  St = ty_map:steps(TyMap),
  Ls = ty_map:labels(TyMap),
  NewSteps = #{S => ty_rec:intersect(TyRef, (?Get(S))(PosSt))
    || S := TyRef <- St},
  LsInt = #{AL => ty_rec:intersect(TyRef, ?Pi(AL, PosTyMap))
    || AL := TyRef <- Ls},
  PosLsInt = #{AL => ty_rec:intersect(TyRef, ?Pi(AL, TyMap))
    || AL := TyRef <- PosLs},
  % can contain opposites
  RawMerge = maps:merge(LsInt, PosLsInt),
  % mandatory is there for all labels
  % optional is there if not the same label as mandatory present
   _Without_Opposite_Associations = NewLabels = maps:filter(
    fun({A, L}, _) ->
      case A of
        mandatory -> true; _ -> not maps:is_key({mandatory, L}, RawMerge) end end, RawMerge),

  is_empty(Left, map(NewLabels, NewSteps), N)
    andalso
    is_empty(Right, map(PosLs, PosSt), [TyMap | N]).


phi({_, Labels, Steps}, []) when Labels == #{} -> Steps == #{};
phi({_, Labels, Steps}, []) when Steps  == #{} -> lists:all(fun(Ty) -> ty_rec:is_empty(Ty) end, maps:values(Labels));
phi(_,                  []) -> false;
phi(P = {_, _, Steps}, [N]) ->
  {Ls1, Ls2, AssocConflict1, AssocConflict2} = optional_diff_labels(P, N),
  S = optional_diff_steps(Steps, ty_map:steps(N)),
  not AssocConflict1
    andalso not AssocConflict2 andalso phi(map(maps:merge(Ls1, Ls2), S), []);

phi(P = {_, Labels, Steps}, [N | Ns]) ->
  _NegLabels = ty_map:labels(N),
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
      {DiffForLs, DiffForNegLs, AssocConflictLs, AssocConflictNegLs} = optional_diff_labels(P, N),
      Rest = [{AL, TyRef} || AL := TyRef <- maps:merge(DiffForLs, DiffForNegLs), not ty_rec:is_empty(TyRef)],
      not AssocConflictLs andalso not AssocConflictNegLs andalso
        begin
          [] == Rest orelse
                  % ∀ ℓ ∈ Rest . Φ(R ∧ {ℓ : ¬N(ℓ)}, Ns)  -- important point to test
                  % with R = (Labels, Steps)
                  lists:all(
                    fun({AL, DiffTyRef}) ->
                      phi(map(Labels#{AL => DiffTyRef}, Steps), Ns) end, Rest)
        end
    ;
    false -> phi(P, Ns)
  end.


optional_diff_steps(Steps, NegSteps) ->
  % empty steps discarded
  #{S => TyRef || S := TyRef <- Steps,
    not
      ty_rec:is_empty(ty_rec:diff(TyRef, (?Get(S))(NegSteps)))}.


optional_diff_labels(TyMapPos = {_, Labels, _}, TyMapNeg = {_, NegLabels, _}) ->
  O = optional, M = mandatory,
  % eliminates opposites if necessary
  % opposite elimination here means: empty check failed
  LsDiff1 = #{AL => ty_rec:diff(TyRef1, TyRef2)
    || {A1, L} = AL := TyRef1 <- Labels, begin
                                           {A2, TyRef2} = pi(L, TyMapNeg),
                                           A1 /= O orelse A2 /= M end},
  LsDiff2 = #{AL => ty_rec:diff(TyRef2, TyRef1)
    || {A1, L} = AL := TyRef1 <- NegLabels, begin
                                              {A2, TyRef2} = pi(L, TyMapPos),
                                              A2 /= O orelse A1 /= M end},
  IsSmaller1 = maps:size(LsDiff1) < maps:size(Labels),
  IsSmaller2 = maps:size(LsDiff2) < maps:size(NegLabels),
  {LsDiff1, LsDiff2, IsSmaller1, IsSmaller2}.



all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Map, PositiveEdge, NegativeEdge}) ->
  TyRefsSteps = [T || _ := T <- ty_map:steps(Map)],
  TyRefsLabelKey = [T || {_, T} := _ <- ty_map:labels(Map)],
  TyRefsLabelValue = [T || _ := T <- ty_map:labels(Map)],

  [ty_rec:all_variables(T) || T <- TyRefsSteps ++ TyRefsLabelKey ++ TyRefsLabelValue]
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).
