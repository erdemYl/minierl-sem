-module(ty_map).
-vsn({2,6,0}).

-define(OPT, optional).
-define(MAN, mandatory).
-define(A, fun(A, ?OPT) -> ?MAN; (A, _) -> A end).
-define(MRG(F, M1, M2), maps:merge_with(fun(_, X, Y) -> F(X, Y) end, M1, M2)).

-define(PI, fun(X, Y, M) ->
  {_, T1} = pi(Y, M),
  T2 = pi_var(X, M),
  u([T1, T2])
  end
).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(b_map).
-export([map/2, b_anymap/0, b_empty/0, b_intersect/2, b_diff/2, pi/2, pi_var/2, pi_tag/2, key_domain/0, key_domain/2, value_domain/1]).


compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

map(Labels, Steps) ->
  {ty_map, Labels, Steps}.
b_anymap() ->
  Labels = #{},
  Steps = #{atom_key => ty_rec:any(), integer_key => ty_rec:any(), tuple_key => ty_rec:any()},
  {ty_map, Labels, Steps}.
b_empty() ->
  {ty_map, #{}, #{}}.

b_intersect(Map1, Map2) ->
  {_, Ls1, St1} = Map1,
  {_, Ls2, St2} = Map2,
  StInt = ?MRG(fun ty_rec:intersect/2, St1, St2),
  LsInt1 = #{AL => ty_rec:intersect(Ref, ?PI(AL, L, Map2)) || AL = {_, L} := Ref <- Ls1},
  LsInt2 = #{AL => ty_rec:intersect(Ref, ?PI(AL, L, Map1)) || AL = {_, L} := Ref <- Ls2},
  % can contain opposites
  RawMerge = maps:merge(LsInt1, LsInt2),
  % mandatory is there for all labels
  % optional is there if not the same label as mandatory present
  _Without_Opposite_Associations = LsInt = maps:filter(fun({A, L}, _) ->
    case A of
      mandatory -> true;
      optional -> not is_map_key({mandatory, L}, RawMerge)
    end
                                                       end, RawMerge),
  map(LsInt, StInt).

b_diff(Map1, Map2) ->
  {_, Ls1, St1} = Map1,
  {_, Ls2, St2} = Map2,
  StDiff = ?MRG(fun ty_rec:diff/2, St1, St2),
  LsDiff1 = #{begin
                {A2, _} = pi(L, Map2),
                case Tag of
                  var_key -> {?MAN, L}; % for normalization
                  _       -> {?A(A1, A2), L} end
              end
    => ty_rec:diff(
      ?PI(AL, L, Map1),
      ?PI(AL, L, Map2)) || AL = {A1, L = {Tag, _}} <- maps:keys(Ls1)
  },
  LsDiff2 = #{begin
                {A1, _} = pi(L, Map1),
                case Tag of
                  var_key -> {?MAN, L}; % for normalization
                  _       -> {?A(A1, A2), L} end
              end
    => ty_rec:diff(
      ?PI(AL, L, Map1),
      ?PI(AL, L, Map2)) || AL = {A2, L = {Tag, _}} <- maps:keys(Ls2)
  },
  LsDiff = maps:merge(LsDiff1, LsDiff2),
  map(LsDiff, StDiff).


pi(L = {Tag, _}, {_, Labels, Steps}) ->
  case Labels of
    #{{?OPT, L} := Ref} -> {?OPT, Ref};
    #{{?MAN, L} := Ref} -> {?MAN, Ref};
    #{} when var_key == Tag -> {?MAN, ty_rec:empty()};
    #{} -> #{Tag := Ref} = Steps, {?OPT, Ref}
  end.

pi_var({?OPT, {var_key, _}}, Map) ->
  value_domain(Map);
pi_var({?MAN, {var_key, _}}, Map = {_, Labels, _}) ->
  case [Ref || {A, _} := Ref <- Labels, ?MAN == A] of
    [] -> value_domain(Map);
    X -> u(X)
  end;
pi_var(AL, {_, Labels, _}) ->
  case Labels of
    #{AL := Ref} -> Ref;
    #{} -> case AL of
             {?OPT, _} -> u([Ref || {A, {Tag, _}} := Ref <- Labels, var_key == Tag, ?OPT == A]);
             {?MAN, _} -> u([Ref || {_, {Tag, _}} := Ref <- Labels, var_key == Tag])
           end
  end.

pi_tag(Tag, {_, Labels, Steps}) ->
  #{Tag := Ref} = Steps,
  Ls = maps:filter(fun({_, {T, _}}, _) -> T == Tag end, Labels),
  u([Ref | maps:values(Ls)]).

key_domain() ->
  u([ty_rec:interval(), ty_rec:atom(), ty_rec:tuple()]).

key_domain({_, Labels, Steps}, WithVariables) ->
  StepKeys = [step_ty(S) || S := Ref <- Steps, Ref =/= ty_rec:empty()],
  LabelKeys = case WithVariables of
                true ->  [Ref || {_, {_, Ref}} := _ <- Labels];
                false -> [Ref || {_, {Tag, Ref}} := _ <- Labels, var_key =/= Tag]
              end,
  u(StepKeys ++ LabelKeys).

value_domain({_, Labels, Steps}) ->
  u([Ref || _ := Ref <- Steps]
  ++ [Ref || _ := Ref <- Labels]).

u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
step_ty(atom_key) -> ty_rec:atom();
step_ty(integer_key) -> ty_rec:interval();
step_ty(tuple_key) -> ty_rec:tuple().