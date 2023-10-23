-module(ty_map).
-vsn({2,5,0}).

-define(OPT, optional).
-define(MAN, mandatory).

-behavior(eq).
-export([equal/2, compare/2, b_anymap/0, b_empty/0, pi_var/2, key_domain/0]).

-behavior(b_map).
-export([map/2, pi/2, key_domain/2, value_domain/1]).


compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

b_anymap() ->
  Labels = #{},
  Steps = #{atom_key => ty_rec:any(), integer_key => ty_rec:any(), tuple_key => ty_rec:any()},
  {ty_map, Labels, Steps}.
b_empty() ->
  {ty_map, #{}, #{}}.
map(Labels, Steps) ->
  {ty_map, Labels, Steps}.

pi(L = {Tag, _}, {_, Labels, Steps}) ->
  case Labels of
    #{{?OPT, L} := Ref} -> {?OPT, Ref};
    #{{?MAN, L} := Ref} -> {?MAN, Ref};
    #{} when var_key == Tag -> {?MAN, ty_rec:empty()};
    #{} -> #{Tag := Ref} = Steps, {?OPT, Ref}
  end.

pi_var({?OPT, {var_key, _}}, Map) ->
  value_domain(Map);
pi_var({?MAN, {var_key, _}}, Map = {_, Labels, _}) when #{} == Labels ->
  value_domain(Map);
pi_var({?MAN, {var_key, _}}, {_, Labels, _}) ->
  u([Ref || {A, _} := Ref <- Labels, ?MAN == A]);
pi_var(AL, {_, Labels, _}) ->
  case Labels of
    #{AL := Ref} -> Ref;
    #{} -> case AL of
             {?OPT, _} -> u([Ref || {A, {Tag, _}} := Ref <- Labels, var_key == Tag, ?OPT == A]);
             {?MAN, _} -> u([Ref || {_, {Tag, _}} := Ref <- Labels, var_key == Tag])
           end
  end.

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
  ++ [Ref || {_, {T, _}} := Ref <- Labels, var_key =/= T]).

u(Tys) ->
  lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).

step_ty(atom_key) -> ty_rec:atom();
step_ty(integer_key) -> ty_rec:interval();
step_ty(tuple_key) -> ty_rec:tuple().