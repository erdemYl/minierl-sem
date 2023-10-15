-module(ty_map).
-vsn({2,4,0}).

-define(OPT, optional).
-define(MAN, mandatory).

-behavior(eq).
-export([equal/2, compare/2, b_anymap/0, b_empty/0, pi_var/2, key_domain/0]).

-behavior(b_map).
-export([map/2, pi/2, key_domain/1, value_domain/1]).


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

pi(L = {Tag, _}, {_, Labels, Steps}) -> O = ?OPT, M = ?MAN,
  case Labels of
    #{{O, L} := Ref} -> {O, Ref};
    #{{M, L} := Ref} -> {M, Ref};
    _ -> case Tag of
           var_key ->
             % pi(a, map) ~ 0
             {M, ty_rec:empty()};
           _ ->
             #{Tag := Ref} = Steps,
             {O, Ref}
         end
  end.

pi_var(AL = {?OPT, {var_key, _}}, Map = {_, Labels, _}) ->
  case Labels of
    #{AL := Ref} -> Ref;
    _ -> value_domain(Map)
  end;
pi_var({?MAN, {var_key, _}}, {_, Labels, _}) ->
    u([Ref || {A, _} := Ref <- Labels, ?MAN == A]);
pi_var({?OPT, _}, {_, Labels, _}) ->
  % association can be any
  u([Ref || {_, {T, _}} := Ref <- Labels, var_key == T]);
pi_var({?MAN, _}, {_, Labels, _}) ->
  % association only mandatory
  u([Ref || {A, {T, _}} := Ref <- Labels, var_key == T andalso ?MAN == A]).


key_domain() ->
  u([ty_rec:interval(), ty_rec:atom(), ty_rec:tuple()]).

key_domain({_, Labels, Steps}) ->
  Union = [step_ty(S) || S := Ref <- Steps, Ref =/= ty_rec:empty()],
  u(Union ++ [Ref || {_, {T, Ref}} := _ <- Labels, var_key =/= T]).

value_domain({_, Labels, Steps}) ->
  u([Ref || _ := Ref <- Steps]
  ++ [Ref || {_, {T, _}} := Ref <- Labels, var_key =/= T]).


u(Tys) ->
  lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).

step_ty(atom_key) -> ty_rec:atom();
step_ty(integer_key) -> ty_rec:interval();
step_ty(tuple_key) -> ty_rec:tuple().