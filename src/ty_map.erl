-module(ty_map).
-vsn({2,2,0}).

-behavior(eq).
-export([equal/2, compare/2, b_any/0]).

-behavior(b_map).
-export([map/2, steps/1, labels/1, pi/2]).


compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

b_any() ->
  Labels = #{},
  Steps = #{atom_key => ty_rec:any(), integer_key => ty_rec:any(), tuple_key => ty_rec:any()},
  map(Labels, Steps).

map(Labels, Steps) -> {ty_map, Labels, Steps}.
steps({ty_map, _, Steps}) -> Steps.
labels({ty_map, Labels, _}) -> Labels.

pi(L = {Tag, _}, {ty_map, Labels, Steps}) ->
  O = optional, M = mandatory,
  case Labels of
    #{{O, L} := Ref} -> {O, Ref};
    #{{M, L} := Ref} -> {M, Ref};
    _ -> #{Tag := Ref} = Steps, {O, Ref}
  end.