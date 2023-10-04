-module(ty_map).
-vsn({2,1,0}).

-behavior(eq).
-export([equal/2, compare/2, b_any/0]).

-behavior(b_map).
-export([map/3, steps/1, labels/1, pi/2]).


compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

b_any() ->
  Labels = #{},
  Steps = #{atom_key => ty_rec:any(), integer_key => ty_rec:any(), tuple_key => ty_rec:any()},
  map(true, Labels, Steps).

map(EmptyContained, Labels, Steps) -> {ty_map, EmptyContained, Labels, Steps}.

steps({ty_map, _, _, Steps}) -> Steps.
labels({ty_map, _, Labels, _}) -> Labels.

pi(L = {Tag, _}, {ty_map, _, Labels, Steps}) ->
  case Labels of
    #{L := Ref} -> Ref;
    _ -> #{Tag := Ref} = Steps, Ref
  end.