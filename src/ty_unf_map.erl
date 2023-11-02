-module(ty_unf_map).
-vsn({2,0,0}).

-define(OPT, optional).
-define(MAN, mandatory).

%% type operators
-export([struct_selection/2, map_selection/2, delete/2, update/3, concat/2]).

%% usual operations
-export([map/1, empty/0, any/0, union/2, intersect/2, diff/2]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.
-type ty_unf_map() :: [ty_map()].

-spec map(ty_map()) -> ty_unf_map().
map(TyMap) -> [TyMap].

-spec struct_selection(b_map:l(), ty_unf_map()) -> {b_map:assoc(), ty_ref()}.
struct_selection(L, U) ->
  {Associations, Projections} = lists:unzip([ty_map:pi(L, X) || X <- U]),
  Opt = fun(?OPT) -> true; (?MAN) -> false end,
  case lists:any(Opt, Associations) of
    true -> {?OPT, u(Projections)};
    false -> {?MAN, u(Projections)}
  end.

-spec map_selection(ty_ref(), ty_unf_map()) -> {b_map:assoc(), ty_ref()}.
map_selection(Ty, U) ->
  {DnfAtom, DnfInt, DnfTuple, _, _} = ty_rec:pi_all(Ty),
  EA = dnf_var_ty_atom:is_empty(DnfAtom),
  EI = dnf_var_int:is_empty(DnfInt),
  ET = dnf_var_ty_tuple:is_empty(DnfTuple),
  AtomProj = case EA of false -> [ty_map:pi_tag(atom_key, X) || X <- U]; true -> [] end,
  IntProj = case EI of false -> [ty_map:pi_tag(integer_key, X) || X <- U]; true -> [] end,
  TupleProj = case ET of false -> [ty_map:pi_tag(tuple_key, X) || X <- U]; true -> [] end,

  {?OPT, u(AtomProj ++ IntProj ++ TupleProj)}.


-spec delete(ty_ref(), ty_unf_map()) -> ty_unf_map().
delete(_, _) -> todo.

-spec update(ty_ref(), ty_ref(), ty_unf_map()) -> ty_unf_map().
update(_, _, _) -> todo.

-spec concat(ty_unf_map(), ty_unf_map()) -> ty_unf_map().
concat(_, _) -> todo.

empty() -> [].
any() -> [ty_map:b_anymap()].

union(U1, U2) -> U1 ++ U2.

intersect([], _) -> [];
intersect(_, []) -> [];
intersect([X | Xs] = U1, U2 = [Y | Ys]) ->
  {_, LsInt, _} = Z = ty_map:b_intersect(X, Y),
  case labels_empty(LsInt) of % steps always at least include ⊥, only labels could be empty
    true -> [];
    false -> [Z]
  end
  ++ intersect(U1, Ys) ++ intersect(Xs, U2).

diff([], _) -> [];
diff(U, []) -> U;
diff([X | Xs] = U1, U2 = [Y | Ys]) ->
  {_, LsX, StX} = X,
  {_, LsDiff, StDiff} = ty_map:b_diff(X, Y),
  L = ty_map:map(LsX, StDiff),
  R = [ty_map:map(LsX#{AL => TyRef}, StX) || AL := TyRef <- LsDiff, not field_empty(AL, TyRef)],
  case steps_empty(StDiff) of % steps could be empty s.t. they don't include ⊥
    true -> R;
    false -> [L | R]
  end
  ++ diff(U1, Ys) ++ diff(Xs, U2).

labels_empty(Ls) ->
  lists:max([field_empty(AL, TyRef) || AL := TyRef <- Ls], false).
steps_empty(St) ->
  lists:all(fun ty_rec:is_empty/1, maps:values(St)).
field_empty({A, _L}, TyRef) ->
  ?MAN == A andalso ty_rec:is_empty(TyRef).
u(Tys) ->
  lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).


