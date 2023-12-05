-module(relation_map).
-vsn({2,0,0}).

-define(OPT, optional).
-define(MAN, mandatory).

-export([equal/2, compare/2]).
-export([map/2, empty/0, anymap/0, emptymap/0, intersect/2, pi_fields/1]).

-record(relmap, {optional :: relation(), mandatory :: overloaded_function()}).

-type relation() :: dnf_ty_tuple().
-type overloaded_function() :: dnf_ty_function().

-type relation_map() :: #relmap{}.
-type dnf_ty_tuple() :: term().
-type dnf_ty_function() :: term().

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.
equal(P1, P2) -> compare(P1, P2) =:= 0.

-spec map(relation(), overloaded_function()) -> relation_map().
map(DnfTuple, DnfFun) ->
  #relmap{ optional = DnfTuple, mandatory = DnfFun }.

-spec empty() -> relation_map().
empty() ->
  map(dnf_ty_tuple:empty(), dnf_ty_function:empty()).

-spec anymap() -> relation_map().
anymap() ->
  map(dnf_ty_tuple:any(), dnf_ty_function:any()).

-spec emptymap() -> relation_map().
emptymap() ->
  map(dnf_ty_tuple:empty(), dnf_ty_function:any()).

-spec intersect(relation_map(), relation_map()) -> relation_map().
intersect(Map1, Map2) ->
  {DnfTuple1, DnfFun1} = pi_fields(Map1),
  {DnfTuple2, DnfFun2} = pi_fields(Map2),
  map(dnf_ty_tuple:intersect(DnfTuple1, DnfTuple2), dnf_ty_function:intersect(DnfFun1, DnfFun2)).

-spec pi_fields(relation_map()) -> {relation(), overloaded_function()}.
pi_fields(Map) ->
  #relmap{ optional = DnfTuple, mandatory = DnfFun } = Map,
  {DnfTuple, DnfFun}.