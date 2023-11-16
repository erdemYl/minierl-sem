-module(relation_map).
-vsn({2,0,0}).

-define(OPT, optional).
-define(MAN, mandatory).

-export([equal/2, compare/2]).
-export([map/2, b_anymap/0, b_emptymap/0, pi_fields/1]).

-record(ty_map, {optional, mandatory}).

-type relation_map() :: { _, ty_map() }.
-type ty_map() :: #ty_map{ optional :: dnf_ty_tuple(), mandatory :: dnf_ty_function() }.

-type dnf_ty_tuple() :: term().
-type dnf_ty_function() :: term().

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

-spec map(dnf_ty_tuple(), dnf_ty_function()) -> relation_map().
map(DnfTuple, DnfFun) ->
  RelMap = #ty_map{ optional = DnfTuple, mandatory = DnfFun },
  {relation_map, RelMap}.

-spec b_anymap() -> relation_map().
b_anymap() ->
  RelMap = #ty_map{ optional = dnf_ty_tuple:any(), mandatory = dnf_ty_function:any() },
  {relation_map, RelMap}.

-spec b_emptymap() -> relation_map().
b_emptymap() ->
  RelMap = #ty_map{ optional = dnf_ty_tuple:empty(), mandatory = dnf_ty_function:empty() },
  {relation_map, RelMap}.

-spec pi_fields(relation_map()) -> {dnf_ty_tuple(), dnf_ty_function()}.
pi_fields(Map) ->
  {relation_map, #ty_map{ optional = DnfTuple, mandatory = DnfFun }} = Map,
  {DnfTuple, DnfFun}.