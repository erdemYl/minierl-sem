-module(ty_ref).
-vsn({1,2,0}).

-export([any/0, store/1, load/1, new_ty_ref/0, define_ty_ref/2, is_empty_cached/1, store_is_empty_cached/2]).

-on_load(setup_ets/0).
-define(TY_UTIL, ty_counter).        % counter store
-define(TY_MEMORY, ty_mem).          % id -> ty
-define(TY_UNIQUE_TABLE, ty_unique). % ty -> id

-define(EMPTY_MEMO, memoize_ty_ets).        % ty_ref -> true
-define(EMPTY_CACHE, is_empty_memoize_ets). % ty_rec -> true/false

-spec setup_ets() -> ok.
setup_ets() ->
  spawn(fun() ->
    % spawns a new process that is the owner of the variable id ETS table
    lists:foreach(fun(Tab) -> ets:new(Tab, [public, named_table]) end, [?TY_UNIQUE_TABLE, ?TY_MEMORY, ?TY_UTIL, ?EMPTY_MEMO, ?EMPTY_CACHE]),
    ets:insert(?TY_UTIL, {ty_number, 0}),

    % define ANY node once
    ok = define_any(),

    % memoize ANY as not empty
    {ty_ref, AnyId} = ty_rec:any(),
    ets:insert(?EMPTY_CACHE, {AnyId, false}),

    % memoize EMPTY as empty
    {ty_ref, EmptyId} = ty_rec:empty(),
    ets:insert(?EMPTY_CACHE, {EmptyId, true}),

    receive _ -> ok end
        end),
  ok.

any() -> {ty_ref, 0}.

define_any() ->
  Any = {ty_ref, 0},

  % create tuple top (co-inductive)
  TupleAny = ty_tuple:tuple(Any, Any),
  DnfTupleAny = dnf_ty_tuple:tuple(TupleAny),
  DnfVarTupleAny = dnf_var_ty_tuple:tuple(DnfTupleAny),

  % create function top (co-inductive)
  % TODO 0 -> t is empty for every t;
  % does it make any difference to set t to something else other than empty or any?
  FunctionAny = ty_function:function(ty_rec:empty(), ty_rec:empty()),
  DnfFunctionAny = dnf_ty_function:function(FunctionAny),
  DnfVarFunctionAny = dnf_var_ty_function:function(DnfFunctionAny),

  % create interval top
  DnfVarIntervalAny = dnf_var_int:any(),

  % create atom top
  DnfVarAtomAny = dnf_var_ty_atom:any(),

  % union
  Ty1   = ty_rec:interval(DnfVarIntervalAny),
  Ty2   = ty_rec:tuple(DnfVarTupleAny),
  Ty3   = ty_rec:atom(DnfVarAtomAny),
  Ty4   = ty_rec:function(DnfVarFunctionAny),

  U1 = ty_rec:union(Ty1, Ty2),
  U2 = ty_rec:union(U1, Ty3),
  U = ty_rec:union(U2, Ty4),

  % define
  ty_ref:define_ty_ref(Any, ty_ref:load(U)),

  ok.

next_ty_id() ->
	ets:update_counter(?TY_MEMORY, ty_number, {2, 1}).

new_ty_ref() ->
  {ty_ref, next_ty_id()}.

define_ty_ref({ty_ref, Id}, Ty) ->
  ets:insert(?TY_UNIQUE_TABLE, {Ty, Id}),
  ets:insert(?TY_MEMORY, {Id, Ty}),
  {ty_ref, Id}.

load({ty_ref, Id}) ->
  Object = ets:lookup(?TY_MEMORY, Id),
%%  io:format(user, "LOOKUP ~p -> ~p ~n", [Id, Object]),
  case Object of
    [] ->
      erlang:error({type_reference_not_in_memory, Id});
    [{Id, Ty}] ->
      Ty
  end;
load(Ty) -> erlang:error({unknown_load_ty_ref, Ty}).

store(Ty) ->
  Object = ets:lookup(?TY_UNIQUE_TABLE, Ty),
  case Object of
    [] ->
      Id = ets:update_counter(?TY_UTIL, ty_number, {2, 1}),
      io:format(user, "Store: ~p :=~n~p~n", [Id, Ty]),
      ets:insert(?TY_UNIQUE_TABLE, {Ty, Id}),
      ets:insert(?TY_MEMORY, {Id, Ty}),
      {ty_ref, Id};
    [{_, Id}] ->
%%      io:format(user, "Cache hit!~n", []),
      {ty_ref, Id}
  end.


is_empty_cached({ty_ref, Id}) ->
  Object = ets:lookup(?EMPTY_CACHE, Id),
  case Object of
    [] -> miss;
    [{_, Result}] -> Result
  end.

store_is_empty_cached({ty_ref, Id}, Result) ->
  ets:insert(?EMPTY_CACHE, {Id, Result}),
  Result.
