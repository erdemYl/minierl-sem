-module(ast).

% @doc This file defines the λ_erl AST.
% It is used to test the erlang types library.

-on_load(setup_ets/0).
-define(VAR_ETS, test_ast_norm_var_memo). % remember variable name -> variable ID to convert variables properly

-spec setup_ets() -> ok.
setup_ets() -> spawn(fun() -> ets:new(?VAR_ETS, [public, named_table]), receive _ -> ok end end), ok.

-compile(nowarn_export_all).
-compile(export_all).

% ================
% Types
% ================

% co-inductive interpretation of types allows recursive references
-type ty_ref() :: {type_ref, integer()}.

-type ty() ::
  ty_union() | ty_intersection() | ty_negation()
  | ty_bottom() | ty_any()
  | ty_fun() | ty_tuple() | ty_var() | ty_base().

% polymorphic calculus with type variables
-type ty_var()     :: {var, ty_varname()}.
-type ty_varname() :: atom().

-type ty_bottom() :: none.
-type ty_any() :: any.
-type ty_tuple()  :: {tuple, ty_ref(), ty_ref()}.
-type ty_fun()    :: {'fun', ty_ref(), ty_ref()}.

-type ty_union()        :: {union, ty(), ty()}.
-type ty_intersection() :: {intersection, ty(), ty()}.
-type ty_negation()     :: {negation, ty()}.

-type ty_base()      :: ty_singleton() | int | float | atom | pair | 'fun'.
-type ty_singleton() :: {atom, atom()} | {integer, integer()}.

% ================
% Expressions
% ================

% expression variables
-type exp() ::
  exp_var() | exp_constant() | exp_fun() | exp_app()  | exp_tuple()
| exp_case() | exp_letrec().


% constants
-type rep_atom() :: {'atom', atom()}.
-type rep_integer() :: {'integer', integer()}.
-type rep_float() :: {'float', float()}.
-type exp_constant() :: rep_atom() | rep_float() | rep_integer().

-type unique_tok() :: integer().
-type exp_var() :: {atom(), unique_tok()}.

-type exp_fun()   :: {'fun', exp_var(), exp()}.
-type exp_app()   :: {'app', exp(), exp()}.
-type exp_tuple() :: {'tuple', exp(), exp()}.

-type exp_case() :: {'case', exp(), [pattern_clause()]}.

-type pattern_clause() :: {pattern_clause, pat(), guard()}.
-type pat() :: exp_constant() | '_' | exp_var() | {pattern_tuple, pat(), pat()}.
-type guard() :: {is, ty_base(), exp_var()} | {guard(), 'and', guard()} | 'true' | oracle.

-type exp_letrec() :: {'letrec', [def_clause()], 'in', exp()}.
-type def_clause() :: {'def', exp_var(), ty_scheme(), exp_fun()} | {'def', exp_var(), exp_fun()}.
-type ty_scheme() :: {ty_scheme, [bounded_tyvar()], ty()}.
-type bounded_tyvar() :: {ty_varname(), ty()}.

subty(T1, T2) ->
  ty_rec:is_subtype(ast:norm(T1), ast:norm(T2)).


% type constructors
a() -> atom.
a(Atom) -> {atom, Atom}.

v(VariableName) -> {var, VariableName}.

% type constructors
r() -> int.
r(X) -> {integer, X}.

any() -> any.
none() -> none.

u([]) -> none();
u([X]) -> X;
u([X,Y | T]) -> {union, X, u([Y | T])}.

i([]) -> any();
i([X]) -> X;
i([X,Y | T]) -> {intersection, X, i([Y | T])}.

% ==================
% ast:ty() -> ty_rec:ty()
% ==================
%
% Conversion of a type into a multi-BDD representation
%
% Type variables are represented as
% the variable intersected with each disjunct unions top-type
% ===============================

% ty_base
norm(int) ->
  Int = dnf_var_int:any(),
  ty_rec:interval(Int);
%%norm({atom, Atom}) ->
%%  erlang:error("TODO").
%%  (empty())#ty{atoms = bdd_lazy:pos({bdd_atom, Atom})};
%%norm({singleton, IntOrChar}) ->
%%  % Char is subset of Int
%%  (empty())#ty{ints = bdd_lazy:pos({bdd_range, IntOrChar, IntOrChar})};
%%
%%% ty_bitstring % TODO
%%norm({binary, _, _}) -> erlang:error("Bitstrings not supported yet");
%%
%%norm({tuple_any}) -> (empty())#ty{prod = rep_map_any()};
%%norm({tuple, Components}) ->
%%  Normed = [norm(Ty) || Ty <- Components],
%%  Tuple = #{length(Components) => bdd_lazy:pos({bdd_tuple, Normed})},
%%  (empty())#ty{prod = {bdd_lazy:empty(), Tuple}};
%%
%%% funs
%%norm({fun_simple}) ->
%%  (empty())#ty{arrw = {bdd_lazy:any(), #{}}};
%%norm({fun_full, Components, Result}) ->
%%  Normed = [norm(Ty) || Ty <- Components],
%%  Function = #{length(Components) => bdd_lazy:pos({bdd_fun_full, Normed, norm(Result)})},
%%  (empty())#ty{arrw = {bdd_lazy:empty(), Function}};
%%
%%
% var
norm({var, A}) ->
  Var = maybe_new_variable(A),
  ty_rec:variable(Var);

%%
%%% ty_some_list
%%norm({list, Ty}) ->
%%  union(
%%    norm({improper_list, Ty, {empty_list}}),
%%    norm({empty_list})
%%  );
%%norm({nonempty_list, Ty}) -> norm({nonempty_improper_list, Ty, {empty_list}});
%%norm({nonempty_improper_list, Ty, Term}) -> diff(norm({list, Ty}), norm(Term));
%%norm({improper_list, Ty, Term}) ->
%%  (empty())#ty{ list = bdd_lazy:pos({bdd_list, norm(Ty), norm(Term)}) };
%%
%%norm({empty_list}) ->
%%  (empty())#ty{special = bdd_lazy:pos({bdd_spec, empty_list})};
%%norm({predef, T}) when T == pid; T == port; T == reference; T == float ->
%%  (empty())#ty{special = bdd_lazy:pos({bdd_spec, T})};
%%
%%% named
%%norm({named, _, Ref, Args}) ->
%%  V = {bdd_named, {Ref, Args}},
%%  (any())#ty{
%%    atoms = bdd_lazy:pos(V),
%%    ints = bdd_lazy:pos(V),
%%    special = bdd_lazy:pos(V),
%%    list = bdd_lazy:pos(V),
%%    prod = {bdd_lazy:pos(V), #{}},
%%    arrw = {bdd_lazy:pos(V), #{}}
%%  };
%%
%%% ty_predef_alias
%%norm({predef_alias, Alias}) ->
%%  Expanded = stdtypes:expand_predef_alias(Alias),
%%  norm(Expanded);
%%
%%% ty_predef
%%norm({predef, atom}) ->
%%  (empty())#ty{atoms = bdd_lazy:any()};
%%
%%norm({predef, any}) -> any();
%%norm({predef, none}) -> empty();
%%norm({predef, integer}) ->
%%  (empty())#ty{ints = bdd_lazy:pos({bdd_range, '*', '*'})};
%%
%%% ints
norm({integer, I}) ->
  Int = dnf_var_int:int(ty_interval:interval(I, I)),
  ty_rec:interval(Int);

norm(any) -> ty_rec:any();
norm(none) -> ty_rec:empty();

norm({union, A, B}) -> ty_rec:union(norm(A), norm(B));
norm({intersection, A, B}) -> ty_rec:intersect(norm(A), norm(B)).

%%norm({negation, Ty}) -> negate(norm(Ty));
%%
%%norm(T) ->
%%  logger:error("Norm not implemented for~n~p", [T]),
%%  erlang:error("Norm not implemented, see error log").


maybe_new_variable(Name) ->
  Object = ets:lookup(?VAR_ETS, Name),
  case Object of
    [] ->
      Var = ty_variable:new(Name),
      ets:insert(?VAR_ETS, {Name, Var}),
      Var;
    [{_, Variable}] -> Variable
  end.