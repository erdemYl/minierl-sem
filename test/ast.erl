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

b(Atom) -> {'atom', Atom}.

% type constructors
f(X, Y) -> {'fun', X, Y}.

v(VariableName) -> {var, VariableName}.

% type constructors
r() -> int.
r(X) -> {integer, X}.

t(X, Y) -> {'tuple', X, Y}.


any() -> any.
none() -> none.

u(X, Y) -> {union, X, Y}.
u([]) -> none();
u([X]) -> X;
u([X,Y | T]) -> {union, X, u([Y | T])}.

i(X, Y) -> {intersection, X, Y}.
i([]) -> any();
i([X]) -> X;
i([X,Y | T]) -> {intersection, X, i([Y | T])}.

n(X) -> {negation, X}.

% ==================
% ast:ty() -> ty_rec:ty()
% ==================
%
% Conversion of a type into a multi-BDD representation
%
% Type variables are represented as
% the variable intersected with each disjunct unions top-type
% ===============================

norm(int) ->
  Int = dnf_var_int:any(),
  ty_rec:interval(Int);
norm({'atom', Atom}) ->
  TyAtom = ty_atom:finite([Atom]),
  TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
  ty_rec:atom(TAtom);
norm({var, A}) ->
  Var = maybe_new_variable(A),
  ty_rec:variable(Var);
norm({tuple, A, B}) ->
  TyA = norm(A),
  TyB = norm(B),

  T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(TyA, TyB))),
  ty_rec:tuple(T);
norm({'fun', A, B}) ->
  TyA = norm(A),
  TyB = norm(B),

  T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(TyA, TyB))),
  ty_rec:function(T);
norm({integer, I}) ->
  Int = dnf_var_int:int(ty_interval:interval(I, I)),
  ty_rec:interval(Int);
norm(any) -> ty_rec:any();
norm(none) -> ty_rec:empty();
norm({union, A, B}) -> ty_rec:union(norm(A), norm(B));
norm({intersection, A, B}) -> ty_rec:intersect(norm(A), norm(B));
norm({negation, A}) -> ty_rec:negate(norm(A)).


maybe_new_variable(Name) ->
  Object = ets:lookup(?VAR_ETS, Name),
  case Object of
    [] ->
      Var = ty_variable:new(Name),
      ets:insert(?VAR_ETS, {Name, Var}),
      Var;
    [{_, Variable}] -> Variable
  end.