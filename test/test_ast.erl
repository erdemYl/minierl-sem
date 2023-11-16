-module(test_ast).

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


-type ty() ::
  ty_mu() | ty_union() | ty_intersection() | ty_negation()
  | ty_bottom() | ty_any()
  | ty_fun() | ty_tuple() | ty_var() | ty_base() | ty_map().

% polymorphic calculus with type variables
-type ty_var()     :: {var, ty_varname()}.
-type ty_varname() :: atom().

% recursive type
-type ty_mu()        :: {mu, ty_var(), ty()}.

-type ty_bottom() :: none.
-type ty_any() :: any.
-type ty_tuple()  :: {tuple, ty(), ty()}.
-type ty_fun()    :: {'fun', ty(), ty()}.
-type ty_map()    :: ty_map_struct() | ty_map_dict() | relation_map().


% maps
-type ty_map_struct()     :: {map_struct, [{ty_map_struct_key(), ty()}], IsOpen :: boolean()}.
-type ty_map_dict()       :: {map_dict, ty_map_dict_key(), ty()}.
-type ty_map_struct_key() :: ty_singleton() | {map_struct_key_tuple, [ty_map_struct_key()]}.
-type ty_map_dict_key()   :: integer_key | atom_key | tuple_key.

% relmap
-type relation_map() :: {map, [ty_tuple()], [ty_fun()]}.


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
  ty_rec:is_subtype(test_ast:norm(T1), test_ast:norm(T2)).

normalize(T, Fixed) ->
  FixedN = sets:from_list(lists:map(
    fun({var, Name}) -> maybe_new_variable(Name) end, sets:to_list(Fixed))),
  ty_rec:normalize(test_ast:norm(T), FixedN, sets:new()).

normalize(T1, T2, Fixed) ->
  FixedN = sets:from_list(lists:map(
    fun({var, Name}) -> maybe_new_variable(Name) end, sets:to_list(Fixed))),
  NT1 = test_ast:norm(T1),
  NT2 = ty_rec:negate(test_ast:norm(T2)),
  NT3 = ty_rec:intersect(NT1, NT2),
  ty_rec:normalize(NT3, FixedN, sets:new()).

b() -> atom.
b(Atom) -> {'atom', Atom}.

% type constructors
f(X, Y) -> {'fun', X, Y}.

v(VariableName) -> {var, VariableName}.

% type constructors
r() -> int.
r(X) -> {integer, X}.

t() -> tuple.
t(X, Y) -> {'tuple', X, Y}.

mu(Var, Ty) -> {mu, Var, Ty}.

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

% map type constructors
struct(Fields, Open) -> {map_struct, Fields, Open}.
dict(Step, V) -> {map_dict, Step, V}. % always open or: only given step is restricted
opt(X) -> u(X, none()). % optional value
stp(a) -> atom_key;
stp(i) -> integer_key;
stp(t) -> tuple_key.
mt(Xs) -> {map_struct_key_tuple, Xs}.
empty_step() -> #{stp(i) => none(), stp(a) => none(), stp(t) => none()}.
any_step() -> #{stp(i) => any(), stp(a) => any(), stp(t) => any()}.

% relation map constructor
relmap(Ts, Fs) -> {map, Ts, Fs}.

% ==================
% ast:ty() -> ty_rec:ty_ref()
% ==================
%
% Conversion of a type into a multi-BDD representation
%
% Type variables are represented as
% the variable intersected with each disjunct unions top-type
% ===============================

norm_substs([]) -> [];
norm_substs([Sub | Subs]) ->
  New = maps:from_list(lists:map(fun({K, V}) -> {var_of(K), norm(V)} end, maps:to_list(Sub))),

  [New | norm_substs(Subs)].

norm_css_basic([]) -> [];
norm_css_basic([Cs | Css]) ->
  [ norm_cs_basic(Cs) ] ++ norm_css_basic(Css).

norm_cs_basic([]) -> [];
norm_cs_basic([{S, T} | Cs]) -> [ {norm(S), norm(T)} ] ++ norm_cs_basic(Cs).

norm_css([]) -> constraint_set:set_of_constraint_sets([]);
norm_css([Cs | Css]) ->
  constraint_set:set_of_constraint_sets([
    norm_cs(Cs)
  ] ++ norm_css(Css)).

norm_cs([]) -> constraint_set:constraint_set([]);
norm_cs([{V, Ty1, Ty2} | Cs]) -> constraint_set:constraint_set([
  constraint_set:constraint(var_of(V), norm(Ty1), norm(Ty2))
] ++ norm_cs(Cs)).


norm(int) ->
  Int = dnf_var_int:any(),
  ty_rec:interval(Int);
norm(tuple) ->
  Tuple = dnf_var_ty_tuple:any(),
  ty_rec:tuple(Tuple);
norm(atom) ->
  Atom = dnf_var_ty_atom:any(),
  ty_rec:atom(Atom);
norm({'atom', Atom}) ->
  TyAtom = ty_atom:finite([Atom]),
  TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
  ty_rec:atom(TAtom);
norm({mu, Var, Ty}) ->
  % assumption: Var has a unique name in the whole Ty
  NewRef = ty_ref:new_ty_ref(),
  ty_ref:store_recursive_variable(Var, NewRef),
  TTy = norm(Ty),
  ty_ref:define_ty_ref(NewRef, ty_ref:load(TTy));
norm(Var = {var, Name}) ->
  case ty_ref:check_recursive_variable(Var) of
    % free variable
    miss ->
      TyVar = maybe_new_variable(Name),
      ty_rec:variable(TyVar);
    % bound recursive variable
    Ty -> Ty
  end;
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
norm({map, Ts, Fs}) ->
  Tuples = [dnf_ty_tuple:tuple(ty_tuple:tuple(norm(A), norm(B))) || {tuple, A, B} <- Ts],
  DnfTuple = lists:foldr(fun dnf_ty_tuple:union/2, dnf_ty_tuple:empty(), Tuples),

  Functions = [dnf_ty_function:function(ty_function:function(norm(A), norm(B))) || {'fun', A, B} <- Fs],
  DnfFun = lists:foldr(fun dnf_ty_function:intersect/2, dnf_ty_function:any(), Functions),

  T = dnf_var_relation_map:map(dnf_relation_map:map(relation_map:map(DnfTuple, DnfFun))),
  ty_rec:relmap(T);
norm({map_struct, Fields, IsOpen}) ->
  StMappings = norm_(case IsOpen of true -> any_step(); _ -> empty_step() end),
  LbMappings = #{
    begin
      % optional ~ Ty ∨ none
      % mandatory ~ Ty
      Assoc = case ValTy of {union, _Ty, none} -> optional; _ -> mandatory end,
      {Assoc, norm_(Lb)}
    end => norm(ValTy) || {Lb, ValTy} <- Fields},

  T = dnf_var_ty_map:map(dnf_ty_map:map(ty_map:map(LbMappings, StMappings))),
  ty_rec:map(T);
norm({map_dict, Step, ValTy}) ->
  LbMappings = #{},
  StMappings = (norm_(any_step()))#{Step := norm(ValTy)},  % dict always open ~ any step

  T = dnf_var_ty_map:map(dnf_ty_map:map(ty_map:map(LbMappings, StMappings))),
  ty_rec:map(T);
norm({map_struct_key_tuple, Tys}) ->
  [Ty1, Ty2 | TyRest] = [norm(T) || T <- lists:reverse(Tys)],
  Tuple = lists:foldl(fun(E, Acc) -> {tuple, E, Acc} end, {tuple, Ty2, Ty1}, TyRest),  % nested tuple
  norm(Tuple);
norm({integer, I}) ->
  Int = dnf_var_int:int(ty_interval:interval(I, I)),
  ty_rec:interval(Int);
norm(any) -> ty_rec:any();
norm(none) -> ty_rec:empty();
norm({union, A, B}) -> ty_rec:union(norm(A), norm(B));
norm({intersection, A, B}) -> ty_rec:intersect(norm(A), norm(B));
norm({negation, A}) -> ty_rec:negate(norm(A)).

norm_(L = {atom, _}) -> {atom_key, norm(L)};
norm_(L = {integer, _}) -> {integer_key, norm(L)};
norm_(L = {map_struct_key_tuple, _}) -> {tuple_key, norm(L)};
norm_(L = {var, _}) -> {var_key, norm(L)};
norm_(#{} = Steps) -> #{St => norm(Ty) || St := Ty <- Steps}.


var_of({var, Name}) -> maybe_new_variable(Name).

maybe_new_variable(Name) ->
  Object = ets:lookup(?VAR_ETS, Name),
  case Object of
    [] ->
      Var = ty_variable:new(Name),
      ets:insert(?VAR_ETS, {Name, Var}),
      Var;
    [{_, Variable}] -> Variable
  end.
