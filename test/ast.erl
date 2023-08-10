-module(ast).

% @doc This file defines the λ_erl AST.
% It is used to test the erlang types library.

% ================
% Types
% ================

% co-inductive interpretation of types allows recursive references
-type ty_ref() :: {type_ref, integer()}.

-type ty() ::
  ty_union() | ty_intersection() | ty_negation()
  | ty_bottom() % any is a co-inductively defined recursive type, not a constant!
  | ty_fun() | ty_tuple() | ty_var() | ty_base().

% polymorphic calculus with type variables
-type ty_var()     :: {var, ty_varname()}.
-type ty_varname() :: atom().

-type ty_bottom() :: none.
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