-module(b_map).
-vsn({2,1,0}).

%% Interpretation: quasi KΩ-step functions
%% Restricted key domain abstraction: key types can be type variables, but cannot be container types like [A].

-export_type([labels/0, steps/0]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.

-type labels() :: #{al() => ty_ref()}.
-type steps()  :: #{key_tag() := ty_ref()}.

-type al() :: {assoc(), l()}.
-type l() :: {key_tag(), ty_ref()}.

-type assoc() :: optional | mandatory.
-type key_tag() :: integer_key | atom_key | tuple_key.


-callback map(X, steps()) -> ty_map() when
  X :: #{al() | Y => ty_ref()},
  Y :: {assoc(), {var_key, ty_ref()}}.

-callback anymap() -> ty_map().

-callback pi(l(), ty_map()) -> {assoc(), ty_ref()}.
-callback intersect(ty_map(), ty_map()) -> ty_map().

-callback diff_labels(ty_map(), ty_map()) -> labels().
-callback diff_steps(ty_map(), ty_map()) -> steps().
-callback diff_w1(ty_map(), ty_map()) -> ty_ref().

-callback key_variable_suite(ty_map()) -> {O1::ty_ref(), O2::ty_ref(), ManKeyVarUnion::ty_ref(), OptKeyVarUnion::ty_ref()}.