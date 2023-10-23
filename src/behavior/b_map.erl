-module(b_map).
-vsn({2,2,2}).

-export_type([labels/0, steps/0]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.

-type labels() :: #{ al() => ty_ref() }.
-type steps()  :: #{ key_tag() := ty_ref() }.

-type al() :: {assoc(), l()}.
-type l()  :: {key_tag() | var_tag(), ty_ref()}.

-type key_tag() :: atom_key | integer_key | tuple_key.
-type var_tag() :: var_key.
-type assoc()   :: optional | mandatory.


% any map behaviour
-callback b_anymap() -> ty_map().
% 0 type behaviour embedded in map structure (not the empty map!)
-callback b_empty() -> ty_map().

-callback map(labels(), steps()) -> ty_map().

% TODO explain
% projects a label, without variable context
% association not used while projecting
-callback pi(l(), ty_map()) -> {assoc(), ty_ref()}.

% TODO explain
% projects a label, with variable context
% association used while projecting
-callback pi_var(al(), ty_map()) -> ty_ref().

% int() | atom() | tuple()
-callback key_domain() -> ty_ref().
% union of all key types
-callback key_domain(ty_map(), WithVariables :: boolean()) -> ty_ref().
% union of all value types
-callback value_domain(ty_map()) -> ty_ref().
