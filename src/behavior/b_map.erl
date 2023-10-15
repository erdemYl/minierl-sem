-module(b_map).
-vsn({2,2,1}).

-export_type([labels/0, steps/0]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.

-type labels() :: #{ {assoc(), l() | l_var()} => ty_ref() }.
-type steps()  :: #{ key_tag() := ty_ref() }.

-type l()     :: {key_tag(), ty_ref()}.
-type l_var() :: {var_key, ty_ref()}.

-type key_tag() :: atom_key | integer_key | tuple_key.
-type assoc()   :: optional | mandatory.


% any map behaviour
-callback b_anymap() -> ty_map().
% 0 type behaviour embedded in map structure (not the empty map!)
-callback b_empty() -> ty_map().

-callback map(labels(), steps()) -> ty_map().

% TODO explain
% projects a label, without variable context
% association not used while projecting
-callback pi(l() | l_var(), ty_map()) -> {assoc(), ty_ref()}.

% TODO explain
% projects a label, with variable context
% association used while projecting
-callback pi_var({assoc(), l() | l_var()}, ty_map()) -> ty_ref().

% int() | atom() | tuple()
-callback key_domain() -> ty_ref().
% union of all key types
-callback key_domain(ty_map()) -> ty_ref().
% union of all value types
-callback value_domain(ty_map()) -> ty_ref().
