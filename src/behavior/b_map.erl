-module(b_map).
-vsn({2,1,0}).

-export_type([labels/0, steps/0]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.

-type labels() :: #{ l() => ty_ref() }.
-type steps()  :: #{ key_tag() := ty_ref() }.


-type l() :: {key_tag(), ty_ref()}.
-type key_tag() :: atom_key | integer_key | tuple_key.


% any map behaviour
-callback b_any() -> ty_map().

-callback map(EmptyContained :: boolean(), labels(), steps()) -> ty_map().
-callback labels(ty_map()) -> labels().
-callback steps(ty_map()) -> steps().
-callback pi(l(), ty_map()) -> ty_ref().

