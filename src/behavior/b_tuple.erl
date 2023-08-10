-module(b_tuple).
-vsn({1,0,0}).

-type ty_tuple() :: term().
-type ty_ref() :: {ty_ref, integer()}.

-callback tuple(ty_ref(), ty_ref()) -> ty_tuple().

