-module(ty_tuple).
-vsn({1,0,0}).

%% 2-tuple representation

-behavior(eq).
-export([compare/2, equal/2]).

-behavior(b_tuple).
-export([tuple/2]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

tuple(Ref1, Ref2) -> {ty_tuple, Ref1, Ref2}.



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    % (int, int)
    TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
    TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),

    _Ty_Tuple = ty_tuple:tuple(TIa, TIb),

    ok.

-endif.

