-module(ty_function).
-vsn({1,2,0}).

%% domain -> co-domain function representation

-behavior(eq).
-export([compare/2, equal/2]).

-behavior(b_function).
-export([function/2, domain/1, codomain/1]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

function(Ref1, Ref2) -> {ty_function, Ref1, Ref2}.

domain({ty_function, Ref, _}) -> Ref.
codomain({ty_function, _, Ref}) -> Ref.



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
    TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),

    % int -> int
    _TyFunction = ty_function:function(TIa, TIb),

    ok.

-endif.
