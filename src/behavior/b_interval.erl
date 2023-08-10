-module(b_interval).
-vsn({1,0,0}).

-callback interval(integer() | '*', integer() | '*') -> term().
-callback cointerval(integer() | '*', integer() | '*') -> term().

