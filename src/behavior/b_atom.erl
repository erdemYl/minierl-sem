-module(b_atom).
-vsn({1,2,0}).

-callback finite([atom()]) -> term().
-callback cofinite([atom()]) -> term().
