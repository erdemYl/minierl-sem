-module(var).
-vsn({1,0,0}).

% every variable is distinct from all other created variables

% creates a new variable with a descriptive name
-callback new(string()) -> term().
