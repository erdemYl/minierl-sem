-module(normalize_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [norm_substs/1, norm/1, mu/2, n/1, b/0, b/1, f/2, t/0, t/2, i/2, i/1, u/2, u/1, r/1, r/0, struct/2, dict/2, opt/1, stp/1, relmap/2, rest/1, none/0, any/0, v/1, subty/2, normalize/3, normalize/2, var_of/1, norm_css/1]).

simple_empty_test() ->
  [[]] = normalize(v(alpha), any(), sets:new()),
  ok.

simple_normalize_atom_test() ->
  % satisfiable constraint: some_atom <: ANY_atom
  [[]] = normalize(b(some_atom), b(), sets:new()),

  % unsatisfiable constraint: ANY_atom <: some_atom
  [] = normalize(b(), b(some_atom), sets:new()),

  Alpha = v(alpha),
  Beta = v(beta),

  % simple variable constraints
  [] = normalize(Alpha, b(some_atom), sets:from_list([Alpha])),
  [] = normalize(Alpha, Beta, sets:from_list([Alpha, Beta])),
  [[]] = normalize(i(Alpha, b()), u(Beta, b()), sets:from_list([Alpha, Beta])),

  ok.

simple_atom_normalize_test() ->
  Alpha = v(alpha),

  [[{V, L, R}]] = normalize(i(Alpha, b()), sets:new()),
  true = ty_rec:is_empty(L),
  true = ty_rec:is_equivalent(R, norm(n(b()))),
  V = var_of(Alpha),

  ok.

var_ordering_atom_normalize_test() ->
  Alpha = v(alpha),
  Beta = v(beta),

  [[{V, L, R}]] = normalize(i([Beta, Alpha, b()]), sets:new()),
  true = ty_rec:is_empty(L),
  true = ty_rec:is_equivalent(R, norm(n(i(b(), Beta)))),
  V = var_of(Alpha),

  ok.

neg_var_atom_normalize_test() ->
  Alpha = v(alpha),
  Beta = v(beta),

  [[{V, L, R}]] = normalize(i([Beta, n(Alpha), b()]), sets:new()),
  true = ty_rec:is_equivalent(ty_rec:any(), R),
  true = ty_rec:is_equivalent(L, norm(i(b(), Beta))),
  V = var_of(Alpha),

  ok.

simple_normalize_interval_test() ->
  [[]] = normalize(r(1), r(), sets:new()),
  [] = normalize(r(), r(1), sets:new()),

  Alpha = v(alpha),
  Beta = v(beta),

  % simple variable constraints
  [] = normalize(Alpha, r(1), sets:from_list([Alpha])),
  [] = normalize(Alpha, Beta, sets:from_list([Alpha, Beta])),
  [[]] = normalize(i(Alpha, r()), u(Beta, r()), sets:from_list([Alpha, Beta])),

  ok.

simple_normalize_tuple_test() ->
  [] = normalize(i(t(r(), r()), n(t(b(), b()))), sets:new()),
  [[]] = normalize(i(t(r(), r()), n(t(r(), r()))), sets:new()),

  ok.

example_1_normalize_test() ->
  % α→Bool ≤ β→β
  Result = normalize(f(v(alpha), b(bool)), f(v(beta), v(beta)), sets:new()),

  % one valid solution (minimal)
  % { {(β≤0) (β≤α)}  {(bool≤β) (β≤α)} }
  Expected = norm_css([
    [{v(alpha), v(beta), any()}, {v(beta), none(), none()}],
    [{v(alpha), v(beta), any()}, {v(beta), b(bool), any()}]
  ]),

  % paper solution (also minimal!)
  % { {(β≤0)}        {(bool≤β) (β≤α)} }
  Expected2 = norm_css([
    [{v(beta), none(), none()}],
    [{v(alpha), v(beta), any()}, {v(beta), b(bool), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => none(), v(beta) => any()},
    #{v(alpha) => any(), v(beta) => b(bool)}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),
  true = set_of_constraint_sets:is_equivalent(Expected2, Result, TestSubstitutions),

  ok.


example_2_normalize_test() ->
  % (Int∨Bool → Int ≤ α → β)
  Result = normalize(f(u(r(), b(bool)), r()), f(v(alpha), v(beta)), sets:new()),

  % solution
  % { {α≤0} , {α≤Int∨Bool, Int≤β} }
  Expected = norm_css([
    [{v(alpha), none(), none()}],
    [{v(alpha), none(), u(r(), b(bool))}, {v(beta), r(), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => none(), v(beta) => none()},
    #{v(alpha) => none(), v(beta) => any()},
    #{v(alpha) => none(), v(beta) => r()},
    #{v(alpha) => r(), v(beta) => r()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.

example_meet_normalize_test() ->
  % α→Bool ≤ β→β
  Res1 = normalize(f(v(alpha), b(bool)), f(v(beta), v(beta)), sets:new()),
  % Int∨Bool → Int ≤ α → β
  Res2 = normalize(f(u(r(), b(bool)), r()), f(v(alpha), v(beta)), sets:new()),
  % meet
  Result = constraint_set:merge_and_meet(Res1, Res2),

  % expected minimal paper solution (2 & 3 constraint unsatisfiable)
  % { {α≤0, β≤0} {α≤Int∨Bool, Int≤β, β≤0} {Bool≤β, β≤α, α≤0} {α≤Int∨Bool, Int≤β, Bool≤β, β≤α} }
  Expected = norm_css([
    [{v(alpha), none(), none()}, {v(beta), none(), none()}],
    [{v(alpha), none(), u(r(), b(bool))}, {v(beta), r(), any()}, {v(beta), none(), none()}],
    [{v(alpha), none(), none()}, {v(alpha), v(beta), any()}, {v(beta), b(bool), any()}],
    [{v(alpha), none(), u(r(), b(bool))}, {v(alpha), v(beta), any()}, {v(beta), r(), any()}, {v(beta), b(bool), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => none(),  v(beta) => none()},
    #{v(alpha) => u(r(), b(bool)), v(beta) => u(r(), b(bool))}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.

% ====
% Map tests
% ====

simple_normalize1_map_test() ->
  % #{int() => int()}  ≤  #{a => β}
  M1 = i([
    dict(stp(i), r()),
    dict(stp(a), none()),
    dict(stp(t), none())
  ]),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Result = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), r(), KeyDomain}, {v(beta), r(), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => r(),  v(beta) => r()},
    #{v(alpha) => KeyDomain,  v(beta) => any()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
simple_normalize2_map_test() ->
  % #{int() => int(), atom() => atom()}  ≤  #{a => β}
  M1 = i([
    dict(stp(i), r()),
    dict(stp(a), b()),
    dict(stp(t), none())
  ]),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Result = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), u(r(), b()), KeyDomain}, {v(beta), u(r(), b()), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => u(r(), b()),  v(beta) => u(r(), b())},
    #{v(alpha) => KeyDomain,  v(beta) => u(r(), b())},
    #{v(alpha) => KeyDomain,  v(beta) => KeyDomain}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
simple_normalize3_map_test() ->
  % #{int() => int(), _ => any()}  ≤  #{a => β}
  M1 = dict(stp(i), r()),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Result = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), KeyDomain, KeyDomain}, {v(beta), any(), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => KeyDomain,  v(beta) => any()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
simple_normalize4_map_test() ->
  % #{int() => int(), _ => foo}  ≤  #{a => β}
  M1 = i([
    dict(stp(i), r()),
    dict(stp(a), b(foo)),
    dict(stp(t), b(foo))
  ]),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  KeyDomain = u([b(), r(), t()]),
  Result = normalize(M1, M2, sets:new()),

  Expected = norm_css([
    [{v(alpha), KeyDomain, KeyDomain}, {v(beta), u(r(), b(foo)), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => KeyDomain,  v(beta) => u(r(), b(foo))},
    #{v(alpha) => KeyDomain,  v(beta) => any()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
simple_normalize5_map_test() ->
  % #{input := int()}  ≤  #{a => β}
  M1 = struct([{b(input), r()}], false),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Result = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), b(input), KeyDomain}, {v(beta), r(), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => b(input),  v(beta) => r()},
    #{v(alpha) => b(input),  v(beta) => any()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
simple_normalize6_map_test() ->
  % #{input := int(), _ => any()}  ≤  #{a := β, _ => any()} | #{γ := δ, _ => any()}
  M1 = struct([{b(input), r()}], true),
  M2 = struct([{v(alpha), v(beta)}], true),
  M3 = struct([{v(gamma), v(delta)}], true),

  Res = normalize(M1, u(M2, M3), sets:new()),
  _Expected = norm_css([
    [{v(alpha), b(input), b(input)}, {v(beta), r(), any()}],
    [{v(gamma), b(input), b(input)}, {v(delta), r(), any()}]
    % and something
  ]),

  true = Res,

  ok.
simple_normalize7_map_test() ->
  % #{input := int(), _ => any()}  !≤  #{input := bool, a => β}
  M1 = struct([{b(input), r()}], true),
  M2 = struct([
    {b(input), b(bool)},
    {v(alpha), opt(v(beta))}], false),

  Result = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Result,

  ok.
simple_normalize8_map_test() ->
  % #{input := int(), _ => any()}  !≤  #{input := 1, a => β}
  M1 = struct([{b(input), r()}], true),
  M2 = struct([
    {b(input), r(1)},
    {v(alpha), opt(v(beta))}], false),

  Result = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Result,

  ok.
simple_normalize9_map_test() ->
  % #{input := int()}  !≤  #{input := 1, _ => any()}
  M1 = struct([{b(input), r()}], false),
  M2 = struct([{b(input), r(1)}], true),

  Result = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Result,

  ok.
simple_normalize10_map_test() ->
  % #{in := 1, out := 2}  ≤  #{a := 1, β := γ}
  M1 = struct([{b(in), r(1)}, {b(out), r(2)}], false),
  M2 = struct([{v(alpha), r(1)}, {v(beta), v(gamma)}], false),

  Result = normalize(M1, M2, sets:new()),

  U = u(b(in), b(out)),
  Expected = norm_css([
    [{v(alpha), U, U}, {v(beta), U, U}, {v(gamma), r(2), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => U,  v(beta) => U, v(gamma) => r(2)}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
norm_map1_test() ->
  % #{a => int()}  ≤  #{int() => β}
  M1 = struct([{v(alpha), opt(r())}], false),  %%  M2 = struct([{v(theta), opt(v(beta))}], false),
  M2 = i([
    dict(stp(i), v(beta)),
    dict(stp(a), none()),
    dict(stp(t), none())
  ]),

  Result = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), none(), r()}, {v(beta), r(), any()}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => none(),  v(beta) => r()},
    #{v(alpha) => r(),  v(beta) => r()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
%%normalize_map_values_test() ->
%%  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, theta => gamma}
%%  M1 = i([
%%    dict(stp(i), b()),
%%    dict(stp(a), r()),
%%    dict(stp(t), none())
%%  ]),
%%  M2 = i([
%%    dict(stp(i), v(alpha)),
%%    dict(stp(a), v(beta)),
%%    dict(stp(t), none())
%%  ]),
%%  M3 = struct([{v(theta), opt(v(gamma))}], true),
%%
%%  Res = normalize(M1, i(M2, M3), sets:new()),
%%
%%  _Expected = norm_css([
%%    [{v(alpha), b(), any()}, {v(beta), r(), any()}]
%%  ]),
%%
%%  true = Res,
%%
%%  ok.
norm_map2_test() ->
  % #{a := β, _ => any()}  ≤  #{γ := δ, _ => any()}
  M1 = struct([{v(alpha), v(beta)}], true),
  M2 = struct([{v(gamma), v(delta)}], true),

  Result = normalize(M1, M2, sets:new()),

  Expected = norm_css([
    [{v(alpha), v(gamma), v(gamma)}, {v(beta), none(), v(delta)}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => any(),  v(beta) => any()}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
norm_map3_test() ->
  % #{}  !≤  #{a := b}
  M1 = struct([], false),
  M2 = struct([{v(alpha), v(beta)}], false),

  Res = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Res,

  ok.
norm_map4_test() ->
  % #{a => any()}  ≤  #{any() => any()}
  M1 = struct([{v(alpha), opt(any())}], false),
  M2 = struct([], true),

  Result = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), none(), KeyDomain}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => KeyDomain}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
norm_map5_test() ->
  % #{a := 2}  ≤  #{b => 2},
  M1 = struct([{v(alpha), r(2)}], false),
  M2 = struct([{v(beta), opt(r(2))}], false),

  Result = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), none(), v(beta)}, {v(beta), none(), KeyDomain}]
  ]),

  TestSubstitutions = norm_substs([
    #{v(alpha) => v(beta),  v(beta) => KeyDomain}
  ]),

  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),

  ok.
norm_map6_test() ->
  % #{a => int(), _ => any()}  ≤  #{b => any()}
  M1 = struct(
    [{v(alpha), opt(r())}], true),
  M2 = struct(
    [{v(beta), opt(any())}], false),

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), none(), v(beta)}, {v(beta), KeyDomain, KeyDomain}]
  ]),

  true = Res == Expected,

  ok.
norm_map7_test() ->
  % #{input => 1}  !≤  #{input := 1}
  M1 = struct(
    [{b(input), opt(r(1))}], false),
  M2 = struct(
    [{b(input), r(1)}], false),

  Res = normalize(M1, M2, sets:new()),

  true = [] == Res,

  ok.

% =====
% Relation Map
% =====

norm_relmap1_test() ->
  % #{int() => int()}  ≤  #{a => β}
  M1 = relmap([t(r(), r())], []),
  M2 = relmap([t(v(alpha), v(beta))], []),
  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), r(), any()}, {v(beta), r(), any()}]
  ]),
  true = Res == Expected,
  ok.

norm_relmap2_test() ->
  % #{int() => int(), atom() => atom()}  ≤  #{a => β}
  M1 = relmap([t(r(), r()), t(b(), b())], []),
  M2 = relmap([t(v(alpha), v(beta))], []),
  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), u(r(), b()), any()}, {v(beta), u(r(), b()), any()}]
  ]),
  true = Res == Expected,
  ok.

norm_relmap3_test() ->
  % #{int() => int(), _ => foo}  ≤  #{a => β}
  M1 = relmap([t(r(), r()), t(rest(r()), b(foo))], []),
  M2 = relmap([t(v(alpha), v(beta))], []),
  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), any(), any()}, {v(beta), u(r(), b(foo)), any()}]
  ]),
  true = Res == Expected,
  ok.

norm_relmap4_test() ->
  % #{a => int()}  ≤  #{int() => β}
  M1 = relmap([t(v(alpha), r())], []),
  M2 = relmap([t(r(), v(beta))], []),
  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), none(), none()}],
    [{v(alpha), none(), r()}, {v(beta), r(), any()}]
  ]),
  true = Res == Expected,
  ok.

norm_relmap5_test() ->
  % #{int() => β} ≤  #{a => int()}
  M1 = relmap([t(r(), v(beta))], []),
  M2 = relmap([t(v(alpha), r())], []),
  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), r(), any()}, {v(beta), none(), r()}],
    [{v(beta), none(), none()}]
]),
  true = Res == Expected,
  ok.

norm_relmap6_test() ->
  % #{a => int(), _ => atom()}  ≤  #{b => atom() | int()}
  M1 = relmap([t(v(alpha), r()), t(rest(v(alpha)),b())], []),
  M2 = relmap([t(v(beta), u(b(), r()))], []),
  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), n(v(beta)), v(beta)}]
  ]),
  true = Res == Expected,
  ok.

norm_relmap7_test() -> % interesting property or to be fixed?
  % #{}  ≤  #{a := β} -- fix with constraint gen (no zero for mandatory): 1 !≤ a  <=  a ≤ int  orelse  a ≤ atom  orelse  a ≤ tuple
  M1 = relmap([], []),
  M2 = relmap([], [f(v(alpha), v(beta))]),
  Res = normalize(M1, M2, sets:new()),
  _Expected = norm_css([
    [{v(alpha), none(), none()}]
  ]),
  true = Res,
  ok.

norm_relmap8_test() ->
  % #{bar := int(), _ => any()}  !≤  #{foo := 1, a => β} -- constraint gen: a ≤ -RestKeys
  M1 = relmap([t(rest(b(bar)), any())], [f(b(bar), r())]),
  M2 = relmap([t(i(v(alpha), rest(b(foo))), v(beta))], [f(b(foo), r(1))]),
  Res = normalize(M1, M2, sets:new()),
  true = Res,
  ok.

norm_relmap9_test() ->
  % #{foo := 1, bar := 2}  ≤  #{a := 1, β := γ}
  M1 = relmap([], [f(b(foo), r(1)), f(b(bar), r(2))]),
  M2 = relmap([], [f(v(alpha), r(1)), f(v(beta), v(gamma))]),
  Res = normalize(M1, M2, sets:new()),
  true = Res,
  ok.

norm_relmap10_test() ->
  % #{a := β, _ => any()}  ≤  #{γ := δ, _ => any()}
  M1 = relmap([t(rest(v(alpha)), any())], [f(v(alpha), v(beta))]),
  M2 = relmap([t(rest(v(gamma)), any())], [f(v(gamma), v(delta))]),
  Res = normalize(M1, M2, sets:new()),
  true = Res,
  ok.

norm_relmap11_test() ->
  % #{i := vi}  ≤  #{a := v1, β := δ} -- efficiency
  Ks = [1,2,3],
  Vs = [v1,v2,v3],
  Fs = [f(r(K), b(V)) || {K, V} <- lists:zip(Ks, Vs)],
  _M1 = relmap([], Fs),
  _M2 = relmap([], [f(v(alpha), b(v1)), f(v(beta), v(gamma))]),
%%  Res = normalize(M1, M2, sets:new()),
%%  true = Res,
  ok.

norm_relmap12_test() ->
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ => δ}
  Rest = rest(u(r(), b())),
  M1 = relmap([t(r(), b()), t(b(), r())], []),
  M2 = relmap([t(r(), v(alpha)), t(b(), v(beta)), t(i(v(gamma), Rest), v(delta))], []),
  Res = normalize(M1, M2, sets:new()),
  true = Res,
  ok.

norm_relmap13_test() ->
  % #{foo := int(), _ => any()}  ≤  #{a := β, _ => any()} | #{γ := δ, _ => any()}
  M1 = relmap([t(rest(b(foo)), any())], [f(b(foo), r())]),
  M2 = u(
    relmap([t(rest(v(alpha)), any())], [f(v(alpha), v(beta))]),
    relmap([t(rest(v(gamma)), any())], [f(v(gamma), v(delta))])
  ),
  Res = normalize(M1, M2, sets:new()),
  true = Res,
  ok.

norm_relmap14_test() ->
  % #{input => 1}  !≤  #{input := 1}
  M1 = relmap([t(b(input), r(1))], []),
  M2 = relmap([], [f(b(input), r(1))]),
  Res = normalize(M1, M2, sets:new()),
  true = Res,
  ok.