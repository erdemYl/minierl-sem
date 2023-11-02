-module(normalize_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [norm_substs/1, norm/1, mu/2, n/1, b/0, b/1, f/2, t/0, t/2, i/2, i/1, u/2, u/1, r/1, r/0, struct/2, dict/2, opt/1, stp/1, none/0, any/0, v/1, subty/2, normalize/3, normalize/2, var_of/1, norm_css/1]).

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

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), r(), KeyDomain}, {v(beta), r(), any()}]
  ]),

  true = Expected == Res,

  ok.
simple_normalize2_map_test() ->
  % #{int() => int(), atom() => atom()}  ≤  #{a => β}
  M1 = i([
    dict(stp(i), r()),
    dict(stp(a), b()),
    dict(stp(t), none())
  ]),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), u(r(), b()), KeyDomain}, {v(beta), u(r(), b()), any()}]
  ]),

  true = Expected == Res,

  ok.
simple_normalize3_map_test() ->
  % #{int() => int(), _ => any()}  ≤  #{a => β}
  M1 = dict(stp(i), r()),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), KeyDomain, KeyDomain}, {v(beta), any(), any()}]
  ]),

  true = Expected == Res,

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
  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), KeyDomain, KeyDomain}, {v(beta), u(r(), b(foo)), any()}]
  ]),

  true = Expected == Res,

  ok.
simple_normalize5_map_test() ->
  % #{input := int()}  ≤  #{a => β}
  M1 = struct([{b(input), r()}], false),
  M2 = struct([{v(alpha), opt(v(beta))}], false),

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), b(input), KeyDomain}, {v(beta), r(), any()}]
  ]),

  true = Expected == Res,

  ok.
simple_normalize6_map_test() ->
  % #{input := int(), _ => any()}  ≤  #{a := β, _ => any()} or #{zeta := theta, _ => any()}
  M1 = struct([{b(input), r()}], true),
  M2 = struct([{v(alpha), v(beta)}], true),
  M3 = struct([{v(zeta), v(theta)}], true),

  Res = normalize(M1, u(M2, M3), sets:new()),
  _Expected = norm_css([
    [{v(alpha), b(input), b(input)}, {v(beta), r(), any()}],
    [{v(zeta), b(input), b(input)}, {v(theta), r(), any()}]
    % and something
  ]),

  true = Res,

  ok.
simple_normalize7_map_test() ->
  % #{input := int(), _ => any()}  ≤  #{input := bool, a => β}
  M1 = struct([{b(input), r()}], true),
  M2 = struct([
    {b(input), b(bool)},
    {v(alpha), opt(v(beta))}], false),

  Res = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Res,

  ok.
simple_normalize8_map_test() ->
  % #{input := int(), _ => any()}  ≤  #{input := 1, a => β}
  M1 = struct([{b(input), r()}], true),
  M2 = struct([
    {b(input), r(1)},
    {v(alpha), opt(v(beta))}], false),

  Res = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Res,

  ok.
simple_normalize9_map_test() ->
  % #{input := int()}  ≤  #{input := 1, _ => any()}
  M1 = struct([{b(input), r()}], false),
  M2 = struct([{b(input), r(1)}], true),

  Res = normalize(M1, M2, sets:new()),
  Expected = [],

  true = Expected == Res,

  ok.
simple_normalize10_map_test() ->
  % #{in := 1, out := 2}  ≤  #{a := 1, β := theta}
  % TODO show variations
  M1 = struct([{b(in), r(1)}, {b(out), r(2)}], false),
  M2 = struct([{v(alpha), r(1)}, {v(beta), v(theta)}], false),

  Res = normalize(M1, M2, sets:new()),

  U = u(b(in), b(out)),
  Expected = norm_css([
    [{v(alpha), U, U}, {v(beta), U, U}, {v(theta), r(2), any()}]
  ]),

  true = Expected == Res,

  ok.
norm_map1_test() ->
  % #{a => int()}  ≤  #{int() => β}
  % TODO ask, show variations
  M1 = struct([{v(alpha), opt(r())}], false),  %%  M2 = struct([{v(theta), opt(v(beta))}], false),
  M2 = i([
    dict(stp(i), v(beta)),
    dict(stp(a), none()),
    dict(stp(t), none())
  ]),

  Res = normalize(M1, M2, sets:new()),
  Expected = norm_css([
    [{v(alpha), none(), r()}, {v(beta), r(), any()}]
  ]),

  true = Expected == Res,

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
  % #{a := β, _ => any()}  ≤  #{zeta := theta, _ => any()}
  M1 = struct([{v(alpha), v(beta)}], true),
  M2 = struct([{v(zeta), v(theta)}], true),

  Res = normalize(M1, M2, sets:new()),

  Expected = norm_css([
    [{v(alpha), v(zeta), v(zeta)}, {v(beta), none(), v(theta)}]
  ]),

  true = Expected == Res,

  ok.
norm_map3_test() ->
  % #{}  ≤  #{zeta := theta}
  M1 = struct([], false),
  M2 = struct([{v(zeta), v(theta)}], false),

  Res = normalize(i(M1, M2), M1, sets:new()),
  Expected = [[]],

  true = Expected == Res,

  ok.
norm_map4_test() ->
  % #{a => any()}  ≤  #{any() => any()}
  M1 = struct([{v(alpha), opt(any())}], false),
  M2 = struct([], true),

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), none(), KeyDomain}]
  ]),

  true = Expected == Res,

  ok.
norm_map5_test() ->
  % #{a := 2}  ≤  #{b => 2},
  M1 = struct([{v(alpha), r(2)}], false),
  M2 = struct([{v(beta), opt(r(2))}], false),

  Res = normalize(M1, M2, sets:new()),

  KeyDomain = u([b(), r(), t()]),
  Expected = norm_css([
    [{v(alpha), none(), v(beta)}, {v(beta), none(), KeyDomain}]
  ]),

  true = Expected == Res,

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

  true = Expected == Res,

  ok.
norm_map7_test() ->
  % #{input => 1}  ≤  #{input := 1}
  M1 = struct(
    [{b(input), opt(r(1))}], false),
  M2 = struct(
    [{b(input), r(1)}], false),

  Res = normalize(M1, M2, sets:new()),

  true = [] == Res,

  ok.
