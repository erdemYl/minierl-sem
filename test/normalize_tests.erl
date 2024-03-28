-module(normalize_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [norm_substs/1, norm/1, mu/2, n/1, b/0, b/1, f/2, t/2, i/2, i/1, u/2, u/1, r/1, r/0, m/1, man/2, opt/2, step/2, none/0, any/0, v/1, subty/2, normalize/3, normalize/2, var_of/1, norm_css/1]).

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

maps_simple1_normalization_test() ->
  KeyDomain = u([r(), b(), t(any(), any())]),

  % { int()=>int() }  ≤  { a=>β }
  Result1 = normalize(m([step(i, r())]), m([opt(v(alpha), v(beta))]), sets:new()),
  Expected1 = norm_css([
    [{v(alpha), r(), r()}, {v(beta), r(), any()}]
  ]),
  TestSubstitutions1 = norm_substs([
    #{v(alpha) => r(),  v(beta) => r()},
    #{v(alpha) => r(),  v(beta) => any()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected1, Result1, TestSubstitutions1),

  % { int()=>int(),  atom()=>atom() }  ≤  { a=>β }
  Result2 = normalize(m([step(i, r()), step(a, b())]), m([opt(v(alpha), v(beta))]), sets:new()),
  Expected2 = norm_css([
    [{v(alpha), u(r(), b()), u(r(), b())}, {v(beta), u(r(), b()), any()}]
  ]),
  TestSubstitutions2 = norm_substs([
    #{v(alpha) => u(r(), b()),  v(beta) => u(r(), b())},
    #{v(alpha) => u(r(), b()),  v(beta) => any()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected2, Result2, TestSubstitutions2),

  % { int()=>int(), _=>foo }  ≤  { a=>β }
  Result3 = normalize(
    m([step(i, r()), step(a, b(foo)), step(i, b(foo)), step(t, b(foo))]),
    m([opt(v(alpha), v(beta))]),
    sets:new()
  ),
  Expected3 = norm_css([
    [{v(alpha), KeyDomain, u(r(), b(foo))}, {v(beta), u(r(), b(foo)), any()}]
  ]),
  TestSubstitutions3 = norm_substs([
    #{v(alpha) => u(r(), b()),  v(beta) => u(r(), b())},
    #{v(alpha) => u(r(), b()),  v(beta) => any()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected3, Result3, TestSubstitutions3).


maps_simple2_normalization_test() ->
  KeyDomain = u([r(), b(), t(any(), any())]),

  % { a=>int() }  !≤  { int()=>β }
  Result1 = normalize(m([opt(v(alpha), r())]), m([step(i, v(beta))]), sets:new()),
  Expected1 = [],
  true = Expected1 == Result1,

  % { int()=>β }  ≤  { a=>int() }
  Result2 = normalize(m([step(i, v(beta))]), m([opt(v(alpha), r())]), sets:new()),
  Expected2 = norm_css([
    [{v(alpha), r(), r()}, {v(beta), none(), r()}]
  ]),
  TestSubstitutions2 = norm_substs([
    #{v(alpha) => r(),  v(beta) => none()},
    #{v(alpha) => r(),  v(beta) => r()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected2, Result2, TestSubstitutions2),

  % { a=>int(), _=>atom() }  ≤  { β=>atom()|int() }
  Result3 = normalize(
    m([opt(v(alpha), r()), step(a, b()), step(i, b()), step(t, b())]),
    m([opt(v(beta), u(b(), r()))]),
    sets:new()
  ),
  Expected3 = norm_css([
    [{v(alpha), none(), any()}, {v(beta), KeyDomain, KeyDomain}]
  ]),
  TestSubstitutions3 = norm_substs([
    #{v(alpha) => none(),  v(beta) => KeyDomain},
    #{v(alpha) => none(),  v(beta) => KeyDomain}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected3, Result3, TestSubstitutions3),

  % { β=>atom()|int() }  !≤  { a=>int(), _=>atom() }
  Result4 = normalize(
    m([opt(v(beta), u(b(), r()))]),
    m([opt(v(alpha), r()), step(a, b()), step(i, b()), step(t, b())]),
    sets:new()
  ),
  Expected4 = [],
  true = Expected4 == Result4.


maps_complex1_normalization_test() ->
  % {}  ≤  { a:=β }
  Result1 = normalize(m([]), m([man(v(alpha), v(beta))]), sets:new()),
  Expected1 = norm_css([
    [{v(alpha), none(), none()}, {v(beta), none(), any()}]
  ]),
  TestSubstitutions1 = norm_substs([
    #{v(alpha) => none(),  v(beta) => none()},
    #{v(alpha) => none(),  v(beta) => any()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected1, Result1, TestSubstitutions1),

  % {}  ≤  { a:=β } ∧ {}
  Result2 = normalize(m([]), i(m([man(v(alpha), v(beta))]), m([])), sets:new()),
  Expected2 = norm_css([
    [{v(alpha), none(), none()}, {v(beta), none(), any()}]
  ]),
  TestSubstitutions2 = norm_substs([
    #{v(alpha) => none(),  v(beta) => none()},
    #{v(alpha) => none(),  v(beta) => any()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected2, Result2, TestSubstitutions2).


maps_complex2_normalization_test() ->
  % { foo:=int(), _=>any() }  !≤  { foo:=1, a=>β }
  Result1 = normalize(
    m([man(b(foo), r()), step(a, any()), step(i, any()), step(t, any())]),
    m([man(b(foo), r(1)), opt(v(alpha), v(beta))]),
    sets:new()
  ),
  Expected1 = [],
  true = Expected1 == Result1,

  % { foo:=1, bar:=2 }  ≤  { a:=1, β:=γ } = { a|β:=1|γ }
  Result2 = normalize(
    m([man(b(foo), r(1)), man(b(bar), r(2))]),
    m([man(v(alpha), r(1)), man(v(beta), v(gamma))]),
    sets:new()
  ),
  Expected2 = norm_css([
    [{v(alpha), i(u(b(foo), b(bar)), n(v(beta))), i(u(b(foo), b(bar)), n(v(beta)))}, % (1|2)\β ≤ a ≤ (1|2)\β
      {v(beta), none(), u(b(foo), b(bar))}, % 0 ≤ β ≤ 1|2
      {v(gamma), r(2), any()}
    ]
  ]),
  TestSubstitutions2 = norm_substs([
    #{v(alpha) => b(foo),  v(beta) => b(bar), v(gamma) => r(2)},
    #{v(alpha) => b(bar),  v(beta) => b(foo), v(gamma) => r(2)}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected2, Result2, TestSubstitutions2),

  % { a:=β, _=>any() }  ≤  { γ:=δ, _=>any() }
  Result3 = normalize(
    m([man(v(alpha), v(beta)), step(a, any()), step(i, any()), step(t, any())]),
    m([man(v(gamma), v(delta)), step(a, any()), step(i, any()), step(t, any())]),
    sets:new()
  ),
  Expected3 = norm_css([
    [{v(alpha), none(), none()},
      {v(gamma), none(), none()}
    ]
  ]),
  TestSubstitutions3 = norm_substs([
    #{v(alpha) => none(),  v(beta) => none(), v(gamma) => none(), v(delta) => any()},
    #{v(alpha) => none(),  v(beta) => any(), v(gamma) => none(), v(delta) => any()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected3, Result3, TestSubstitutions3).


maps_complex3_normalization_test() ->
  % { int()=>atom(), atom()=>int() }  ≤  { int()=>a, atom()=>β, γ=>δ }
  Result1 = normalize(
    m([step(i, b()), step(a, r())]),
    m([step(i, v(alpha)), step(a, v(beta)), opt(v(gamma), v(delta))]),
    sets:new()
  ),
  Expected1 = norm_css([
    [{v(alpha), b(), any()},
      {v(beta), r(), any()},
      {v(gamma), none(), none()}
    ]
  ]),
  TestSubstitutions1 = norm_substs([
    #{v(alpha) => b(),  v(beta) => r(), v(gamma) => none()},
    #{v(alpha) => any(), v(beta) => any(), v(gamma) => none()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected1, Result1, TestSubstitutions1),

  % { foo:=int(), _=>atom() }  ≤  { a:=β, _=>any() } | { γ:=δ, _=>any() }
  Result2 = normalize(
    m([man(b(foo), r()), step(a, b()), step(i, b()), step(t, b())]),
    u(
      m([man(v(alpha), v(beta)), step(a, any()), step(i, any()), step(t, any())]),
      m([man(v(gamma), v(delta)), step(a, any()), step(i, any()), step(t, any())])
    ),
    sets:new()
  ),
  Expected2 = norm_css([
    [{v(alpha), b(foo), b(foo)}, {v(beta), r(), any()}],
    [{v(gamma), b(foo), b(foo)}, {v(delta), r(), any()}]
    % one redundant constraint set removed
  ]),
  TestSubstitutions2 = norm_substs([
    #{v(alpha) => b(foo), v(beta) => r()},
    #{v(gamma) => b(foo), v(delta) => r()}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected2, Result2, TestSubstitutions2),

  % { foo:=1, bar=>2 }  ≤  { β=>1|2 }
  Result3 = normalize(
    m([man(b(foo), r(1)), opt(b(bar), r(2))]),
    m([opt(v(beta), u(r(1), r(2)))]),
    sets:new()
  ),
  Expected3 = norm_css([
    [{v(beta), u(b(foo), b(bar)), u(b(foo), b(bar))}]
  ]),
  TestSubstitutions3 = norm_substs([
    #{v(beta) => u(b(foo), b(bar))}
  ]),
  true = set_of_constraint_sets:is_equivalent(Expected3, Result3, TestSubstitutions3).


maps_limited_normalization_test() ->
  % { foo:=1, bar=>2 }  !≤  { a:=1, β=>2 }
  Result = normalize(
    m([man(b(foo), r(1)), opt(b(bar), r(2))]),
    m([man(v(alpha), r(1)), opt(v(beta), r(2))]),
    sets:new()
  ),
  Expected = [],
  true = Expected == Result.