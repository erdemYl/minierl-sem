-module(subty_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [mu/2, n/1, b/1, f/2, t/2, i/2, i/1, u/2, u/1, r/1, r/0, none/0, any/0, v/1, subty/2, struct/2, dict/2, stp/1]).

simple_test_() ->
  Data = lists:map(
    fun
      L({_Name, S, T, SltT, TltS}) ->
        fun() ->
          SltT = subty(S, T),
          TltS = subty(T, S),
          ok
        end
      ;
      L({Name, S, T, SltT}) -> L({Name, S, T, SltT, SltT})
    end, basic_monomorphic_tests()),

  Data.


basic_monomorphic_tests() ->
  [ % {name, S, T, S <: T?, T <: S?}
    {int_any, r(), r(), true},
    {interval1, u([u([r(), r(1)]), r(2)]), r(), true},
    {interval2, u([r(1), r(2)]), r(), true, false},
    {interval3, r(0), r(), true, false},
    {interval4, i([u([r(1), r(2)]), u([r(1), r(2)])]), r(), true, false},
    {interval5, r(2),  u([r(1), r(2)]), true, false},
    {interval_empty, r(2),  none(), false, true}
  ]
.

edge_cases_test() ->
  false = subty(v(alpha), none),
  true = subty(none, v(alpha)),

  true = subty(v(alpha), any),
  true = subty(v(alpha), v(alpha)),
  false = subty(v(alpha), v(beta)),

  ok.

simple_var_test() ->
  S = v(alpha),
  T = r(),
  A = r(10),

  false = subty(S, A),
  false = subty(S, T),
  false = subty(A, S),
  false = subty(T, S).

simple_prod_test() ->
  S = t(r(1), r()),
  T = t(r(), r()),

  true = subty(S, T),
  false = subty(T, S),

  ok.

simple_prod_var_test() ->
  S = t(r(1), r()),
  T = t(v(alpha), v(beta)),

  false = subty( S, T ),
  false = subty(T, S),
  ok.

% (α × t) ∧ α !≤ ((1 × 1) × t)
tricky_substitution_step_5_test() ->
  A = i([t(v(alpha), r()), v(alpha)]),
  B = t(t(any(), any()), r()),
  false = subty(A, B).

% α ∧ (α × t) ≤ α
type_variables_are_not_basic_types_test() ->
  S = i([v(alpha), t(v(alpha), r())]),
  T = v(alpha),
  true = subty(S, T).

% (S-->T)&(S-->U) <: S-->T&U
axiom_intersection_test() ->
  S = r(1),
  T = r(2),
  U = r(3),
  Ty1 = i([f(S, T), f(S, U)]),
  Ty2 = f(S, i([T, U])),

  true = subty(Ty1, Ty2).

% (S-->U)&(T-->U) <: S|T-->U
axiom_union_test() ->
  S = r(1),
  T = r(2),
  U = r(3),
  Ty1 = i(f(S, U), f(T, U)),
  Ty2 = f(u(S, T), U),

  true = subty(Ty1, Ty2).

% (o1 | o2) --> (t1 | t2)  <:> ( o1 -> t1 | t2 ) & ( o2 -> t1 | t2 )
axiom_unions_test() ->
  S = f(u(b(o1), b(o2)), u(b(t1), b(t2))),
  T = i(f(b(o1), u(b(t1), b(t2))), f(b(o2), u(b(t1), b(t2)))),
  true = subty( S, T ),
  true = subty( T, S ).

% (o1 | o2) --> (t)  <:> ( o1 -> t ) & ( o2 -> t )
axiom_unions_left_test() ->
  S = f(u(b(o1), b(o2)), b(t)),
  T = i(f(b(o1), b(t)), f(b(o2), b(t))),
  true = subty( S, T ),
  true = subty( T, S ).

% (o) --> (t1 | t2)  <:> ( o1 -> t1 | t2 ) & ( o2 -> t1 | t2 )
axiom_unions_right_test() ->
  S = f(u(b(o1), b(o2)), u(b(t1), b(t2))),
  T = i(f(b(o1), u(b(t1), b(t2))), f(b(o2), u(b(t1), b(t2)))),
  true = subty( S, T ),
  true = subty( T, S ).

% annotation: 1 -> 1|2
% inferred body type: 1 -> 1
refine_2_test() ->
  Annotation = f(b(a), u(b(a), b(b))),
  Body = f(b(a), b(a)),
  false = subty( Annotation, Body ).

% annotation: 1|2 -> 1|2
% inferred body type: 1 -> 1 & 2 -> 2
refine_test() ->
  Annotation = f(u(b(a), b(b)), u(b(a), b(b))),
  Body = i(f(b(a), b(a)), f(b(b), b(b))),
  true = subty( Body, Annotation ),
  false = subty( Annotation, Body ).

% (α → γ) ∧ (β → γ) ∼ (α∨β) → γ
arrow_distribution_test() ->
  S = i(f(v(alpha), v(gamma)), f(v(beta), v(gamma))),
  T = f(u(v(alpha), v(beta)), v(gamma)),
  true = subty( S, T ),
  true = subty( T, S ).

% ((α∨β) × γ) ∼ (α×γ) ∨ (β×γ)
tuple_distributivity_test() ->
  S = t(u(v(alpha), v(beta)), v(gamma)),
  T = u(t(v(alpha), v(gamma)), t(v(beta), v(gamma))),
  true = subty( S, T ),
  true = subty( T, S ).

% (α×γ → δ1 ) ∧ (β×γ → δ2 ) ≤ ((α∨β) × γ) → δ1 ∨ δ2
intersection_of_domains_and_codomains_arrows_test() ->
  S = i(f(t(v(alpha), v(gamma)), v(delta1)), f(t(v(beta), v(gamma)), v(delta2))),
  T = f(t(u(v(alpha), v(beta)), v(gamma)), u(v(delta1), v(delta2))),
  true = subty( S, T ),
  false = subty( T, S ).


% 1 → 0 ≤ α → β ≤ 0 → 1
non_trivial_arrow_containment_test() ->
  A = f(any(), none()),
  B = f(v(alpha), v(beta)),
  C = f(none(), any()),
  true = subty( A, B ),
  true = subty( B, C ),
  true = subty( A, C ),

  false = subty( B, A ),
  false = subty( C, B ),
  false = subty( C, A ).

% 1 ≤ ((α ⇒ β) ⇒ α) ⇒ α
pierces_law_test() ->
  A = any(),
  B = u(n( u(n(u(n(v(alpha)), v(beta))), v(alpha)) ), v(alpha)),
  true = subty( A, B ).

% nil × α ≤! (nil × ¬nil) ∨ (α × nil)
stuttering_validity_test() ->
  A = t(b(nil), v(alpha)),
  B = u(
    t(b(nil), n(b(nil))),
    t(v(alpha), b(nil))
  ),
  false = subty( A, B ).

% α1 → β1 ≤ ((α1 ∧α2 )→(β1 ∧β2 )) ∨ ¬(α2 →(β2 ∧¬β1 ))
subtle_arrow_relation_test() ->
  S = f(v(alpha1), v(beta1)),
  T = u(f(i(v(alpha1), v(alpha2)), i(v(beta1), v(beta2))),
    n(f(v(alpha2), i(v(beta2), n(v(beta1)))))),
  true = subty( S, T ).

neg_var_prod_test() ->
  S = t(b(hello), v(alpha)),
  T = v(alpha),

  false = subty( S, T ),
  false = subty( T, S ),
  ok.

% µx.(α×(α×x)) ∨ nil  ≤ µx.(α×x)     ∨ nil
% µx.(α×x)     ∨ nil !≤ µx.(α×(α×x)) ∨ nil
even_lists_contained_in_lists_test() ->
  S = mu(v(x),  u(t(v(a), t(v(a), v(x))), b(nil))),
  T = mu(v(x2), u(t(v(a), v(x2)), b(nil))),
  true  = subty(S, T),
  false = subty(T, S),
  ok.

% µx.(α×(α×x)) ∨ (α×nil)  ≤ µx.(α×x)     ∨ nil
% µx.(α×x)     ∨ (α×nil) !≤ µx.(α×(α×x)) ∨ nil
uneven_lists_contained_in_lists_test() ->
  S = mu(v(x),  u(t(v(a), t(v(a), v(x))), t(v(a), b(nil)))),
  T = mu(v(x2), u(t(v(a), v(x2)), b(nil))),
  true  = subty(S, T),
  false = subty(T, S),
  ok.

% µx.(α×x) ∨ nil ∼ (µx.(α×(α×x))∨nil) ∨ (µx.(α×(α×x))∨(α×nil))
uneven_even_lists_contained_in_lists_test() ->
  Even = mu(v(x),  u(t(v(a), t(v(a), v(x))), b(nil))),
  Uneven = mu(v(x2),  u(t(v(a), t(v(a), v(x2))), t(v(a), b(nil)))),
  U = u(Even, Uneven),
  AllList = mu(v(x3), u(t(v(a), v(x3)), b(nil))),

  true = subty(U, AllList),
  true = subty(AllList, U),

  ok.

% (µx.(α×(α×x))∨nil) <!> (µx.(α×(α×x))∨(α×nil))
uneven_even_lists_not_comparable_test() ->
  Even = mu(v(x),  u(t(v(a), t(v(a), v(x))), b(nil))),
  Uneven = mu(v(x2),  u(t(v(a), t(v(a), v(x2))), t(v(a), b(nil)))),

  false = subty(Even, Uneven),
  false = subty(Uneven, Even),

  ok.

% ====
% Map tests
% ====

maps_any_empty_test() ->
  % struct
  EmptyS = struct([], false), % type that only contains empty struct
  AnyS = struct([], true),
  true = subty(EmptyS, AnyS),
  false = subty(AnyS, EmptyS),
  false = subty(EmptyS, none()),

  % dict
  EmptyD = i([
    dict(stp(i), none()),
    dict(stp(a), none()),
    dict(stp(t), none())
  ]),
  % all same, all any map
  A1 = dict(stp(i), any()),
  A2 = dict(stp(a), any()),
  A3 = dict(stp(t), any()),
  As = [A1, A2, A3],

  true = subty(A1, A3),
  true = subty(A3, A1),
  true = lists:all(fun(X) -> subty(AnyS, X) end, As),
  true = lists:all(fun(X) -> subty(X, AnyS) end, As),
  true = subty(EmptyS, EmptyD) andalso subty(EmptyD, EmptyS)
.

dict_interpretation_test() ->
  S = u([r(1), r(2), r(3)]),
  T = u([r(1), r(2)]),
  IntDict = dict(stp(i), S),
  IntDict2 = dict(stp(i), T),
  AtomDict = dict(stp(a), S),

  false = subty(IntDict, AtomDict),
  false = subty(AtomDict, IntDict),
  true = subty(IntDict2, IntDict)
.

% D1 = {integer() => T} ∧ {atom() => any()} ∧ {tuple() => none()}  ≤  {integer() => T} = D2
% D1 !≤ 0
dict_intersection_test() ->
  T = r(),
  D1 = i([
    dict(stp(i), T),
    dict(stp(a), any()),
    dict(stp(t), none())
  ]),
  D2 = dict(stp(i), T),

  true = subty(D1, D2),
  false = subty(D1, none())
.

% M1 = {1 := a, 2 := b}  !≤≥!  {atom() => atom} = M2
% M1 ≤ {tuple => any()} = M3
% M2 ≤ {tuple => any()} = M3
maps_simple_test() ->
  M1 = struct(
    [{r(1), b(a)}, {r(2), b(b)}],
    true),
  M2 = dict(stp(a), b(atom)),
  M3 = dict(stp(t), any()),

  true = subty(M2, M3),
  false = subty(M2, M1),
  false = subty(M1, M2),
  true = subty(M1, M3),

  M4 = struct(
    [{r(1), b(a)}, {r(2), b(b)}],
    false),

  true = subty(M4, M2),
  true = subty(M4, M3).

