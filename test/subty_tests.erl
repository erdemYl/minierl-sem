-module(subty_tests).
-include_lib("eunit/include/eunit.hrl").

%%-import(ast, [a/1, a/0, none/0, any/0, r/0, r/2, u/1, i/1, t/0, t/1, t/2, tfun_full/2, funs/0]).
-import(ast, [i/1, u/1, r/1, r/0, none/0, any/0, v/1, subty/2]).


%%timeout() -> 500.

simple_test_() ->
  Data = lists:map(
    fun
      L({_Name, S, T, SltT, TltS}) ->
        fun() ->
%%          io:format(user, "~p <: ~p :: ~p~n", [S, T, SltT]),
          SltT = subty(S, T),
%%          io:format(user, "~p <: ~p :: ~p~n", [T, S, TltS]),
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
  false = subty( v(alpha), none ),
  true = subty( none, v(alpha) ),
  true = subty( v(alpha), any ),
  true = subty( v(alpha), v(alpha)),
  false = subty( v(alpha), v(beta) ),
  ok.

simple_var_test() ->
  S = v(alpha),
  T = r(),
  A = r(10),

  false = subty( S, A ),
  false = subty( S, T ),
  false = subty( A, S ),
  false = subty( T, S ).

%%%%simple_prod_var_test() ->
%%%%  S = stdtypes:ttuple([stdtypes:a(hello)]),
%%%%  T = stdtypes:ttuple([stdtypes:tvar(alpha)]),
%%%%
%%%%  false = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ),
%%%%  ok.
%%%%
%%%%% (α × t) ∧ α !≤ ((1 × 1) × t)
%%%%tricky_substitution_step_5_test() ->
%%%%  A = tintersect([ttuple([v(alpha), b(int)]), v(alpha)]),
%%%%  B = ttuple([ttuple([tany(), tany()]), b(int)]),
%%%%  false = is_subtype( A, B ).

%%complex_monomorphic_tests() ->
%%  [ % {name, S, T, S <: T?, T <: S?}
%%    {basic_2, t(a(a), a(b)), t(any(), any()), t, f},
%%    {basic_3, t(a(a)), t(any(), any()), f},
%%    {basic_4, tfun_full([u([a(true), a(false)]), a(true)], a(ok)), tfun_full([a(false), a(true)], a(ok)), u, f},
%%    {empty_zero_tuple, none(), t(), t, f},
%%    {empty_tuple_2, none(), t(none(), a(hello)), t, t},
%%    {empty_fun_1, funs(), tfun_full([a(ok), none()], a(ok)), f, t},
%%    {empty_fun_2, funs(), tfun_full([none(), a(ok), a(no)], a(ok)), f, t},
%%    {funs_1, tfun_full([a(ok), none()], a(ok)), tfun_full([none(), a(ok), a(no)], a(ok)), f},
%%    ok
%%  ]
%%.
%%
%%
%%
%%
%%
%%
%% edge_1_test() ->
%%   Ty = {union,[
%%     {fun_full,[{negation,{predef,any}}],{predef,any}},
%%     {fun_full,[{negation, {singleton,a}}],{predef, any}}
%%   ]},
%%   Norm = ty_rec:norm(Ty),
%%   Ty2 = ty_rec:eval(Norm),
%%   true = is_equiv(Ty, Ty2).
%%
%%
%%
%%%%intersection_test() ->
%%%%  S = a(u(b(a), b(b)), u(b(a), b(b))),
%%%%  T = a(u(b(a), b(b)), u(b(a), b(b))),
%%%%  true = is_subtype( S, T ).
%%%%
%%%%% (S-->T)&(S-->U) <: S-->T&U
%%%%axiom_intersection_test() ->
%%%%  S = i(a(b(s), b(t)), a(b(s), b(u))),
%%%%  T = a(b(s), i(b(t), b(u))),
%%%%  true = is_subtype( S, T ).
%%%%
%%%%% (S-->U)&(T-->U) <: S|T-->U
%%%%axiom_union_test() ->
%%%%  S = i(a(b(s), b(u)), a(b(t), b(u))),
%%%%  T = a(u(b(s), b(t)), b(u)),
%%%%  true = is_subtype( S, T ).
%%%%
%%%%% (o1 | o2) --> (t1 | t2)  <:> ( o1 -> t1 | t2 ) & ( o2 -> t1 | t2 )
%%%%axiom_unions_test() ->
%%%%  S = a(u(b(o1), b(o2)), u(b(t1), b(t2))),
%%%%  T = i(a(b(o1), u(b(t1), b(t2))), a(b(o2), u(b(t1), b(t2)))),
%%%%  true = is_subtype( S, T ),
%%%%  true = is_subtype( T, S ).
%%%%
%%%%% (o1 | o2) --> (t)  <:> ( o1 -> t ) & ( o2 -> t )
%%%%axiom_unions_left_test() ->
%%%%  S = a(u(b(o1), b(o2)), b(t)),
%%%%  T = i(a(b(o1), b(t)), a(b(o2), b(t))),
%%%%  true = is_subtype( S, T ),
%%%%  true = is_subtype( T, S ).
%%%%
%%%%% (o) --> (t1 | t2)  <:> ( o1 -> t1 | t2 ) & ( o2 -> t1 | t2 )
%%%%axiom_unions_right_test() ->
%%%%  S = a(u(b(o1), b(o2)), u(b(t1), b(t2))),
%%%%  T = i(a(b(o1), u(b(t1), b(t2))), a(b(o2), u(b(t1), b(t2)))),
%%%%  true = is_subtype( S, T ),
%%%%  true = is_subtype( T, S ).
%%%%
%%%%% annotation: 1|2 -> 1|2
%%%%% inferred body type: 1 -> 1 & 2 -> 2
%%%%refine_test() ->
%%%%  Annotation = a(u(b(a), b(b)), u(b(a), b(b))),
%%%%  Body = i(a(b(a), b(a)), a(b(b), b(b))),
%%%%  true = is_subtype( Body, Annotation ),
%%%%  false = is_subtype( Annotation, Body ).
%%%%
%%%%% create fun_simple with only fun_full
%%%%all_funs_test() ->
%%%%  Everything =
%%%%  tunion([
%%%%    tnegate(tfun_full([a(b)], a(a))),
%%%%    tfun_full([a(b)], a(a))
%%%%  ]),
%%%%  true = is_equiv( Everything, {predef, any}),
%%%%
%%%%  OnlyFuns = tintersect([{predef, any},
%%%%    tnegate(tunion([a(), stdtypes:tspecial_any(), stdtypes:tlist_any(), trange_any(), ttuple_any()]))
%%%%  ]),
%%%%
%%%%  true = is_subtype({fun_simple}, OnlyFuns),
%%%%  true = is_subtype(OnlyFuns, {fun_simple}),
%%%%
%%%%  ok.
%%%%
%%%%
%%%%% (α → γ) ∧ (β → γ) ∼ (α∨β) → γ
%%%%arrow_distribution_test() ->
%%%%  S = i(a(v(alpha), v(gamma)), a(v(beta), v(gamma))),
%%%%  T = a(u(v(alpha), v(beta)), v(gamma)),
%%%%  true = is_subtype( S, T ),
%%%%  true = is_subtype( T, S ).
%%%%
%%%%% ((α∨β) × γ) ∼ (α×γ) ∨ (β×γ)
%%%%distributivity_test() ->
%%%%  S = p(u(v(alpha), v(beta)), v(gamma)),
%%%%  T = u(p(v(alpha), v(gamma)), p(v(beta), v(gamma))),
%%%%  true = is_subtype( S, T ),
%%%%  true = is_subtype( T, S ).
%%%%
%%%%% (α×γ → δ1 ) ∧ (β×γ → δ2 ) ≤ ((α∨β) × γ) → δ1 ∨ δ2
%%%%intersection_of_domains_and_codomains_arrows_test() ->
%%%%  S = i(a(p(v(alpha), v(gamma)), v(delta1)), a(p(v(beta), v(gamma)), v(delta2))),
%%%%  T = a(p(u(v(alpha), v(beta)), v(gamma)), u(v(delta1), v(delta2))),
%%%%  true = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ).
%%%%
%%%%% α ∧ (α × t) ≤ α
%%%%type_variables_are_not_basic_types_test() ->
%%%%  S = i(v(alpha), p(v(alpha), b(int))),
%%%%  T = v(alpha),
%%%%  true = is_subtype( S, T ).
%%%%
%%%%% 1 → 0 ≤ α → β ≤ 0 → 1
%%%%non_trivial_arrow_containment_test() ->
%%%%  A = a(tany(), tnone()),
%%%%  B = a(v(alpha), v(beta)),
%%%%  C = a(tnone(), tany()),
%%%%  true = is_subtype( A, B ),
%%%%  true = is_subtype( B, C ),
%%%%  true = is_subtype( A, C ),
%%%%
%%%%  false = is_subtype( B, A ),
%%%%  false = is_subtype( C, B ),
%%%%  false = is_subtype( C, A ).
%%%%
%%%%% 1 ≤ ((α ⇒ β) ⇒ α) ⇒ α
%%%%pierces_law_test() ->
%%%%  A = tany(),
%%%%  B = u(n( u(n(u(n(v(alpha)), v(beta))), v(alpha)) ), v(alpha)),
%%%%  true = is_subtype( A, B ).
%%%%
%%%%% nil × α ≤! (nil × ¬nil) ∨ (α × nil)
%%%%stuttering_validity_test() ->
%%%%  A = p(b(nil), v(alpha)),
%%%%  B = u(p(b(nil), b(nil)), p(v(alpha), b(nil))),
%%%%  false = is_subtype( A, B ).
%%%%
%%%%% α1 → β1 ≤ ((α1 ∧α2 )→(β1 ∧β2 )) ∨ ¬(α2 →(β2 ∧¬β1 ))
%%%%subtle_arrow_relation_test() ->
%%%%  S = a(v(alpha1), v(beta1)),
%%%%  T = u(a(i(v(alpha1), v(alpha2)), i(v(beta1), v(beta2))),
%%%%    n(a(v(alpha2), i(v(beta2), n(v(beta1)))))),
%%%%  true = is_subtype( S, T ).
%%%%
%%%%var_prod_test() ->
%%%%  S = i(stdtypes:ttuple([stdtypes:a(hello)]), stdtypes:tvar(alpha)),
%%%%  T = stdtypes:tvar(alpha),
%%%%
%%%%  true = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ),
%%%%  ok.
%%%%
%%%%neg_var_prod_test() ->
%%%%  S = stdtypes:ttuple([stdtypes:a(hello), stdtypes:tvar(alpha)]),
%%%%  T = stdtypes:tvar(alpha),
%%%%
%%%%  false = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ),
%%%%  ok.
%%%%
%%%%pos_var_prod_test() ->
%%%%  S = i(stdtypes:ttuple([stdtypes:a(hello)]), stdtypes:tvar(alpha)),
%%%%  T = stdtypes:tnegate(stdtypes:tvar(alpha)),
%%%%
%%%%  false = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ),
%%%%  ok.
%%%%
%%%%neg_var_fun_test() ->
%%%%  S = stdtypes:tfun_full([stdtypes:a(hello), stdtypes:tvar(alpha)], stdtypes:a(ok)),
%%%%  T = stdtypes:tvar(alpha),
%%%%
%%%%  false = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ),
%%%%  ok.
%%%%
%%%%pos_var_fun_test() ->
%%%%  S = i(stdtypes:tfun_full([stdtypes:a(hello)], stdtypes:a(ok)), stdtypes:tvar(alpha)),
%%%%  T = stdtypes:tnegate(stdtypes:tvar(alpha)),
%%%%
%%%%  false = is_subtype( S, T ),
%%%%  false = is_subtype( T, S ),
%%%%  ok.
%%%%
%%%%simple_named_test() ->
%%%%  Scheme = stdtypes:tyscm([a], stdtypes:tfun([stdtypes:tvar(a), stdtypes:tvar(a)], stdtypes:a(ok))),
%%%%  TyDef = {mynamed, Scheme},
%%%%  Form = {attribute, noloc(), type, transparent, TyDef},
%%%%  Sym = symtab:extend_symtab([Form], symtab:empty()),
%%%%
%%%%  S = {named, noloc(), {ref, mynamed, 1}, [{predef, integer}]},
%%%%  T = {named, noloc(), {ref, mynamed, 1}, [stdtypes:a(ok)]},
%%%%
%%%%  false = subty:is_subty(Sym, S, T),
%%%%  false = subty:is_subty(Sym, T, S),
%%%%  ok.
%%%%
%%%%simple_named2_test() ->
%%%%  Scheme2 = stdtypes:tyscm([a], stdtypes:a(helloworld)),
%%%%  TyDef2 = {mynamed2, Scheme2},
%%%%  Form2 = {attribute, noloc(), type, transparent, TyDef2},
%%%%
%%%%  Scheme = stdtypes:tyscm([a], {named, noloc(), {ref, mynamed2, 1}, [{var, a}]}),
%%%%  TyDef = {mynamed, Scheme},
%%%%  Form = {attribute, noloc(), type, transparent, TyDef},
%%%%
%%%%
%%%%  M = symtab:extend_symtab([Form], symtab:empty()),
%%%%  Sym = symtab:extend_symtab([Form2], M),
%%%%
%%%%  S = {named, noloc(), {ref, mynamed, 1}, [stdtypes:a(helloworld)]},
%%%%  T = stdtypes:a(helloworld),
%%%%
%%%%  true = subty:is_subty(Sym, S, T),
%%%%  ok.
%%%%
%%%%simple_recursive_test() ->
%%%%  Scheme = stdtypes:tyscm([a],
%%%%    stdtypes:tunion([stdtypes:a(emptylist), stdtypes:ttuple([stdtypes:tvar(a), {named, noloc(), {ref, mylist, 1}, [stdtypes:tvar(a)]}])])
%%%%  ),
%%%%  TyDef = {mylist, Scheme},
%%%%  Form = {attribute, noloc(), type, transparent, TyDef},
%%%%
%%%%  Sym = symtab:extend_symtab([Form], symtab:empty()),
%%%%
%%%%  S = named(mylist, [stdtypes:a(myints)]),
%%%%  T = stdtypes:a(helloworld),
%%%%
%%%%  false = subty:is_subty(Sym, S, T),
%%%%  ok.
%%%%
%%%%simple_basic_ulist_test() ->
%%%%  SymbolTable = predefSymbolicTable(),
%%%%
%%%%  S = named(ulist, [{predef, integer}]),
%%%%  T = named(ulist, [stdtypes:a(float)]),
%%%%
%%%%  true = subty:is_subty(SymbolTable, S, S),
%%%%  false = subty:is_subty(SymbolTable, S, T),
%%%%  false = subty:is_subty(SymbolTable, T, S),
%%%%
%%%%  ok.
%%%%
%%%%% µx.(α×(α×x)) ∨ nil  ≤ µx.(α×x)     ∨ nil
%%%%% µx.(α×x)     ∨ nil !≤ µx.(α×(α×x)) ∨ nil
%%%%even_lists_contained_in_lists_test() ->
%%%%  S = named(even_ulist, [tvar(alpha)]),
%%%%  T = named(ulist, [tvar(alpha)]),
%%%%  true  = subty:is_subty(predefSymbolicTable(), S, T),
%%%%  false = subty:is_subty(predefSymbolicTable(), T, S),
%%%%  ok.
%%%%
%%%%% µx.(α×(α×x)) ∨ (α×nil)  ≤ µx.(α×x)     ∨ nil
%%%%% µx.(α×x)     ∨ (α×nil) !≤ µx.(α×(α×x)) ∨ nil
%%%%uneven_lists_contained_in_lists_test() ->
%%%%  S = named(uneven_ulist, [tvar(alpha)]),
%%%%  T = named(ulist, [tvar(alpha)]),
%%%%  true  = subty:is_subty(predefSymbolicTable(), S, T),
%%%%  false = subty:is_subty(predefSymbolicTable(), T, S),
%%%%  ok.
%%%%
%%%%% µx.(α×x) ∨ nil ∼ (µx.(α×(α×x))∨nil) ∨ (µx.(α×(α×x))∨(α×nil))
%%%%uneven_even_lists_contained_in_lists_test() ->
%%%%  S = tunion([
%%%%    named(uneven_ulist, [tvar(alpha)]),
%%%%    named(even_ulist, [tvar(alpha)])
%%%%  ]),
%%%%  T = named(ulist, [tvar(alpha)]),
%%%%
%%%%  true  = subty:is_subty(predefSymbolicTable(), S, T),
%%%%  true = subty:is_subty(predefSymbolicTable(), T, S),
%%%%  ok.
%%%%
%%%%% (µx.(α×(α×x))∨nil) <!> (µx.(α×(α×x))∨(α×nil))
%%%%uneven_even_lists_not_comparable_test() ->
%%%%  S = named(uneven_ulist, [tvar(alpha)]),
%%%%  T = named(even_ulist, [tvar(alpha)]),
%%%%
%%%%  false  = subty:is_subty(predefSymbolicTable(), S, T),
%%%%  false = subty:is_subty(predefSymbolicTable(), T, S),
%%%%  ok.
%%%%
%%%%
%%%%empty_tuples_edge_cases_test() ->
%%%%  S = stdtypes:ttuple([]),
%%%%  T = stdtypes:ttuple([stdtypes:tany()]),
%%%%  true = is_subtype(S, S),
%%%%  false = is_subtype(S, T),
%%%%  false = is_subtype(T, S),
%%%%  true = is_subtype(S, stdtypes:ttuple_any()),
%%%%  false = is_subtype(stdtypes:ttuple_any(), S),
%%%%  ok.
%%%%
%%%%
%%%%simple_list_test() ->
%%%%  S = {empty_list},
%%%%  T = {list, {singleton, hello}},
%%%%  Ti = {improper_list, {singleton, hello}, {empty_list}},
%%%%
%%%%  true = is_subtype(S, T),
%%%%  false = is_subtype(S, Ti),
%%%%  false = is_subtype(T, Ti).
%%%%
%%%%nonempty_list_test() ->
%%%%  S = {empty_list},
%%%%  T = {nonempty_list, {singleton, hello}},
%%%%  Ti = {nonempty_improper_list, {singleton, hello}, {empty_list}},
%%%%
%%%%  false = is_subtype(S, T),
%%%%  false = is_subtype(S, Ti),
%%%%  true = is_subtype(T, Ti).
%%%%
%%%%number_list_test() ->
%%%%  T = {list, stdtypes:tunion([{predef, integer}, {predef, float}])},
%%%%  S = {list, stdtypes:tunion([{predef, integer}])},
%%%%
%%%%  true = is_subtype(S, T),
%%%%  false = is_subtype(T, S).
%%%%
%%%%simple_predef_alias_test() ->
%%%%  S = {predef_alias, term},
%%%%  true = is_subtype(S, S),
%%%%  ok.
%%%%
%%%%
%%%%
%%%%noloc() -> {loc, "no", 0, 0}.
%%%%named(Ref, Args) ->
%%%%  {named, noloc(), {ref, Ref, length(Args)}, Args}.
%%%%
%%%%
%%%%predefSymbolicTable() ->
%%%%  Scheme = stdtypes:tyscm([a],
%%%%    tunion([
%%%%      a('[]'),
%%%%      ttuple([tvar(a), named(ulist, [tvar(a)])])
%%%%    ])
%%%%  ),
%%%%  List = {attribute, noloc(), type, transparent, {ulist, Scheme}},
%%%%
%%%%  UnevenScheme = stdtypes:tyscm([a],
%%%%    tunion([
%%%%      ttuple([tvar(a), a('[]')]),
%%%%      ttuple([tvar(a), ttuple([tvar(a), named(uneven_ulist, [tvar(a)])])])
%%%%    ])
%%%%  ),
%%%%  UnevenList = {attribute, noloc(), type, transparent, {uneven_ulist, UnevenScheme}},
%%%%
%%%%  EvenScheme = stdtypes:tyscm([a],
%%%%    tunion([
%%%%      a('[]'),
%%%%      ttuple([tvar(a), ttuple([tvar(a), named(even_ulist, [tvar(a)])])])
%%%%    ])
%%%%  ),
%%%%  EvenList = {attribute, noloc(), type, transparent, {even_ulist, EvenScheme}},
%%%%
%%%%  % user-defined list :: µx.(α×x) ∨ nil
%%%%  % user-defined even list :: µx.(α×(α×x)) ∨ nil
%%%%  % user-defined uneven list :: µx.(α×(α×x)) ∨ (α×nil)
%%%%  symtab:extend_symtab([List, EvenList, UnevenList], symtab:empty()).
%%%%
%%%%
%%%%a(A, B) -> {fun_full, [A], B}.
%%%%b(A) -> stdtypes:a(A).
%%%%n(A) -> stdtypes:tnegate(A).
%%%%u(A,B) -> stdtypes:tunion([A,B]).
%%%%i(A,B) -> stdtypes:tintersect([A,B]).
%%%%v(A) -> stdtypes:tvar(A).
%%%%p(A, B) -> ttuple([A, B]).
%%%%
%%%%
%%%%
%%%%
%%%%bug1_test() ->
%%%%  O = {intersection,
%%%%    [{union,
%%%%         [{intersection,
%%%%              [{negation,{tuple,[{singleton,a}]}},
%%%%               {tuple,
%%%%                   [{intersection,
%%%%                        [{intersection,
%%%%                             [{negation,{singleton,a}},{singleton,b}]},
%%%%                         {union,
%%%%                             [{intersection,
%%%%                                  [{negation,{singleton,a}},{singleton,b}]},
%%%%                              {intersection,
%%%%                                  [{singleton,a},{singleton,b}]}]}]}]}]},
%%%%          {tuple,
%%%%              [{intersection,
%%%%                   [{intersection,[{singleton,a},{singleton,b}]},
%%%%                    {union,
%%%%                        [{intersection,
%%%%                             [{negation,{singleton,a}},{singleton,b}]},
%%%%                         {intersection,[{singleton,a},{singleton,b}]}]}]}]}]},
%%%%     {intersection,[{tuple,[{singleton,a}]},{tuple,[{predef,any}]}]}]},
%%%%
%%%%  O2 = {intersection,
%%%%    [
%%%%      {tuple, [{singleton,b}]},
%%%%      {tuple,[{singleton,a}]}
%%%%    ]},
%%%%
%%%%  O3 = {predef, none},
%%%%
%%%%  true = is_equiv(O, O2),
%%%%  true = is_equiv(O2, O3),
%%%%
%%%%  ok.
%%%%
%%%%empty_tuple_test() ->
%%%%  O2 = {intersection,
%%%%    [
%%%%      {tuple, [{singleton,b}]},
%%%%      {tuple,[{singleton,a}]}
%%%%    ]},
%%%%
%%%%  true = subty:is_empty(O2, none),
%%%%
%%%%  ok.
%%%%
%%%%
%%%%is_equiv(S, T) ->
%%%%  subty:is_subty(none, S, T) andalso
%%%%    subty:is_subty(none, T, S).
%%%%
%%%%is_subtype(S, T) ->
%%%%  subty:is_subty(none, S, T).
%%%%
%%%%
%%%%
%%%%
%%%%
%%%%
%%%%  simple_tuple3_test() ->
%%%%    S = {tuple, [{predef, atom}]},
%%%%    Snorm = ty_rec:norm(S),
%%%%    Seval = ty_rec:eval(Snorm),
%%%%
%%%%    true = is_equiv(S, Seval).
%%%%
%%%%  simple_any_test() ->
%%%%    S = {negation,{union,[{singleton,f}]}},
%%%%    Snorm = ty_rec:norm(S),
%%%%    Seval = ty_rec:eval(Snorm),
%%%%
%%%%    true = is_equiv(S, Seval).
%%%%
%%%%  simple_predef_test() ->
%%%%    S = {negation,{tuple,[{predef,atom}]}},
%%%%    Snorm = ty_rec:norm(S),
%%%%    Seval = ty_rec:eval(Snorm),
%%%%
%%%%    true = is_equiv(S, Seval).