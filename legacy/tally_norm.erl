-module(tally_norm).

%%norm_single_partition({{P, []}, {N, []}}, Memo, Fix, Sym) ->
%%  SimpleSubty = fun(Pp, Nn) -> case subty:is_subty(Sym, stdtypes:tintersect(Pp), stdtypes:tunion(Nn)) of true -> [[]]; _    -> [] end end,
%%
%%  case P of
%%    [] -> []; % unsatisfiable constraints
%%    % === ATOMS & INTS & special
%%    [A | _] when
%%      A == {predef, atom};
%%      A == {predef, integer};
%%      A == {predef, float};
%%      A == {empty_list} ->
%%      SimpleSubty(P, N);
%%    [{singleton, Atom} | _] when is_atom(Atom); is_integer(Atom) -> SimpleSubty(P, N);
%%    [{range, _,_} | _] -> SimpleSubty(P, N);
%%    [{left, _} | _] -> SimpleSubty(P, N);
%%    [{right, _} | _] -> SimpleSubty(P, N);
%%
%%    % empty tuples can be decided immediately, like atoms
%%    [{tuple, []} | _Ps] ->
%%      case [Z || Z <- N, is_ttuple(Z, 0)] of
%%        [] -> []; % not empty, unsatisfiable
%%        [{tuple, []}] -> [[]] % empty, satisfiable
%%      end;
%%
%%    % === LIST A B
%%    [{improper_list, _, _} | _Ps] ->
%%      FilteredNegativeAtoms = lists:filter(fun stdtypes:is_tlist/1, N),
%%      norm_list(P, FilteredNegativeAtoms, Memo, Fix, Sym);
%%
%%
%%    [{tuple, L} | _Ps] ->
%%      norm_tuple(length(L), P, [X || X <- N, is_ttuple(X, length(L))], Memo, Fix, Sym)
%%    ;
%%
%%    [{fun_full, C, _} | _Ps] ->
%%      norm_fun_full(length(C), P, [X || X <- N, is_tfun_full(X, length(C))], Memo, Fix, Sym);
%%
%%    [Pp | _Ps] ->
%%      logger:debug("Unhandled normalization of atom type:~n~p", [Pp]),
%%      throw(todo)
%%  end;
%%
%%norm_fun_full(_Length, _Ps, [], _Memo, _, _Sym) -> []; % not empty
%%norm_fun_full(Length, Ps, [{fun_full, NDomains, NCodomain} | Ns], Memo, Fix, Sym) ->
%%  % treat multi argument as tuple
%%  NDomainsTuple = {tuple, NDomains},
%%
%%  PDomainsTuple = {union, [{tuple, Domains} || {fun_full, Domains, _} <- Ps]},
%%
%%  Tx = tintersect([NDomainsTuple, tnegate(PDomainsTuple)]),
%%  CounterExample = fun() -> norm_and_merge(Tx, Memo, Fix, Sym) end,
%%
%%  Others = fun() -> norm_fun_full_explore(NDomainsTuple, stdtypes:tnegate(NCodomain), Ps, Memo, Fix, Sym) end,
%%  Con1 = lazy_meet(CounterExample, Others, Sym),
%%
%%  % if not, continue searching for another arrow in N
%%  FullSearch = fun() -> norm_fun_full(Length, Ps, Ns, Memo, Fix, Sym) end,
%%
%%  lazy_join(Con1, FullSearch, Sym).
%%
%%norm_fun_full_explore(NDomains, NCodomain, [], Memo, Fix, Sym) ->
%%  Con1 = fun() -> norm_and_merge(NDomains, Memo, Fix, Sym) end,
%%  Con2 = fun() -> norm_and_merge(NCodomain, Memo, Fix, Sym) end,
%%  lazy_join(Con1, Con2, Sym);
%%
%%norm_fun_full_explore(NDomains, NCodomain, [{fun_full, From, S2} | P], Memo, Fix, Sym) ->
%%
%%  S1 = {tuple, From},
%%  Tx1 = tintersect([NDomains, tnegate(S1)]),
%%  OptCon1 = fun() -> norm_and_merge(Tx1, Memo, Fix, Sym) end,
%%
%%  BigIntersectionCoDomain = {intersection, [CoDomain || {fun_full, _, CoDomain} <- P]},
%%  Tx2 = tintersect([BigIntersectionCoDomain, NCodomain]),
%%  OptCon2 = fun() -> norm_and_merge(Tx2, Memo, Fix, Sym) end,
%%  OptCon = lazy_join(OptCon1, OptCon2, Sym),
%%
%%  Con1 = fun() -> norm_fun_full_explore(NDomains, tintersect([S2, NCodomain]), P, Memo, Fix, Sym) end,
%%  Con2 = fun() -> norm_fun_full_explore(Tx1, NCodomain, P, Memo, Fix, Sym) end,
%%
%%  Res = lazy_meet(OptCon, Con1, Sym),
%%  lazy_meet(Res, Con2, Sym).
%%
%%
%%norm_tuple(Length, Ps, Ns, Memo, Fix, Sym) ->
%%  % T_i intersections
%%  T_is = [ {intersection, [lists:nth(Index, Components) || {tuple, Components} <- Ps]} || Index <- lists:seq(1, Length) ],
%%
%%
%%  % either all n-components (of Ps) are equated to empty for every n
%%  EmptynessPosComponents = lists:foldl(fun(Tx, Res) ->
%%    Con1 = fun() -> norm_and_merge(Tx, Memo, Fix, Sym) end,
%%    lazy_join(Res, Con1, Sym)
%%              end, [], T_is),
%%
%%
%%  % or explore all possibilities of negated Ns
%%  ExploreConstraints = fun() -> norm_tuple_explore(Length, T_is, Ns, Memo, Fix, Sym) end,
%%  lazy_join(EmptynessPosComponents, ExploreConstraints, Sym).
%%
%%
%%
%%norm_tuple_explore(_Length, _T_is, [], _Memo, _Fix, _Sym) -> [];
%%norm_tuple_explore(Length, T_is, [{tuple, N} | Ns], Memo, Fix, Sym) ->
%%  GenerateEmptynessConstraints = fun
%%                                   (_, []) -> [];
%%                                   ({Index, {PComponent, NComponent}}, Result) ->
%%                                     % either P & !N is empty at index i
%%
%%                                     TiCap = tintersect([PComponent, tnegate(NComponent)]),
%%                                     TiCon1 = fun() -> norm_and_merge(TiCap, Memo, Fix, Sym) end,
%%
%%                                     % OR
%%                                     % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
%%                                     ExploreCons = begin
%%                                                     DoDiff = fun({IIndex, PComp}) ->
%%                                                       case IIndex of
%%                                                         Index ->
%%                                                           tintersect([PComp, tnegate(NComponent)]);
%%                                                         _ ->
%%                                                           PComp
%%                                                       end
%%                                                              end,
%%                                                     NewPs = lists:map(DoDiff, lists:zip(lists:seq(1, length(T_is)), T_is)),
%%                                                     fun() -> norm_tuple_explore(Length, NewPs, Ns, Memo, Fix, Sym) end
%%                                                   end,
%%
%%
%%                                     UnionResult = lazy_join(TiCon1, ExploreCons, Sym),
%%                                     lazy_meet(Result, UnionResult, Sym)
%%                                 end,
%%
%%  lists:foldl(GenerateEmptynessConstraints, [[]], lists:zip(lists:seq(1, Length), lists:zip(T_is, N))).
%%
%%norm_list(Ps, Ns, Memo, Fix, Sym) ->
%%  T1 = {intersection, [X || {improper_list, X, _} <- Ps]},
%%  T2 = {intersection, [X || {improper_list, _, X} <- Ps]},
%%  Cons1 = fun() -> norm_and_merge(T1, Memo, Fix, Sym) end,
%%  Cons2 = fun() -> norm_and_merge(T2, Memo, Fix, Sym) end,
%%
%%  Con0 = fun() -> norm_list_ext(T1, T2, Ns, Memo, Fix, Sym) end,
%%
%%  Comps = lazy_join(Cons1, Cons2, Sym),
%%  lazy_join(Comps, Con0, Sym).
%%
%%norm_list_ext(_T1, _T2, [], _Memo, _, _Sym) -> [];
%%norm_list_ext(T1, T2, [{improper_list, S1, S2} | Ns], Memo, Fix, Sym) ->
%%  T1Cap = tintersect([T1, tnegate(S1)]),
%%  T2Cap = tintersect([T2, tnegate(S2)]),
%%
%%  Con1 = fun() -> norm_and_merge(T1Cap, Memo, Fix, Sym) end,
%%  Con10 = fun() -> norm_list_ext(T1Cap, T2, Ns, Memo, Fix, Sym) end,
%%  Con11 = lazy_join(Con1, Con10, Sym),
%%
%%  Con22 = fun() ->
%%    Con2 = fun() -> norm_and_merge(T2Cap, Memo, Fix, Sym) end,
%%    Con20 = fun() -> norm_list_ext(T1, T2Cap, Ns, Memo, Fix, Sym) end,
%%    lazy_join(Con2, Con20, Sym)
%%          end,
%%
%%  lazy_meet(Con11, Con22, Sym).