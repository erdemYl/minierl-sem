-module(ty_rec).
-vsn({1,1,0}).

-behavior(type).
-export([empty/0, any/0]).
-export([union/2, negate/1, intersect/2, diff/2, is_any/1]).
-export([is_empty/1, eval/1]).

% additional type constructors
-export([variable/1, interval/1, tuple/1]).

-export([is_subtype/2]).

-record(ty, {interval, tuple}).

-type ty_ref() :: {ty_ref, integer()}.
-type interval() :: term().
-type ty_tuple() :: term().
-type ty_variable() :: term().


% ======
% top-level API
% ======

is_subtype(TyRef1, TyRef2) ->
  NewTy = intersect(TyRef1, ty_rec:negate(TyRef2)),
  is_empty(NewTy).

% ======
% Type constructors
% ======

-spec empty() -> ty_ref().
empty() ->
  ty_ref:store(#ty{interval = dnf_var_int:empty(), tuple = dnf_var_ty_tuple:empty()}).

-spec any() -> ty_ref().
any() ->
  ty_ref:any().

-spec variable(ty_variable()) -> ty_ref().
variable(Var) ->
  Any = ty_ref:load(any()),

  ty_ref:store(Any#ty{
    interval = dnf_var_int:intersect(Any#ty.interval, dnf_var_int:var(Var)),
    tuple = dnf_var_ty_tuple:intersect(Any#ty.tuple, dnf_var_ty_tuple:var(Var))
  }).

-spec interval(interval()) -> ty_ref().
interval(Interval) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ interval = Interval }).

-spec tuple(ty_tuple()) -> ty_ref().
tuple(Tuple) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = Tuple }).

% ======
% Boolean operations
% ======

-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(TyRef1, TyRef2) ->
  #ty{interval = I1, tuple = P1} = ty_ref:load(TyRef1),
  #ty{interval = I2, tuple = P2} = ty_ref:load(TyRef2),
  ty_ref:store(#ty{
    interval = dnf_var_int:intersect(I1, I2),
    tuple = dnf_var_ty_tuple:intersect(P1, P2)
  }).

-spec negate(ty_ref()) -> ty_ref().
negate(TyRef1) ->
  #ty{interval = I1, tuple = P1} = ty_ref:load(TyRef1),
  ty_ref:store(#ty{
    interval = dnf_var_int:negate(I1),
    tuple = dnf_var_ty_tuple:negate(P1)
  }).

-spec diff(ty_ref(), ty_ref()) -> ty_ref().
diff(A, B) -> intersect(A, negate(B)).

-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(A, B) -> negate(intersect(negate(A), negate(B))).









%%
%%
%%eval(#ty{atoms = At, ints = I, special = S, list = L, prod = {DefP, P}, arrw = {DefA, A}}) ->
%%  {union, [
%%    {intersection, [{predef, atom}, bdd_lazy:eval(At)]},
%%    {intersection, [{predef, integer}, bdd_lazy:eval(I)]},
%%    {intersection, [stdtypes:tspecial_any(), bdd_lazy:eval(S)]},
%%    {intersection, [stdtypes:tlist_any(), bdd_lazy:eval(L)]},
%%    {union, eval_inf_union(DefP, P, fun stdtypes:ttuple_n/1, {tuple_any})},
%%    {union, eval_inf_union(DefA, A, fun stdtypes:tarrow_n/1, {fun_simple})}
%%  ]}.
%%
%%eval_inf_union({bdd, 0}, Explicit, AnyNGenerator, _) ->
%%  Eval = fun({Length, Tuple}) ->
%%    {intersection, [AnyNGenerator(Length), bdd_lazy:eval(Tuple)]}
%%         end,
%%  lists:map(Eval, maps:to_list(Explicit));
%%eval_inf_union(Default, A, AnyNGenerator, TopType) ->
%%  Others = {union, eval_inf_union({bdd, 0}, A, AnyNGenerator, TopType)},
%%  % others union with ((any -> T) function WITHOUT any (n -> T)-functions which are already captured by Others)
%%  OtherNAny = [{negation, AnyNGenerator(N)} || N <- maps:keys(A)],
%%  [Others, {intersection, [TopType] ++ OtherNAny ++ [bdd_lazy:eval(Default)]}].
%%
%%multi_union({DefaultT1, T1}, {DefaultT2, T2}) ->
%%  % get all keys
%%  AllKeys = maps:keys(T1) ++ maps:keys(T2),
%%  IntersectKey = fun(Key) ->
%%    bdd_lazy:union(
%%      maps:get(Key, T1, DefaultT1),
%%      maps:get(Key, T2, DefaultT2)
%%    )
%%                 end,
%%  {bdd_lazy:union(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.
%%
%%multi_intersect({DefaultT1, T1}, {DefaultT2, T2}) ->
%%  % get all keys
%%  AllKeys = maps:keys(T1) ++ maps:keys(T2),
%%  IntersectKey = fun(Key) ->
%%    bdd_lazy:intersect(
%%      maps:get(Key, T1, DefaultT1),
%%      maps:get(Key, T2, DefaultT2)
%%    )
%%    end,
%%  {bdd_lazy:intersect(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.
%%
%%multi_diff({DefaultT1, T1}, {DefaultT2, T2}) ->
%%  % all on left side
%%  M1 = maps:map(fun(Length, BddT1) ->
%%    Other = maps:get(Length, T2, DefaultT2),
%%    bdd_lazy:diff(BddT1, Other)
%%           end, T1),
%%
%%  % rest on right side that are not in left side
%%  M2_orig = maps:filter(fun(Length, _) -> not maps:is_key(Length, M1) end, T2),
%%  M2 = maps:map(fun(_Length, Bdd) ->
%%    bdd_lazy:diff(DefaultT1, Bdd)
%%                end, M2_orig),
%%
%%  % M1 and M2 are disjunct
%%  {bdd_lazy:diff(DefaultT1, DefaultT2), maps:merge(M1, M2)}.
%%
%%
%%
%%
%%
%%% ===========================
%%% BDD set-theoretic predicates
%%% ==================
%%
%%% ===============
%%% emptiness check
%%is_empty(SnT, Symtab, Memo) ->
%%  Memoized = fun (Type, M, Fun) ->
%%    case sets:is_element(Type, M) of
%%      true ->
%%        true;
%%      _ ->
%%        NewMemo = sets:add_element(Type, M),
%%        Fun(NewMemo)
%%    end
%%             end,
%%
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               ATOMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%%intersected with empty is always empty
%%is_empty_atoms({bdd, 0}, _P, _N, _) -> true;
%%is_empty_atoms({bdd, 1}, P, N, _) ->
%%  PAtoms = case P of [] -> rep_basic:any(); _ -> rep_basic:finite(P) end,
%%  NAtoms = case N of [] -> rep_basic:any(); _ -> rep_basic:cofinite(N) end,
%%  I = rep_basic:intersect(PAtoms, NAtoms),
%%  rep_basic:is_empty(I);
%%
%%% explore DNF branches
%%is_empty_atoms({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, P, N, Sym) ->
%%  Ty = find_ty(Ref, Args, atom, Sym),
%%  is_empty_atoms(bdd_lazy:intersect(Left, Ty), P, N, Sym)
%%    andalso is_empty_atoms(Middle, P, N, Sym)
%%    andalso is_empty_atoms(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), P, N, Sym);
%%% reduces to containment without variables
%%is_empty_atoms({bdd, {bdd_var, _Var}, Left, Middle, Right}, P, N, Sym) ->
%%  is_empty_atoms(Left, P, N, Sym)
%%    andalso is_empty_atoms(Middle, P, N, Sym)
%%    andalso is_empty_atoms(Right, P, N, Sym);
%%is_empty_atoms({bdd, {bdd_atom, Atom}, Left, Middle, Right}, P, N, Sym) ->
%%  is_empty_atoms(Left, P ++ [Atom], N, Sym)
%%    andalso is_empty_atoms(Middle, P, N, Sym)
%%    andalso is_empty_atoms(Right, P, N ++ [Atom], Sym).
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               SPECIAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%%intersected with empty is always empty
%%is_empty_special({bdd, 0}, _P, _N, _) -> true;
%%is_empty_special({bdd, 1}, P, N, _) ->
%%  Ps = lists:usort(P),
%%  Ns = lists:usort(N),
%%
%%  length(Ps) > 1
%%    orelse
%%  length(Ns) == 5 % pid port ref float []
%%  orelse
%%    (length(Ps) == 1 andalso lists:member(lists:nth(1, Ps), Ns));
%%
%%% explore DNF branches
%%is_empty_special({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, P, N, Sym) ->
%%  Ty = find_ty(Ref, Args, spec, Sym),
%%  is_empty_special(bdd_lazy:intersect(Left, Ty), P, N, Sym)
%%    andalso is_empty_special(Middle, P, N, Sym)
%%    andalso is_empty_special(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), P, N, Sym);
%%% reduces to containment without variables
%%is_empty_special({bdd, {bdd_var, _Var}, Left, Middle, Right}, P, N, Sym) ->
%%  is_empty_special(Left, P, N, Sym)
%%    andalso is_empty_special(Middle, P, N, Sym)
%%    andalso is_empty_special(Right, P, N, Sym);
%%is_empty_special({bdd, {bdd_spec, Atom}, Left, Middle, Right}, P, N, Sym) ->
%%  is_empty_special(Left, P ++ [Atom], N, Sym)
%%    andalso is_empty_special(Middle, P, N, Sym)
%%    andalso is_empty_special(Right, P, N ++ [Atom], Sym).
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               TUPLES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%is_empty_multi_prod({{bdd, 1}, _}, _PVar, _NVar, _Symtab, _Memo) -> false;
%%% TODO I *think* multi-product resolves to the case without variables
%%is_empty_multi_prod({{bdd, 0}, Tuples}, _PVar, _NVar, Symtab, Memo) ->
%%  IsNTupleEmpty = fun
%%                    (_, _, false) -> false;
%%                    (Length, Bdd, _) ->
%%                      is_empty_n_prod(Length, Bdd, Symtab, Memo)
%%                    end,
%%  maps:fold(IsNTupleEmpty, true, Tuples);
%%is_empty_multi_prod({{bdd, {bdd_var, Var}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
%%  is_empty_multi_prod({L, T}, PVar ++ [Var], NVar, Symtab, Memo)
%%    andalso is_empty_multi_prod({M, T}, PVar, NVar, Symtab, Memo)
%%    andalso is_empty_multi_prod({R, T}, PVar, NVar ++ [Var], Symtab, Memo);
%%is_empty_multi_prod({{bdd, {bdd_named, {Ref, Args}}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
%%  {ok, Ty} = symtab:find_ty(Ref, Symtab),
%%  ActualTy = replace(Ty, Args),
%%  Only = pi(prod_default, norm(ActualTy)),
%%
%%  %% non-default products need to be included in their respective partitions
%%  {_, More} = (norm(ActualTy))#ty.prod,
%%  Keys = lists:usort(maps:keys(More) ++ maps:keys(T)),
%%
%%  % for a key
%%  NewT = maps:from_list([{Key,
%%      bdd_lazy:intersect(
%%        % Default is not ANY!
%%        % if tuple is not contained in current mapping, use default value mapping!
%%        maps:get(Key, T, L),
%%        maps:get(Key, More, bdd_lazy:any())
%%      )
%%  } || Key <- Keys]),
%%
%%  NewNegT = maps:from_list([{Key, bdd_lazy:intersect(
%%    maps:get(Key, T, R),
%%    bdd_lazy:negate(maps:get(Key, More, bdd_lazy:any()))
%%  )} || Key <- Keys]),
%%
%%  is_empty_multi_prod({bdd_lazy:intersect(L, Only), NewT}, PVar, NVar, Symtab, Memo)
%%    andalso
%%    is_empty_multi_prod({M, T}, PVar, NVar, Symtab, Memo)
%%    andalso
%%    is_empty_multi_prod({bdd_lazy:intersect(R, bdd_lazy:negate(Only)), NewNegT}, PVar, NVar, Symtab, Memo)
%%.
%%
%%is_empty_n_prod(Length, Bdd, Symtab, Memo) ->
%%  is_empty_prod(Length, Bdd, [ty_rec:any() || _ <- lists:seq(1, Length)], [], [], [], Symtab, Memo).
%%
%%is_empty_prod(_Length, {bdd, 0}, _Ps, _PVar, _NVar, _Ns, _SymTab, _Memo) -> true;
%%is_empty_prod(_Length, {bdd, 1}, PositiveComponents, [], [], N, SymTab, Memo) ->
%%  % no more variables
%%  % assertion
%%  Length = length(PositiveComponents),
%%
%%  PositivesEmpty = lists:foldl(fun(Element, Result) -> Result orelse ty_rec:is_empty(Element, SymTab, Memo) end, false, PositiveComponents),
%%  PositivesEmpty orelse explore_tuple(Length, PositiveComponents, N, SymTab, Memo);
%%is_empty_prod(Length, {bdd, 1}, Ps, PVars, [Var | NVars], N, SymTab, Memo) ->
%%  logger:debug("Removing negative variable from product clause: substitute in both positive and negative tuples:~n !~p => ~p", [Var, Var]),
%%
%%  Map = #{ Var => stdtypes:tnegate(Var) },
%%
%%  PsWithoutNegativeVars = [ substitute_bdd(Map, P) || P <- Ps ],
%%  NsWithoutNegativeVars = [ {bdd_tuple, [substitute_bdd(Map, P) || P <- Components ]}
%%    || {bdd_tuple, Components} <- N ],
%%
%%  is_empty_prod(Length, {bdd, 1}, PsWithoutNegativeVars, PVars, NVars, NsWithoutNegativeVars, SymTab, Memo);
%%is_empty_prod(Length, {bdd, 1}, Ps, [StdVar | PVars], [], N, SymTab, Memo) ->
%%  logger:debug("Removing positive variable from product clause~nsubstitute toplevel positive: ~n~p => (y1..yn)~nsubstitute negative and positive components: ~n~p => (y1..yn) U ~p", [StdVar, StdVar, StdVar]),
%%
%%  FreshVars = [fresh_variable(StdVar) || _ <- lists:seq(1, Length) ],
%%  SubstitutionStdMap = #{StdVar => stdtypes:tunion([StdVar, stdtypes:ttuple(FreshVars)]) },
%%
%%  SubstitutedPositiveTupleComponents = [substitute_bdd(SubstitutionStdMap, C) || C <- Ps],
%%
%%  % covariance of tuples: intersect positives with (y1..yn)
%%  FinishedPosTuple = [intersect(norm(Var), C)|| {Var, C} <- lists:zip(FreshVars, SubstitutedPositiveTupleComponents)],
%%
%%  NNoVars = [ {bdd_tuple, [substitute_bdd(SubstitutionStdMap, C) || C <- Components]}
%%    || {bdd_tuple, Components} <- N ],
%%
%%  % continue removing positive variables
%%  is_empty_prod(Length, {bdd, 1}, FinishedPosTuple, PVars, [], NNoVars, SymTab, Memo);
%%
%%is_empty_prod(Length, {bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, Ps, PVar, NVar, N, SymTab, Memo) ->
%%  Ty = find_ty(Ref, Args, {prod, Length}, SymTab),
%%
%%  is_empty_prod(Length, bdd_lazy:intersect(Left, Ty),   Ps, PVar, NVar, N, SymTab, Memo) andalso
%%    is_empty_prod(Length, Middle, Ps, PVar, NVar, N, SymTab, Memo) andalso
%%    is_empty_prod(Length, bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)),  Ps, PVar, NVar, N, SymTab, Memo);
%%% collecting variables
%%is_empty_prod(Length, {bdd, {bdd_var, Var}, Left, Middle, Right}, Ps, PVar, NVar, N, SymTab, Memo) ->
%%  is_empty_prod(Length, Left,   Ps, PVar ++ [stdtypes:tvar(Var)], NVar, N, SymTab, Memo) andalso
%%    is_empty_prod(Length, Middle, Ps, PVar, NVar, N, SymTab, Memo) andalso
%%    is_empty_prod(Length, Right,  Ps, PVar, NVar ++ [stdtypes:tvar(Var)], N, SymTab, Memo);
%%is_empty_prod(Length, {bdd, {bdd_tuple, BddComponents}, Left, Middle, Right}, Ps, PVar, NVar, N, SymTab, Memo) ->
%%  %% norming
%%  PsExtended = [ty_rec:intersect(ToIntersect, Others) || {ToIntersect, Others} <- lists:zip(BddComponents, Ps)],
%%
%%  is_empty_prod(Length, Left,   PsExtended, PVar, NVar, N, SymTab, Memo) andalso
%%  is_empty_prod(Length, Middle, Ps, PVar, NVar, N, SymTab, Memo) andalso
%%  is_empty_prod(Length, Right,  Ps, PVar, NVar, N ++ [{bdd_tuple, BddComponents}], SymTab, Memo).
%%
%%explore_tuple(_L, _Ps, [], _Symtab, _Memo) -> false;
%%explore_tuple(L, Ps, [{bdd_tuple, NegativeBddComponents} | N], Symtab, Memo) ->
%%  Solve = fun({Index, {PComponent, NComponent}}, Result) ->
%%    Result
%%      andalso
%%      begin
%%        subty:is_subty_bdd(PComponent, NComponent, Symtab, Memo)
%%          orelse
%%          % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
%%        begin
%%          DoDiff = fun({IIndex, PComp}) ->
%%            case IIndex of
%%              Index -> ty_rec:diff(PComp, NComponent);
%%              _ -> PComp
%%            end
%%                   end,
%%          NewPs = lists:map(DoDiff, lists:zip(lists:seq(1, length(Ps)), Ps)),
%%          explore_tuple(L, NewPs, N, Symtab, Memo)
%%        end
%%      end
%%          end,
%%
%%
%%  lists:foldl(Solve, true, lists:zip(lists:seq(1, L), lists:zip(Ps, NegativeBddComponents))).
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%is_empty_multi_arrow({{bdd, 1}, _}, _PVar, _NVar, _Symtab, _Memo) -> false;
%%% TODO I *think* multi-arrow resolves to the case without variables
%%is_empty_multi_arrow({{bdd, 0}, Arrows}, _PVar, _NVar, Symtab, Memo) ->
%%  IsNArrowEmpty = fun
%%                    (_, _, false) -> false;
%%                    (Length, Bdd, _) ->
%%                      is_empty_n_arrow(Length, Bdd, Symtab, Memo)
%%                  end,
%%  maps:fold(IsNArrowEmpty, true, Arrows);
%%is_empty_multi_arrow({{bdd, {bdd_var, Var}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
%%  is_empty_multi_arrow({L, T}, PVar ++ [Var], NVar, Symtab, Memo)
%%    andalso is_empty_multi_arrow({M, T}, PVar, NVar, Symtab, Memo)
%%    andalso is_empty_multi_arrow({R, T}, PVar, NVar ++ [Var], Symtab, Memo);
%%is_empty_multi_arrow({{bdd, {bdd_named, {Ref, Args}}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
%%  {ok, Ty} = symtab:find_ty(Ref, Symtab),
%%  ActualTy = replace(Ty, Args),
%%  Only = pi(arrw_default, norm(ActualTy)),
%%
%%  %% non-default arrows need to be included in their respective partitions
%%  {_, More} = (norm(ActualTy))#ty.arrw,
%%  Keys = lists:usort(maps:keys(More) ++ maps:keys(T)),
%%
%%  % for a key
%%  NewT = maps:from_list([{Key, bdd_lazy:intersect(
%%    % Default is not ANY!
%%    % if tuple is not contained in current mapping, use default value mapping!
%%    maps:get(Key, T, L),
%%    maps:get(Key, More, bdd_lazy:any())
%%  )} || Key <- Keys]),
%%
%%  NewNegT = maps:from_list([{Key, bdd_lazy:intersect(
%%    maps:get(Key, T, R),
%%    bdd_lazy:negate(maps:get(Key, More, bdd_lazy:any()))
%%  )} || Key <- Keys]),
%%
%%  is_empty_multi_arrow({bdd_lazy:intersect(L, Only), NewT}, PVar, NVar, Symtab, Memo)
%%    andalso is_empty_multi_arrow({M, T}, PVar, NVar, Symtab, Memo)
%%    andalso is_empty_multi_arrow({bdd_lazy:intersect(R, bdd_lazy:negate(Only)), NewNegT}, PVar, NVar, Symtab, Memo).
%%
%%is_empty_n_arrow(Length, Bdd, Symtab, Memo) ->
%%  is_empty_arrow(Length, Bdd, ty_rec:empty(), [], [], [], [], Symtab, Memo).
%%
%%is_empty_arrow(_Length, {bdd, 0}, _STys, _P, _N, _PVars, _NVars, _SymTab, _Memo) -> true;
%%is_empty_arrow(Length, {bdd, 1}, STys, P, N, PVars, [Var | NVars], SymTab, Memo) ->
%%  logger:debug("Removing negative variable from fun clause: substitute in both positive and negative funs:~n !~p => ~p", [Var, Var]),
%%
%%  Map = #{ Var => stdtypes:tnegate(Var) },
%%  SWithoutNeg = substitute_bdd(Map, STys),
%%
%%  PWithoutNeg =
%%    [ {bdd_fun_full, [substitute_bdd(Map, C) || C <- Components ], substitute_bdd(Map, Ret)}
%%    || {bdd_fun_full, Components, Ret} <- P ],
%%
%%  NWithoutNeg =
%%    [ {bdd_fun_full, [substitute_bdd(Map, C) || C <- Components ], substitute_bdd(Map, Ret)}
%%      || {bdd_fun_full, Components, Ret} <- N ],
%%
%%  is_empty_arrow(Length, {bdd, 1}, SWithoutNeg, PWithoutNeg, NWithoutNeg, PVars, NVars, SymTab, Memo);
%%is_empty_arrow(Length, {bdd, 1}, STys, P, N, [Var | PVars], [], SymTab, Memo) ->
%%  logger:debug("Removing positive variable from tuple clause~nsubstitute toplevel positive: ~n~p", [STys]),
%%
%%  AnyArgs = [stdtypes:tany() || _ <- lists:seq(1, Length) ],
%%  % "alpha1"
%%  FreshArgVars = [fresh_variable(Var) || _ <- lists:seq(1, Length) ],
%%  % alpha2
%%  FreshRetVars = fresh_variable(Var),
%%
%%  % ========
%%  % PART 1
%%  % replace var by alpha1 -> alpha2 intersection
%%
%%  % substitution
%%  % alpha   =>  (alpha1 -> alpha2) U alpha
%%  Phi1 = #{ Var => stdtypes:tunion([stdtypes:tfun_full(FreshArgVars, FreshRetVars), Var]) },
%%
%%  % add alpha1 to union of domains
%%  T1 = tuple_of(FreshArgVars),
%%  NewS = ty_rec:union(T1, STys),
%%
%%  % substitute negative and positive funs
%%  NewPos = [ {bdd_fun_full, [substitute_bdd(Phi1, C) || C <- Components ], substitute_bdd(Phi1, Ret)}
%%    || {bdd_fun_full, Components, Ret} <- P ],
%%  NewNeg = [ {bdd_fun_full, [substitute_bdd(Phi1, C) || C <- Components ], substitute_bdd(Phi1, Ret)}
%%    || {bdd_fun_full, Components, Ret} <- N ],
%%
%%  % ========
%%  % PART 2
%%  % replace var by alpha1 -> alpha2 intersection
%%
%%  EleArrow = stdtypes:tintersect([
%%      stdtypes:tfun_full(FreshArgVars, FreshRetVars),
%%      stdtypes:tnegate(stdtypes:tfun_full(AnyArgs, stdtypes:tnone()))
%%    ]),
%%  % substitution
%%  % alpha   =>  [(alpha1 -> alpha2) \ (1 -> 0)] U alpha
%%  Phi2 = #{ Var => stdtypes:tunion([EleArrow , Var]) },
%%
%%  % add alpha1 to union of domains (alpha1 and empty set, so just alpha1)
%%  T2 = tuple_of(FreshArgVars),
%%  NewS2 = ty_rec:union(T2, STys),
%%
%%  % substitute negative and positive funs
%%  NewPos2 = [ {bdd_fun_full, [substitute_bdd(Phi2, C) || C <- Components ], substitute_bdd(Phi2, Ret)}
%%    || {bdd_fun_full, Components, Ret} <- P ],
%%  NewNeg2 = [ {bdd_fun_full, [substitute_bdd(Phi2, C) || C <- Components ], substitute_bdd(Phi2, Ret)}
%%    || {bdd_fun_full, Components, Ret} <- N ],
%%
%%  % both part 1 and part 2 have to hold
%%  is_empty_arrow(Length, {bdd, 1}, NewS, NewPos, NewNeg, PVars, [], SymTab, Memo)
%%    andalso
%%    is_empty_arrow(Length, {bdd, 1}, NewS2, NewPos2, NewNeg2, PVars, [], SymTab, Memo);
%%is_empty_arrow(_Length, {bdd, 1}, _STys, _P, [], [], [], _SymTab, _Memo) -> false;
%%% solve arrow without vars
%%is_empty_arrow(Length, {bdd, 1}, STyRec, PBddLazys, [{bdd_fun_full, NTs1, NT2} | NBddsLazy ], [], [], SymTab, Memo) ->
%%    (
%%        begin
%%          % treat multi argument as tuple
%%        FunTuple = tuple_of(NTs1),
%%
%%        %% ∃ NTys1 --> T2 ∈ N s.t.
%%        %%    NTys1 are in the domains of the function (as a tuple)
%%        %%    S is the union of all (tuple) domains of the positive function intersections
%%        subty:is_subty_bdd(FunTuple, STyRec, SymTab, Memo)
%%        end
%%          andalso
%%          explore_arrow(FunTuple, NT2, PBddLazys, ty_rec:empty(), ty_rec:any(), SymTab, Memo)
%%    )
%%      %% Continue searching for another arrow ∈ N
%%      orelse is_empty_arrow(Length, {bdd, 1}, STyRec, PBddLazys, NBddsLazy, [], [], SymTab, Memo);
%%
%%is_empty_arrow(Length, {bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, S, P, N, PVar, NVar, SymTab, Memo) ->
%%  Ty = find_ty(Ref, Args, {arrw, Length}, SymTab),
%%
%%  is_empty_arrow(Length, bdd_lazy:intersect(Left, Ty), S, P, N, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_arrow(Length, Middle, S, P, N, PVar, NVar, SymTab, Memo) andalso
%%    is_empty_arrow(Length, bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), S, P, N, PVar, NVar, SymTab, Memo);
%%is_empty_arrow(Length, {bdd, {bdd_var, Var}, Left, Middle, Right}, S, P, N, PVars, NVars, SymTab, Memo) ->
%%  is_empty_arrow(Length, Left, S, P, N, PVars ++ [stdtypes:tvar(Var)], NVars, SymTab, Memo) andalso
%%    is_empty_arrow(Length, Middle, S, P, N, PVars, NVars, SymTab, Memo) andalso
%%    is_empty_arrow(Length, Right, S, P, N, PVars, NVars  ++ [stdtypes:tvar(Var)], SymTab, Memo);
%%is_empty_arrow(Length, {bdd, Arrw = {bdd_fun_full, T1raw, _}, L, M, R}, S, P, N, PVars, NVars, SymTab, Memo) ->
%%  T1 = tuple_of(T1raw),
%%  is_empty_arrow(Length, L, ty_rec:union(S, T1), [Arrw] ++ P, N, PVars, NVars, SymTab, Memo)
%%    andalso is_empty_arrow(Length, M, S, P, N, PVars, NVars, SymTab, Memo)
%%    andalso is_empty_arrow(Length, R, S, P, [Arrw] ++ N, PVars, NVars, SymTab, Memo).
%%
%%explore_arrow(T1, T2, [], Domain, Codomain, SymTab, Memo) ->
%%  subty:is_subty_bdd(T1, Domain, SymTab, Memo) orelse subty:is_subty_bdd(Codomain, T2, SymTab, Memo);
%%explore_arrow(T1, T2, [{bdd_fun_full, S1raw, S2} | P], Domain, Codomain, SymTab, Memo) ->
%%  S1 = tuple_of(S1raw),
%%  explore_arrow(T1, T2, P, Domain, ty_rec:intersect(Codomain, S2), SymTab, Memo)
%%    andalso
%%    explore_arrow(T1, T2, P, ty_rec:union(Domain, S1), Codomain, SymTab, Memo).
%%
%%
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               UTILITY FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%substitute_bdd(StdMap, #ty{
%%  atoms = Atoms, special = S, list = Lists, ints = Ints, prod = {DefaultTuple, Tuples}, arrw = {DefaultFun, Funs}
%%}) ->
%%  % substitutions can introduce tuples and arrows which are currently not captured by (non-default) Tuples and Arrows
%%  % figure out what length to explicitly calculate with the DefaultTuple value to do an explicit substitution filtering
%%  % TODO do this only once
%%  ProdLengths = lists:usort(lists:flatten([begin Ty = norm(Target), #ty{prod = {_, Others}} = Ty, maps:keys(Others) end || {_V, Target} <- maps:to_list(StdMap)])),
%%  FunLengths = lists:usort(lists:flatten([begin Ty = norm(Target), #ty{arrw = {_, Others}} = Ty, maps:keys(Others) end || {_V, Target} <- maps:to_list(StdMap)])),
%%
%%
%%  % TODO smart ty constructor
%%  % whenever default Value matches the value in the tuple/fun map, remove the value in the tuple/fun map (redundant)
%%  #ty{
%%    atoms = bdd_lazy:substitute(atom, Atoms, StdMap),
%%    ints = bdd_lazy:substitute(ints, Ints, StdMap),
%%    special = bdd_lazy:substitute(spec, S, StdMap),
%%    list = bdd_lazy:substitute(list, Lists, StdMap),
%%    prod =
%%    {bdd_lazy:substitute(prod_default, DefaultTuple, StdMap),
%%      maps:merge(
%%        maps:from_list([{N, bdd_lazy:substitute({prod, N}, DefaultTuple, StdMap)} || N <- ProdLengths]),
%%        maps:map(fun(Length, V) -> bdd_lazy:substitute({prod, Length}, V, StdMap) end, Tuples) % this map supersedes the default value substitutions
%%      )
%%    },
%%    arrw =
%%    {bdd_lazy:substitute(arrw_default, DefaultFun, StdMap),
%%      maps:merge(
%%        maps:from_list([{N, bdd_lazy:substitute({arrw, N}, DefaultFun, StdMap)} || N <- FunLengths]),
%%        maps:map(fun(Length, V) -> bdd_lazy:substitute({arrw, Length}, V, StdMap) end, Funs) % this map supersedes the default value substitutions
%%      )
%%    }
%%  }.
%%
%%fresh_variable({Type, VariableName}) ->
%%  Uniq = erlang:unique_integer(),
%%  ToName = lists:takewhile(fun(E) -> not(E == $-) end, atom_to_list(VariableName)),
%%
%%  {Type,
%%    %% behold the universally feared dynamically created Erlang atom
%%    list_to_atom(
%%      ToName ++ erlang:integer_to_list(Uniq)
%%    )
%%  }.
%%
%%tuple_of(Components) ->
%%  Tuple = #{length(Components) => bdd_lazy:pos({bdd_tuple, Components})},
%%  (empty())#ty{prod = {bdd_lazy:empty(), Tuple}}.
%%
%%pi(atom, #ty{atoms = A}) -> A;
%%pi(ints, #ty{ints = A}) -> A;
%%pi(spec, #ty{special = A}) -> A;
%%pi(list, #ty{list = A}) -> A;
%%pi(prod_default, #ty{prod = {Default, _}}) -> Default;
%%pi(arrw_default, #ty{arrw = {Default, _}}) -> Default;
%%pi({prod, Length}, #ty{prod = {_, Prods}}) -> maps:get(Length, Prods);
%%pi({arrw, Length}, #ty{arrw = {_, Arrws}}) -> maps:get(Length, Arrws).
%%
%%find_ty(Ref, Args, Type, Sym) ->
%%  % 1: lookup
%%  {ok, Ty} = symtab:find_ty(Ref, Sym),
%%  % 2: replace ty scheme variables with argument variables
%%  ActualTy = replace(Ty, Args),
%%  % 3: norm and project out type
%%  pi(Type, norm(ActualTy)).
%%
%%replace({ty_scheme, Vars, Ty}, Args) ->
%%  Vs = [Name || {Name, _} <- Vars],
%%  Subst = maps:from_list(lists:zip(Vs, Args)),
%%  SubTy = subst:apply(Subst, Ty),
%%  SubTy.


is_empty(TyRef) ->
  % first try op-cache
  case ty_ref:is_empty_cached(TyRef) of
    R when R == true; R == false ->
      io:format(user, "Subty cache hit~n", []),
      R;
    miss ->
      ty_ref:store_is_empty_cached(TyRef, is_empty_miss(TyRef))
  end.

is_empty_miss(TyRef) ->
  io:format(user, "Not cached: ~p~n", [TyRef]),
  Ty = ty_ref:load(TyRef),
  A = dnf_var_int:is_empty(Ty#ty.interval),
  B = dnf_var_int:is_empty(Ty#ty.tuple),
  A andalso B.

%%  is_empty_atoms(SnT#ty.atoms, [], [], Symtab)
%%    andalso is_empty_special(SnT#ty.special, [], [], Symtab)
%%    andalso Memoized(SnT#ty.list, Memo, fun (NewMemo) -> is_empty_list(SnT#ty.list, any(), any(), [], [], [], Symtab, NewMemo) end)
%%    andalso Memoized(SnT#ty.arrw, Memo, fun (NewMemo) -> is_empty_multi_arrow(SnT#ty.arrw, [], [], Symtab, NewMemo) end).









% TODO implement witness
eval(_) ->
  erlang:error(eval_witness_not_implemented).


is_any(_Arg0) ->
  erlang:error(any_not_implemented). % TODO needed?