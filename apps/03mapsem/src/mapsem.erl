-module(mapsem).
-compile(nowarn_export_all).
-compile(export_all).

-define(MAN, mandatory).
-define(OPT, optional).
-define(LStep, {'L', integers}).
-define(LHatStep, {'LHat', integers}).

% Explain the aim of this map interpretation
% Find examples

% General type
-type ty() :: ty_ref() | ty_rec().
-type flag() :: integer().

-record(map, {
  ls = #{} :: labels(),
  st :: steps(),
  ns = {[], []} :: {ManNs :: names(), OptNs :: names()}
}).

% Map type
-type map() :: #map{}.
-type labels() :: #{flag() => field()}.
-type steps()  :: #{{index(), step()} := field()}.
-type names()  :: [atom()].


% Intrinsic data-structures
-type field() :: {assoc(), ty_ref()}.
-type step() :: integers.
-type index() :: 'L' | 'LHat'.
-type assoc() :: mandatory | optional.

-record(ty, { flag :: dnf(flag()), map :: dnf(map()) }).
-type ty_ref () :: fun(() -> ty()).
-type ty_rec () :: #ty{}.

-type memo() :: #{}.

-type dnf(Atom) :: [{[Atom], [Atom]}].


-spec flag(flag()) -> dnf(flag()).
flag(F) -> [{[F], []}].

-spec negated_flag(flag()) -> dnf(flag()).
negated_flag(F) -> [{[], [F]}].

% 0 U. !0 is any
-spec any_flag() -> dnf(flag()).
any_flag() -> [{[0], []}, {[], [0]}].

% 0 n !0 is empty
% Why not use the empty dnf representation []?
% Because negating any_flag() representation is equal to this.
-spec negated_any_flag() -> dnf(flag()).
negated_any_flag() -> [{[0], [0]}].


-spec map(map()) -> dnf(map()).
map(M) -> [{[M], []}].

-spec negated_map(map()) -> dnf(map()).
negated_map(M) -> [{[], [M]}].

-spec any_map() -> dnf(map()).
any_map() ->
  M = #map{  st = #{?LStep => {?OPT, any()}, ?LHatStep => {?OPT, any()}}  },
  [{[M], []}].

-spec negated_any_map() -> dnf(map()).
negated_any_map() ->
  M = #map{  st = #{?LStep => {?OPT, any()}, ?LHatStep => {?OPT, any()}}  },
  [{[], [M]}].


-spec ty(dnf(flag()), dnf(map())) -> ty_rec().
ty(Flag, Map) -> #ty{flag = Flag, map = Map}.

-spec ty_flag(dnf(flag())) -> ty_rec().
ty_flag(Flag) -> #ty{flag = Flag, map = negated_any_map()}.

-spec ty_map(dnf(map())) -> ty_rec().
ty_map(Map) -> #ty{flag = negated_any_flag(), map = Map}.


% Corecursive Top type:  Any = Z U { Z1 => Any, Z2 => Any }.
-spec any() -> ty().
any() -> fun Any() -> #ty{
  flag = any_flag(),
  map = map(#map{  st = #{?LStep => {?OPT, Any}, ?LHatStep => {?OPT, Any}}  })
} end.

% Empty := !Any = false U. !{ (1,Z) => Any, (2,Z) => Any }
-spec empty() -> ty().
empty() -> negate(any()).

-spec negate(ty_ref()) -> ty_ref().
negate(Ty) -> corec_ref(Ty, #{}, fun negate/2).

corec_ref(Corec, Memo, Continue) -> corec(Corec, Memo, Continue, reference).
corec_const(Corec, Memo, Continue, Const) -> corec(Corec, Memo, Continue, {const, Const}).


-spec corec
    ([ty_ref()], memo(), fun(([ty_rec()], memo()) -> ty_rec()), reference) -> ty_ref();
    ( ty_ref() , memo(), fun(( ty_rec() , memo()) -> ty_rec()), reference) -> ty_ref();
    ([ty_ref()], memo(), fun(([ty_rec()], memo()) -> ty_rec()), {const, Const}) -> Const;
    ( ty_ref() , memo(), fun(( ty_rec() , memo()) -> ty_rec()), {const, Const}) -> Const.
corec(Corec, Memo, Continue, Type) ->
  case Memo of
    #{Corec := Codefinition} -> Codefinition;
    _ ->
      UnfoldMaybeList = fun(L) when is_list(L) -> [T() || T <- L]; (L) -> L() end,
      case Type of
        reference -> fun NewRef() -> Continue(UnfoldMaybeList(Corec), Memo#{Corec => NewRef}) end;
        {const, Const} -> Continue(UnfoldMaybeList(Corec), Memo#{Corec => Const})
      end
  end.


-spec negate(ty_ref(), memo()) -> ty_ref(); (ty_rec(), memo()) -> ty_rec().
negate(Ty, Memo) when is_function(Ty) -> corec_ref(Ty, Memo, fun negate/2);

negate(#ty{flag = F, map = Map}, M) ->
  FlagDnf = negate_flag_dnf(F, M),
  MapDnf = negate_map_dnf(Map, M),
  #ty{flag = FlagDnf, map = MapDnf}.

-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  dnf(Dnf, {fun(P, N) ->
    [F | Fs] = [negated_flag(F) || F <- P] ++ [flag(F) || F <- N],
    lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, F, Fs)
            end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

-spec negate_map_dnf(dnf(map()), memo()) -> dnf(map()).
negate_map_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  dnf(Dnf, {fun(P, N) ->
    [Map | Maps] = [negated_map(T) || T <- P] ++ [map(T) || T <- N],
    lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, Map, Maps)
            end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

% intersection and union for ty, corecursive
% Here, we have two operands for memoization.
% We memoize the intersection operation Ty & Ty2 as {Ty, Ty2}
% and the result equation as NewTy
% Whenever the intersection operation on Ty & Ty2 is encountered
% we return the memoized result NewTy
% In our implementation, the corecursive case is never triggered,
% as intersection and negation only moves the atoms in the lines around.
% It does not recurse into an atom in a line.
-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cintersect/2).
-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cunion/2).

% wrapper functions for single argument type operators
-spec cintersect ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cintersect([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cintersect/2);
cintersect([#ty{flag = F1, map = M1}, #ty{flag = F2, map = M2}], _Memo) ->
  #ty{flag = intersect_dnf(F1, F2), map = intersect_dnf(M1, M2)}.

-spec cunion ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cunion([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cunion/2);
cunion([#ty{flag = F1, map = M1}, #ty{flag = F2, map = M2}], _Memo) ->
  #ty{flag = union_dnf(F1, F2), map = union_dnf(M1, M2)}.


-spec union_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
union_dnf(A, B) -> lists:uniq(A ++ B).

-spec intersect_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
intersect_dnf(A, B) -> lists:uniq([{lists:usort(P1 ++ P2), lists:usort(N1 ++ N2)} || {P1, N1} <- A, {P2, N2} <- B]).


-spec dnf(dnf(Atom), {fun(([Atom], [Atom]) -> Result), fun((Result, Result) -> Result)}) -> Result.
dnf([{Pos, Neg}], {Process, _Combine}) -> Process(Pos, Neg);
dnf([{Pos, Neg} | Cs], F = {Process, Combine}) ->
  Res1 = Process(Pos, Neg),
  Res2 = dnf(Cs, F),
  Combine(Res1, Res2).


% now for the main part, emptyness checking
-spec is_empty(ty_ref()) -> boolean().
is_empty(Ty) ->
  corec_const(Ty, #{}, fun is_empty/2, true).

-spec is_empty(ty_ref(), memo()) -> boolean(); (ty_rec(), memo()) -> boolean().
is_empty(Ty, Memo) when is_function(Ty) -> corec_const(Ty, Memo, fun is_empty/2, true);
is_empty(#ty{flag = FlagDnf, map = MapDnf}, Memo) ->
  is_empty_flag(FlagDnf, Memo) and is_empty_map(MapDnf, Memo).


-spec is_empty_flag(dnf(flag()), memo()) -> boolean().
is_empty_flag(FlagDnf, _Memo) -> % memo not needed, no corecursive components
  dnf(FlagDnf, {
    fun ([F], N) -> lists:member(F, N);
        (_, _) -> true
    end,
    fun erlang:'and'/2
  }).

-spec is_empty_map(dnf(map()), memo()) -> boolean().
is_empty_map(MapDnf, Memo) ->
  dnf(MapDnf, {
    fun(P, N) -> phi_map(big_intersect(P), N, Memo) end,
    fun erlang:'and'/2
  }).

phi_map(Pos, [], Memo) ->
  #map{ls = Ls, st = St} = Pos,
  % Just check emptiness of each field
  lists:any(
    fun(Fld) -> field_empty(Fld, Memo) end,
    maps:values(Ls) ++ maps:values(St)
  );
phi_map(Pos, [Neg | Negs], Memo) ->
  #map{ls = Ls1, st = St1, ns = {ManNs1, OptNs1}} = Pos,
  #map{ls = Ls2, st = St2, ns = {ManNs2, OptNs2}} = Neg,
  %% (1) Check Named Indexes
  %     - Mandatory names must be the same:
  X1 = lists:usort(ManNs1) == lists:usort(ManNs2),
  %     - Orelse, Neg must contain all mandatory-names of the Pos as optional-names:
  X11 = lists:prefix(lists:usort(ManNs1), lists:usort(OptNs2)),
  %     - Also Neg must contain all the optional-names of Pos:
  X2 = lists:prefix(lists:usort(OptNs1), lists:usort(OptNs2)),
  % Hence:
  case (X1 orelse X11) andalso X2 of
    true ->
      %% (2) Check Step Emptiness
      #{?LStep := Ref1, ?LHatStep := Ref2} = St1,
      #{?LStep := Ref3, ?LHatStep := Ref4} = St2,
      LEmpty = field_empty(field_diff(Ref1, Ref3), Memo),
      LHatEmpty = field_empty(field_diff(Ref2, Ref4), Memo),
      case LEmpty andalso LHatEmpty of
        true ->
          %% (3) Check Label Emptiness (and recurse if needed)
          AllLabels =
            maps:keys(Ls1) ++ maps:keys(Ls2),
          LabelFieldDiffs =
            #{L => field_diff(pi(L, Pos), pi(L, Neg)) || L <- AllLabels},
          NonEmptyDiffs =
            #{L => Fld || L := Fld <- LabelFieldDiffs, not field_empty(Fld, Memo)},

          % Function to apply to each nonempty fields
          IntersectAndRecurse =
            fun({L, Fld}) -> phi_map( % recursion
              big_intersect([Pos, map_with_label(L, Fld)]), % intersection
              Negs, Memo)
            end,
          % All recursive applications must return true
          lists:all(
            IntersectAndRecurse,
            maps:to_list(NonEmptyDiffs)
          );
        false ->
          % Recurse to rest
          phi_map(Pos, Negs, Memo)
      end;
    false ->
      % Recurse to rest
      phi_map(Pos, Negs, Memo)
  end.

-spec big_intersect([map()]) -> map().
big_intersect([]) -> #map{  st = #{?LStep => {?OPT, any()}, ?LHatStep => {?OPT, any()}}  };
big_intersect([Map]) -> Map;
big_intersect([Map1, Map2 | Maps]) ->
  #map{ls = Ls1, st = St1, ns = {ManNs1, OptNs1}} = Map1,
  #map{ls = Ls2, st = St2, ns = {ManNs2, OptNs2}} = Map2,

  AllLabels = maps:keys(Ls1) ++ maps:keys(Ls2),
  Ls = #{L => field_intersect(pi(L, Map1), pi(L, Map2)) || L <- AllLabels},
  St = maps:intersect_with(fun(_, Fld1, Fld2) -> field_intersect(Fld1, Fld2) end, St1, St2),

  Map = #map{ls = Ls, st = St, ns = {lists:usort(ManNs1 ++ ManNs2), lists:usort(OptNs1 ++ OptNs2)}},
  big_intersect([Map | Maps]).


-spec pi(flag(), map()) -> field().
pi(F, #map{ls = Ls, st = St}) ->
  case Ls of
    #{F := Fld} -> Fld;
    #{} -> #{?LStep := Fld} = St, Fld
  end.

-spec map_with_label(flag(), field()) -> map().
map_with_label(F, Fld) -> #map{
  ls = #{F => Fld},
  st = #{?LStep => {?OPT, any()}, ?LHatStep => {?OPT, any()}}
}.

-spec field_intersect(field(), field()) -> field().
field_intersect({?MAN, Ref1}, {_, Ref2}) -> {?MAN, intersect(Ref1, Ref2)};
field_intersect({?OPT, Ref1}, {Assoc, Ref2}) -> {Assoc, intersect(Ref1, Ref2)}.

-spec field_diff(field(), field()) -> field().
field_diff({?MAN, Ref1}, {_, Ref2}) -> {?MAN, intersect(Ref1, negate(Ref2))};
field_diff({?OPT, Ref1}, {?OPT, Ref2}) -> {?MAN, intersect(Ref1, negate(Ref2))};
field_diff({?OPT, Ref1}, {?MAN, Ref2}) -> {?OPT, intersect(Ref1, negate(Ref2))}.

-spec field_empty(field(), memo()) -> boolean().
field_empty({?MAN, Ref}, Memo) -> is_empty(Ref, Memo);
field_empty({?OPT, _}, _Memo) -> false.



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  A = any(),
  io:format(user,"Any: ~p (~p) ~n~p~n", [A, erlang:phash2(A), A()]),

  % negation:
  Aneg = negate(A),
  io:format(user,"Empty: ~p~n", [Aneg]),
  io:format(user,"Empty unfolded: ~p~n", [Aneg()]),

  % intersection of same recursive equations
  Ai = intersect(A, A),
  io:format(user,"Any & Any: ~p~n", [{Ai, Ai()}]),

  % % double negation
  Anegneg = negate(negate(A)),
  io:format(user,"Any: ~p~n", [Anegneg]),
  io:format(user,"Any unfolded: ~p~n", [Anegneg()]),

  % % We cannot trust the name generated for the corecursive equations (Erlang funs):
  io:format(user,"Refs Aneg vs Anegneg: ~p vs ~p~nHashes Aneg vs Anegeg: ~p vs ~p~n", [Aneg, Anegneg, erlang:phash2(Aneg), erlang:phash2(Anegneg)]),
  F1 = io_lib:format("~p", [Aneg]),
  F2 = io_lib:format("~p", [Anegneg]),
  true = (F1 =:= F2),
  false = (Aneg =:= Anegneg),
  false = (erlang:phash2(Aneg) =:= erlang:phash2(Anegneg)),

  % is_empty
  io:format(user,"Any is empty: ~p~n", [is_empty(A)]),
  false = is_empty(A),
  io:format(user,"Empty is empty: ~p~n", [is_empty(Aneg)]),
  true = is_empty(Aneg),

  % define a custom any type
  X = fun Z() -> ty(any_flag(), map(#map{  st =  steps({?OPT, Z}, {?OPT, Z}) })) end,
  % it's different from the any equation return by any()
  true = X /= any(),
  io:format(user,"Any (custom) is empty: ~p~n", [is_empty(X)]),
  false = is_empty(X),

  JustTrue = fun() -> ty_flag(flag(1)) end,
  false = is_empty(JustTrue),

  % {1 := Y} where Y = {2 := Y} | {3 := Y}
  Right = fun Y() -> ty_map(union_dnf(
    map(#map{  ls = #{2 => {?MAN, Y}},   st = steps({?OPT, empty()}, {?OPT, empty()})  }),
    map(#map{  ls = #{3 => {?MAN, Y}},   st = steps({?OPT, empty()}, {?OPT, empty()})  })
  )) end,
  Left = fun() -> ty_map(
    map(#map{  ls = #{1 => {?MAN, Right}},   st = steps({?OPT, empty()}, {?OPT, empty()})  })
  ) end,

  true = is_empty(Left),

  % interleaving corecursion
  % {1 := A} where
  % A = {2 := B} | {AnyNum => 2}
  % B = {3 := A}
  Ty = fun() ->
    fun TyA() ->
      TyB = fun() -> ty_map(map(#map{  ls = #{3 => {?MAN, TyA}},   st = steps({?OPT, empty()}, {?OPT, empty()})  })) end,
      ty_map(union_dnf(
        map(#map{
          ls = #{2 => {?MAN, TyB}},
          st = steps({?OPT, empty()}, {?OPT, empty()})
        }),
        map(#map{
          st = steps({?OPT, fun() -> ty_flag(flag(2)) end}, {?OPT, fun() -> ty_flag(flag(2)) end})
        })))
    end
       end,

  false = is_empty(Ty),

  % {1 := A} where
  % A = {2 := B}
  % B = {3 := A}
  Ty2 = fun() ->
    fun TyA() ->
      TyB = fun() ->
        ty_map(map(#map{  ls = #{3 => {?MAN, TyA}},   st = steps({?OPT, empty()}, {?OPT, empty()})  }))
            end,
      ty_map(map(#map{  ls = #{2 => {?MAN, TyB}},  st = steps({?OPT, empty()}, {?OPT, empty()})  }))
    end
       end,

  true = is_empty(Ty2),

  ok.


map_test() ->
  % (1) Three arbitrary types denoting the empty map {| |}
  fun() ->
    S = fun() -> ty_map(map(#map{st = steps({?OPT, empty()}, {?OPT, empty()})})) end,
    T = fun() -> ty_map(map(#map{ls = #{1 => {?OPT, empty()}}, st = steps({?OPT, empty()}, {?OPT, empty()})})) end,
    U = fun() -> ty_map(map(#map{ls = #{2 => {?OPT, empty()}}, st = steps({?OPT, empty()}, {?OPT, empty()})})) end,
    false = lists:any(fun is_empty/1, [S, T, U]),
    % S <: T <: U <: S
    {true, _} = lists:foldr(fun(Ty1, {Bool, Ty2}) -> {Bool andalso is_empty(intersect(Ty2, negate(Ty1))), Ty1} end, {true, S}, [T, U, S])
  end(),

  % (2) Three arbitrary types denoting the any map {| Any => Any |}
  fun() ->
    S = fun() -> ty_map(map(#map{st = steps({?OPT, any()}, {?OPT, any()})})) end,
    T = fun() -> ty_map(map(#map{ls = #{1 => {?OPT, any()}}, st = steps({?OPT, any()}, {?OPT, any()})})) end,
    U = fun() -> ty_map(map(#map{ls = #{2 => {?OPT, any()}}, st = steps({?OPT, any()}, {?OPT, any()})})) end,
    false = lists:any(fun is_empty/1, [S, T, U]),
    % S <: T <: U <: S
    {true, _} = lists:foldr(fun(Ty1, {Bool, Ty2}) -> {Bool andalso is_empty(intersect(Ty2, negate(Ty1))), Ty1} end, {true, S}, [T, U, S])
  end(),

  % (3) Any/Empty edge cases
  fun() ->
    Any = fun() -> ty_map(map(#map{st = steps({?OPT, any()}, {?OPT, any()})})) end,
    Empty = fun() -> ty_map(map(#map{ls = #{1 => {?MAN, empty()}}, st = steps({?OPT, any()}, {?OPT, any()})})) end,
    false = is_empty(Any),
    true = is_empty(Empty),
    true = is_empty(intersect(Any, Empty)),
    false = is_empty(union(Any, Empty))
  end(),

  % (4) Subtyping example
  fun() ->
    % {| 1 := 1, 2 => 2, 10 => 3 |} = S
    S = fun() -> ty_map(map(#map{
      ls = #{
        1 => {?MAN, fun() -> ty_flag(flag(1)) end},
        2 => {?OPT, fun() -> ty_flag(flag(2)) end},
        10 => {?OPT, fun() -> ty_flag(flag(3)) end}
      },
      st = steps({?OPT, empty()}, {?OPT, empty()})
    })) end,
    % {| 1 => 1, 2 := 2, 3 => 3 |} = T
    T = fun() -> ty_map(map(#map{
      ls = #{
        1 => {?OPT, fun() -> ty_flag(flag(1)) end},
        2 => {?MAN, fun() -> ty_flag(flag(2)) end},
        3 => {?OPT, fun() -> ty_flag(flag(3)) end}
      },
      st = steps({?OPT, empty()}, {?OPT, empty()})
    })) end,
    % S !<:>! T
    false = is_empty(intersect(S, negate(T))),
    false = is_empty(intersect(T, negate(S)))
  end(),

  ok.


map_variable_test() ->
  % {| 1 := 1, 2 => 2 |} = S
  S = fun() -> ty_map(map(#map{
    ls = #{1 => {?MAN, fun() -> ty_flag(flag(1)) end}, 2 => {?OPT, fun() -> ty_flag(flag(2)) end}},
    st = steps({?OPT, empty()}, {?OPT, empty()})
  })) end,

  % {| beta => 1 U 2 |} = T
  Union = union(fun() -> ty_flag(flag(1)) end, fun() -> ty_flag(flag(2)) end),
  T = fun() -> ty_map(map(#map{
    st = steps({?OPT, Union}, {?OPT, Union}),
    ns = {[], [beta]}
  })) end,

  % {| alpha := 1, beta => 2 |} = U
  U = fun() -> ty_map(map(#map{
    st = steps({?MAN, fun() -> ty_flag(flag(1)) end}, {?OPT, fun() -> ty_flag(flag(2)) end}),
    ns = {[alpha], [beta]}
  })) end,

  true = is_empty(intersect(S, negate(T))),
  false = is_empty(intersect(S, negate(U))),
  false = is_empty(intersect(U, negate(S))),

  ok.

steps(LStepField, LHatStepField) ->
  #{?LStep => LStepField, ?LHatStep => LHatStepField}.

-endif.
