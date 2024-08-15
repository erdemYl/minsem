-module(recsem).
-compile(nowarn_export_all).
-compile(export_all).

-define(MAN, mandatory).
-define(OPT, optional).

% This module implements a minimal but full implementation for the semantic subtyping framework for the limited type algebra
%
% t = true | {t, t} | r | !t | t & t        r = { true => t,  (Any, Any) => t }
%                                             | { true := t, (Any, Any) => t }
%
% In addition to the minimal grammar records are now allowed.
% Semantics: quasi K-step functions

-type ty() :: ty_ref() | ty_rec().
-type product() :: {ty_ref(), ty_ref()}.
-type flag() :: true.

% General data structure for records.
% General case matters, although it is an overfit for the grammar.
% Record constructor also uses equation references (as values) that are unfolded upon visit.
-type record() :: {record, labels(), steps()}.

% Keys are not equation references (corecursion not needed).
% The theory requires key specifications to be either singletons (true) or steps ((Any, Any)).
-type labels() :: #{flag() := field()}.
-type steps()  :: #{step() := field()}.
-type field() :: {assoc(), ty_ref()}.
-type step()  :: tuples.
-type assoc() :: mandatory | optional.
% What about singleton products, e.g. (true*, true*)? We can implement a check whether
% some product unfolds to a union of singleton products. We will avoid this complex case.
% Yet its implementation should require modest effort w.r.t. the minimal grammar.
% More sophistication is needed, though, in a richer grammar.

% Usual adjustment with records.
-record(ty, { flag = negated_flag() :: dnf(flag()), product :: dnf(product()), record :: dnf(record()) }).

-type ty_ref () :: fun(() -> ty_rec()).
-type ty_rec () :: #ty{}.
-type memo() :: #{}.
-type dnf(Atom) :: [{[Atom], [Atom]}].

% Constructors for flags and products at the DNF level
-spec flag() -> dnf(true).
flag() -> [{[true], []}].

-spec negated_flag() -> dnf(true).
negated_flag() -> [{[], [true]}].

-spec product(ty_ref(), ty_ref()) -> dnf(product()).
product(A, B) -> [{[{A, B}], []}].

-spec product(product()) -> dnf(product()).
product(P) -> [{[P], []}].

-spec negated_product(product()) -> dnf(product()).
negated_product(P) -> [{[], [P]}].


-spec record(labels(), steps()) -> dnf(record()).
record(Ls, St) -> [{[{record, Ls, St}], []}].

-spec record(record()) -> dnf(record()).
record(Rec) -> [{[Rec], []}].

-spec anyrecord() -> record().
anyrecord() -> {record, #{true => {?OPT, any()}}, #{tuples => {?OPT, any()}}}.

-spec negated_record(record()) -> dnf(record()).
negated_record(Rec) -> [{[], [Rec]}].


-spec ty(dnf(flag()), dnf(product()), dnf(record())) -> ty_rec().
ty(Flag, Product, Rec) -> #ty{flag = Flag, product = Product, record = Rec}.

-spec ty_flag(dnf(flag())) -> ty_rec().
ty_flag(Flag) -> #ty{flag = Flag, product = product(empty(), empty()), record = negated_record(anyrecord())}.

-spec ty_product(dnf(product())) -> ty_rec().
ty_product(Product) -> #ty{flag = negated_flag(), product = Product}.

-spec ty_record(dnf(record())) -> ty_rec().
ty_record(Rec) -> #ty{flag = negated_flag(), product = product({empty(), empty()}), record = Rec}.


% Corecursive Top type:  Any = true U. {Any, Any} U. {true => Any, (Any, Any) => Any}
-spec any() -> ty().
any() -> fun Any() -> #ty{
  flag = flag(),
  product = product(Any, Any),
  record = record(#{true => {?OPT, Any}}, #{tuples => {?OPT, Any}})
} end.

% Empty := !Any = false U. !{Any, Any} U. !{true => Any, (Any, Any) => Any}
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
negate(Ty, Memo) when is_function(Ty) ->
  corec_ref(Ty, Memo, fun negate/2);
negate(#ty{flag = F, product = Prod, record = Rec}, M) ->
  FlagDnf = negate_flag_dnf(F, M),
  ProductDnf = negate_product_dnf(Prod, M),
  RecordDnf = negate_record_dnf(Rec, M),
  #ty{flag = FlagDnf, product = ProductDnf, record = RecordDnf}.


-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  dnf(Dnf, {fun(P, N) ->
    [X | Xs] = [negated_flag() || true <- P] ++ [flag() || true <- N],
    lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
            end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

-spec negate_product_dnf(dnf(product()), memo()) -> dnf(product()).
negate_product_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  dnf(Dnf, {fun(P, N) ->
    [X | Xs] = [negated_product(T) || T <- P] ++ [product(T) || T <- N],
    lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
            end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

-spec negate_record_dnf(dnf(record()), memo()) -> dnf(record()).
negate_record_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  dnf(Dnf, {fun(P, N) ->
    [X | Xs] = [negated_record(T) || T <- P] ++ [record(T) || T <- N],
    lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
            end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).


-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cintersect/2).
-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cunion/2).

-spec cintersect ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cintersect([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cintersect/2);
cintersect([#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}], _Memo) ->
  #ty{flag = intersect_dnf(F1, F2), product = intersect_dnf(P1, P2)}.

-spec cunion ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cunion([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cunion/2);
cunion([#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}], _Memo) ->
  #ty{flag = union_dnf(F1, F2), product = union_dnf(P1, P2)}.


-spec union_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
union_dnf(A, B) -> lists:uniq(A ++ B).
-spec intersect_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
intersect_dnf(A, B) -> [{lists:uniq(P1 ++ P2), lists:uniq(N1 ++ N2)} || {P1, N1} <- A, {P2, N2} <- B].

-spec dnf(dnf(Atom), {fun(([Atom], [Atom]) -> Result), fun((Result, Result) -> Result)}) -> Result.
dnf([{Pos, Neg}], {Process, _Combine}) -> Process(Pos, Neg);
dnf([{Pos, Neg} | Cs], F = {Process, Combine}) ->
  Res1 = Process(Pos, Neg),
  Res2 = dnf(Cs, F),
  Combine(Res1, Res2).


% Main Part: emptiness checking
-spec is_empty(ty_ref()) -> boolean().
is_empty(Ty) ->
  corec_const(Ty, #{}, fun is_empty/2, true).

-spec is_empty(ty_ref(), memo()) -> boolean(); (ty_rec(), memo()) -> boolean().
is_empty(Ty, Memo) when is_function(Ty) -> corec_const(Ty, Memo, fun is_empty/2, true);
is_empty(#ty{flag = FlagDnf, product = ProdDnf}, Memo) ->
  is_empty_flag(FlagDnf, Memo) and is_empty_prod(ProdDnf, Memo).

-spec is_empty_flag(dnf(flag()), memo()) -> boolean().
% flag emptyness, empty iff: (true in N)
is_empty_flag(FlagDnf, _Memo) -> % memo not needed, no corecursive components
  dnf(FlagDnf, {fun(_Pos, Neg) -> not sets:is_empty(sets:from_list(Neg)) end, fun(R1, R2) -> R1 and R2 end}).

-spec is_empty_prod(dnf(product()), memo()) -> boolean().
% product emptyness, empty iff: product dnf empty
is_empty_prod(Dnf, Memo) ->
  dnf(Dnf, {
    fun(Pos, Neg) ->
      % intersect all positive products, and execute full tree exploration phi
      {Ty1, Ty2} = big_intersect(Pos),
      phi(Ty1, Ty2, Neg, Memo)
    end,
    fun(R1, R2) -> R1 and R2 end
  }).

-spec is_empty_record(dnf(record()), memo()) -> boolean().
is_empty_record(Dnf, Memo) ->
  dnf(Dnf, {
    fun(Pos, Neg) -> phi_record(big_intersect_record(Pos), Neg, Memo) end,
    fun(R1, R2) -> R1 and R2 end
  }).

-spec big_intersect([product()]) -> product().
big_intersect([]) -> {any(), any()};
big_intersect([X]) -> X;
big_intersect([{Ty1, Ty2}, {Ty3, Ty4} | Xs]) ->
  big_intersect([{intersect(Ty1, Ty3), intersect(Ty2, Ty4)} | Xs]).

-spec big_intersect_record([record()]) -> record().
big_intersect_record([]) -> anyrecord();
big_intersect_record([{record, _, _} = Rec]) -> Rec;
big_intersect_record([{record, Ls1, St1}, {record, Ls2, St2} | Recs]) ->
  Ls = maps:intersect_with(fun(_, Fld1, Fld2) -> field_intersect(Fld1, Fld2) end, Ls1, Ls2),
  St = maps:intersect_with(fun(_, Fld1, Fld2) -> field_intersect(Fld1, Fld2) end, St1, St2),
  big_intersect([{record, Ls, St} | Recs]).

-spec field_intersect(field(), field()) -> field().
field_intersect({?MAN, Ref1}, {_, Ref2}) -> {?MAN, intersect(Ref1, Ref2)};
field_intersect({?OPT, Ref1}, {Assoc, Ref2}) -> {Assoc, intersect(Ref1, Ref2)}.


% Φ(S1 , S2 , ∅ , T1 , T2) = (S1<:T1) or (S2<:T2)
% Φ(S1 , S2 , N ∪ {T1, T2} , Left , Right) = Φ(S1 , S2 , N , Left | T1 , Right) and Φ(S1 , S2 , N , Left , Right | T2)
-spec phi(ty_ref(), ty_ref(), [ty_ref()], memo()) -> boolean().
phi(S1, S2, N, Memo) -> phi(S1, S2, N, empty(), empty(), Memo).

-spec phi(ty_ref(), ty_ref(), [ty_ref()], ty_ref(), ty_ref(), memo()) -> boolean().
phi(S1, S2, [], T1, T2, Memo) ->
  is_empty(intersect(S1, negate(T1)), Memo) or is_empty(intersect(S2, negate(T2)), Memo);
phi(S1, S2, [{T1, T2} | N], Left, Right, Memo) ->
  phi(S1, S2, N, union(Left, T1), Right, Memo) and phi(S1, S2, N , Left, union(Right,T2), Memo).


-spec phi_record(record(), [record()], memo()) -> boolean().
phi_record({record, _, _}, [], _) -> false;
phi_record({record, Ls1, St1} = P, [{record, Ls2, St2} | Ns], Memo) ->
  #{tuples := StepFld} = maps:intersect_with(fun(_, Fld1, Fld2) -> field_diff(Fld1, Fld2, Memo) end, St1, St2),
  case field_empty(StepFld) of
    true ->
      #{true := FlagFld} = maps:intersect_with(fun(_, Fld1, Fld2) -> field_diff(Fld1, Fld2, Memo) end, Ls1, Ls2),
      case field_empty(FlagFld) of
        true -> true;
        false ->
          Rec = {record, #{true => FlagFld}, #{tuples => {?OPT, any()}}},
          phi_record(big_intersect_record([P, Rec]), Ns, Memo)
      end;
    false ->
      phi_record(P, Ns, Memo)
  end.

-spec field_diff(field(), field(), memo()) -> field().
field_diff({?MAN, Ref1}, {_, Ref2}, Memo) -> {?MAN, intersect(Ref1, negate(Ref2, Memo))};
field_diff({?OPT, Ref1}, {?OPT, Ref2}, Memo) -> {?MAN, intersect(Ref1, negate(Ref2, Memo))};
field_diff({?OPT, Ref1}, {?MAN, Ref2}, Memo) -> {?OPT, intersect(Ref1, negate(Ref2, Memo))}.

-spec field_empty(field()) -> boolean().
field_empty({?MAN, Ref}) -> is_empty(Ref);
field_empty({?OPT, _}) -> false.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  A = any(),
  io:format(user,"Any: ~p (~p) ~n~p~n", [A, erlang:phash2(A), A()]),

  % negation:
  Aneg = negate(A),
  io:format(user,"Empty: ~p~n", [Aneg]),
  io:format(user,"Empty unfolded: ~p~n", [Aneg()]),

  %intersection of same recursive equations
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
  X = fun Z() -> ty(flag(), product(Z, Z), record(#{true => {?OPT, any()}}, #{tuples => {?OPT, any()}})) end,
  % it's different from the any equation return by any()
  true = X /= any(),
  io:format(user,"Any (custom) is empty: ~p~n", [is_empty(X)]),
  false = is_empty(X),

  % (X, (X, true)) where X = (X, true) | (true, true)
  JustTrue = fun() -> ty_flag(flag()) end,
  false = is_empty(JustTrue),
  RX = fun XX() -> ty_product( union_dnf(product(XX, JustTrue), product(JustTrue, JustTrue)) ) end,
  false = is_empty(RX),
  RXX = fun() ->
    InnerProd = fun() -> ty_product(product(RX, JustTrue)) end,
    ty_product(product(RX, InnerProd))
        end,
  false = is_empty(RXX),

  % interleaving corecursion
  % (true, A) where
  % A = (B, true) | (true, true)
  % B = (true, A)
  Ty = fun() ->
    fun TyA() ->
      TyB = fun() -> ty_product(product(JustTrue, TyA)) end,
      ty_product( union_dnf(product(TyB, JustTrue), product(JustTrue, JustTrue)))
    end
       end,
  false = is_empty(Ty),

  % (true, A) where
  % A = (B, true)
  % B = (true, A)
  Ty2 = fun() ->
    fun TyA() ->
      TyB = fun() -> ty_product(product(JustTrue, TyA)) end,
      ty_product( product(TyB, JustTrue) )
    end
        end,
  true = is_empty(Ty2),

  ok.

-endif.