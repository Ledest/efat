-module(test).

-export([test1/4, test2/2, test3/1, test4/0]).

-compile([{parse_transform, efat_pt}]).

-record(rec, {}).

test1({A/integer>=0, C/{int,#{}}}, I/{}:size(T), B/[1,2,3], [H1/#rec{},H2/tuple|T/any:I])
  when is_tuple(I); is_float(A) ->
    ok.

test2(I/{integer,null}, A) -> I + A.

test3(X/integer=/=0) when tuple_size(X) =:= 3 orelse X =:= 2 orelse X =:= 3 -> true.

test4({X/any>0, Y!term}) ->
    lists:foldl(fun({I/term=:=X, L>A}, A) -> L;
                   (_, A) -> A
                end, 0, Y).
