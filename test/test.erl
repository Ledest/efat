-module(test).

-export([test1/4, test2/2, test3/1]).

-compile([{parse_transform, efat_pt}]).

-record(rec, {}).

test1({A/term, C/{int,#{}}}, I/{}:size(T), B/[1,2,3], [H1/#rec{},H2/tuple|T/any:I]) when is_tuple(I); is_float(A) -> ok.

test2(I, A) when is_integer(I), is_integer(A) -> I + A.

test3(X) when tuple_size(X) =:= 3 orelse X =:= 2 orelse X =:= 3 -> true.
