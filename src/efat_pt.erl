-module(efat_pt).

-export([parse_transform/2]).

-define(OP, '/').

-import(erl_syntax, [concrete/1, type/1, get_pos/1,
                     integer_value/1, atom_value/1,
                     tuple_elements/1,
                     infix_expr_left/1, infix_expr_right/1,
                     module_qualifier_argument/1, module_qualifier_body/1]).

parse_transform(Forms, _Options) ->
    lists:map(fun(Tree) ->
                  erl_syntax:revert(erl_syntax_lib:map(fun(E) -> do_transform(E) end, Tree))
              end, Forms).

do_transform(Node) ->
    case type(Node) of
        clause -> clause_transform(Node);
        _ -> Node
    end.

clause_transform(Node) ->
    case erl_syntax:clause_patterns(Node) of
        none -> Node;
        Patterns ->
            case patterns_transform(Patterns) of
                {Patterns, _} -> Node;
%                {P, []} ->
%                    io:fwrite(standard_error, "Patterns = ~p~nP = ~p~n", [Patterns, P]),
%                    erl_syntax:clause(P, erl_syntax:clause_guard(Node), erl_syntax:clause_body(Node));
                {P, G} ->
                    erl_syntax:clause(P,
                                      case erl_syntax:clause_guard(Node) of
                                          none -> conjunction(G);
                                          Guards -> disjunction(lists:map(fun(E) -> guards_append(G, E) end,
                                                                erl_syntax:disjunction_body(Guards)))
                                      end,
                                      erl_syntax:clause_body(Node))
            end
    end.

guards_append(L, G) -> conjunction(L ++ erl_syntax:conjunction_body(G)).

patterns_transform(Patterns) -> lists:mapfoldr(fun pattern_transform/2, [], Patterns).

pattern_transform(Pattern, Guards) ->
    case Pattern =/= none andalso type(Pattern) of
        infix_expr -> do_pattern_transform(Pattern, Guards);
        tuple ->
            {P, G} = patterns_transform(tuple_elements(Pattern)),
            {tuple(P), G ++ Guards};
        list ->
            {PH, GH} = patterns_transform(erl_syntax:list_prefix(Pattern)),
            {PT, GT} = pattern_transform(erl_syntax:list_suffix(Pattern), []),
            {list(PH, PT), GH ++ GT ++ Guards};
        _ -> {Pattern, Guards}
    end.

do_pattern_transform(Pattern, Guards) ->
    O = erl_syntax:infix_expr_operator(Pattern),
    case erl_syntax:operator_name(O) of
        ?OP -> do_pattern_transform_op(Pattern, Guards);
        Op ->
            case lists:member(Op, ['<', '>', '=<', '>=', '/=', '=/=']) of
                true ->
                    case do_pattern_transform(infix_expr_left(Pattern), []) of
                        {Pattern, []} -> {Pattern, Guards};
                        {V, G} -> {V, G ++ [infix_expr(V, O, infix_expr_right(Pattern))|Guards]}
                    end;
                _ -> {Pattern, Guards}
            end
    end.

do_pattern_transform_op(Pattern, Guards) ->
    Arg = infix_expr_left(Pattern),
    case type(Arg) of
        variable -> do_pattern_transform_op(Pattern, Guards, Arg);
        _ -> {Pattern, Guards}
    end.

do_pattern_transform_op(Pattern, Guards, Arg) ->
    Type = infix_expr_right(Pattern),
    case get_pos(Arg) =:= get_pos(Type) of
        true -> do_pattern_transform_op(Pattern, Guards, Arg, Type);
        _ -> {Pattern, Guards}
    end.

do_pattern_transform_op(Pattern, Guards, Arg, Type) -> do_pattern_transform_op(Pattern, Guards, Arg, Type, type(Type)).

do_pattern_transform_op(Pattern, Guards, Arg, Type, atom) ->
    T = atom_value(Type),
    if
        T =:= any orelse T =:= term -> {variable(Arg), Guards};
        T =:= record ->
            V = variable(Arg),
            {V, make_guard(application(atom(is_atom, Arg), [application(atom(element, Arg), [integer(1, Arg), V])]),
                           Guards)};
        true ->
            case type_to_guard(T) of
                undefined -> {Pattern, Guards};
                G -> make_var_guard(G, Arg, Guards)
            end
    end;
do_pattern_transform_op(_Pattern, Guards, Arg, Type, record_expr) ->
    make_var_guard(is_record, Arg, Guards, fun() -> erl_syntax:record_expr_type(Type) end);
do_pattern_transform_op(Pattern, Guards, Arg, Type, map_expr) ->
    case erl_syntax:map_expr_fields(Type) of
        [] -> make_var_guard(is_map, Arg, Guards);
        _ -> {Pattern, Guards}
    end;
do_pattern_transform_op(_Pattern, Guards, Arg, _Type, nil) -> make_var_guard(is_list, Arg, Guards);
do_pattern_transform_op(_Pattern, Guards, Arg, Type, list) ->
    case erl_syntax:list_elements(Type) of
        [Size] -> make_var_guard(length, Arg, Size, Guards);
        L ->
            V = variable(Arg),
            {V, [make_orelse_chain(lists:map(fun(E) -> {V, [infix_expr(V, operator('=:=', V), E)]} end, L))|Guards]}
    end;
do_pattern_transform_op(Pattern, Guards, Arg, Type, tuple) ->
    case tuple_elements(Type) of
        [] -> make_var_guard(is_tuple, Arg, Guards);
        [Size] -> make_var_guard(tuple_size, Arg, Size, Guards);
        Types ->
            {variable(Arg),
             [make_orelse_chain(lists:map(fun(T) -> do_pattern_transform_op(Pattern, [], Arg, T) end, Types))|Guards]}
    end;
do_pattern_transform_op(Pattern, Guards, Arg, Type, binary) ->
    case erl_syntax:binary_fields(Type) of
        [] -> make_var_guard(is_binary, Arg, Guards);
        [Size] -> make_var_guard(byte_size, Arg, erl_syntax:binary_field_body(Size), Guards);
        _ -> {Pattern, Guards}
    end;
do_pattern_transform_op(_, Guards, Arg, Type, integer) -> make_var_guard(size, Arg, Type, Guards);
do_pattern_transform_op(Pattern, Guards, Arg, Type, module_qualifier) ->
    case type_to_size_guard(module_qualifier_argument(Type)) of
        undefined -> {Pattern, Guards};
        G -> make_var_guard(G, Arg, module_qualifier_body(Type), Guards)
    end;
do_pattern_transform_op(Pattern, Guards, Arg, Type, application) ->
    O = erl_syntax:application_operator(Type),
    case type(O) of
        module_qualifier ->
            case type_to_size_guard(module_qualifier_argument(O)) of
                undefined -> {Pattern, Guards};
                G -> make_var_guard(G, Arg,
                                    application(atom(atom_value(module_qualifier_body(O)), O),
                                                erl_syntax:application_arguments(Type)),
                                    Guards)
            end;
        _ -> {Pattern, Guards}
    end;
do_pattern_transform_op(Pattern, Guards, _Arg, _Type, T) ->
    io:fwrite(standard_error, "Unknown type '~p'~n", [T]),
    {Pattern, Guards}.

make_orelse_chain(Guards) -> make_op_chain(Guards, 'orelse').

make_op_chain(Guards, Op) ->
    [{_, [H]}|T] = lists:reverse(Guards),
    lists:foldl(fun({_, [G]}, A) -> infix_expr(G, operator(Op, G), A) end, H, T).

make_guard(G, Guards) -> [G|Guards].

make_var_guard(G, Arg, Guards) when is_atom(G) ->
    V = variable(Arg),
    {V, [application(atom(G, Arg), [V])|Guards]}.

make_var_guard(G, Arg, Guards, F) when is_function(F, 0) ->
    V = variable(Arg),
    {V, make_guard(application(atom(G, Arg), [V, F()]), Guards)};
make_var_guard(G, Arg, Size, Guards) ->
    V = variable(Arg),
    {V, [infix_expr(application(atom(G, Arg), [V]), operator('=:=', Arg), Size)|Guards]}.

type_to_guard(Type) when is_atom(Type) ->
    proplists:get_value(Type,
                        [{atom, is_atom},
                         {binary, is_binary},
                         {bin, is_binary},
                         {bitstring, is_bitstring},
                         {boolean, is_boolean},
                         {bool, is_boolean},
                         {float, is_float},
                         {function, is_function},
                         {'fun', is_function},
                         {integer, is_integer},
                         {int, is_integer},
                         {list, is_list},
                         {string, is_list},
                         {map, is_map},
                         {number, is_number},
                         {num, is_number},
                         {pid, is_pid},
                         {port, is_port},
                         {reference, is_reference},
                         {ref, is_reference},
                         {tuple, is_tuple}]).

type_to_size_guard(Type) when is_atom(Type) ->
    proplists:get_value(Type,
                        [{list, length},
                         {nil, length},
                         {string, length},
                         {tuple, tuple_size},
                         {binary, byte_size},
                         {bin, byte_size},
                         {map, map_size},
                         {any, size},
                         {term, size}]);
type_to_size_guard(A) when is_tuple(A) ->
    type_to_size_guard(case type(A) of
                           atom -> atom_value(A);
                           T -> T
                       end).

copy_pos([S|_], T) -> erl_syntax:copy_pos(S, T);
copy_pos(S, T) -> erl_syntax:copy_pos(S, T).

tuple(L) -> copy_pos(hd(L), erl_syntax:tuple(L)).

list(H, T) -> copy_pos(hd(H), erl_syntax:list(H, T)).

atom(A, P) -> copy_pos(P, erl_syntax:atom(A)).

integer(I, P) -> copy_pos(P, erl_syntax:integer(I)).

variable(V, P) when is_atom(V) -> copy_pos(P, erl_syntax:variable(V)).

variable(V) when is_tuple(V) -> variable(erl_syntax:variable_name(V), V).

application(O, A) -> copy_pos(O, erl_syntax:application(O, A)).

%application(M, N, A) -> copy_pos(M, erl_syntax:application(M, N, A)).

operator(O, P) -> copy_pos(P, erl_syntax:operator(O)).

infix_expr(L, O, R) -> copy_pos(L, erl_syntax:infix_expr(L, O, R)).

conjunction(T) -> copy_pos(T, erl_syntax:conjunction(T)).

disjunction(T) -> copy_pos(T, erl_syntax:disjunction(T)).
