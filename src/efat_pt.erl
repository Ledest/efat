-module(efat_pt).

-export([parse_transform/2]).

-define(OP, '/').

-import(erl_syntax, [concrete/1,
                     type/1,
                     get_pos/1,
                     integer_value/1, atom_value/1,
                     tuple_elements/1,
                     infix_expr_left/1, infix_expr_operator/1, infix_expr_right/1,
                     operator_name/1,
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
                {P, G} -> clause(P,
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
            case patterns_transform(tuple_elements(Pattern)) of
                {[], _} -> {Pattern, Guards};
                {P, G} -> {tuple(P), G ++ Guards}
            end;
        list ->
            {PH, GH} = patterns_transform(erl_syntax:list_prefix(Pattern)),
            {PT, GT} = pattern_transform(erl_syntax:list_suffix(Pattern), []),
            {list(PH, PT), GH ++ GT ++ Guards};
        _ -> {Pattern, Guards}
    end.

do_pattern_transform(Pattern, Guards) ->
    O = infix_expr_operator(Pattern),
    case operator_name(O) of
        ?OP -> do_pattern_transform_op(Pattern, Guards);
        Op ->
            case lists:member(Op, ['<', '>', '=<', '>=', '/=', '=/=', '=:=', '==']) of
                true ->
                    L = infix_expr_left(Pattern),
                    Op2 = infix_expr_operator(L),
                    case type(L) =:= infix_expr andalso operator_name(Op2) of
                        ?OP -> do_pattern_transform_op(infix_expr(infix_expr_left(L), Op2,
                                                                  infix_expr(infix_expr_right(L), O,
                                                                             infix_expr_right(Pattern))),
                                                       Guards);
                        _ -> {Pattern, Guards}
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
    V = variable(Arg),
    if
        T =:= any; T =:= term -> {V, Guards};
        T =:= null; T =:= none; T =:= undefined ->
            {V, make_guard(infix_expr(V, operator('=:=', Arg), atom(T, Arg)), Guards)};
        T =:= record ->
            {V, make_guard(application(atom(is_atom, Arg), [application(atom(element, Arg), [integer(1, Arg), V])]),
                           Guards)};
        true ->
            case type_to_guard(T) of
                undefined -> {Pattern, Guards};
                G -> make_var_guard(G, Arg, Guards)
            end
    end;
do_pattern_transform_op(_Pattern, Guards, Arg, Type, record_expr) ->
    make_var_guard(is_record, Arg, erl_syntax:record_expr_type(Type), Guards);
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
do_pattern_transform_op(Pattern, Guards, Arg, Type, infix_expr) ->
    O = infix_expr_operator(Type),
    case lists:member(operator_name(O), ['<', '>', '=<', '>=', '/=', '=/=', '=:=', '==']) of
        true ->
            {V, [G]} = do_pattern_transform_op(Pattern, [], Arg, infix_expr_left(Type)),
            {V, make_guard(infix_expr(G, operator('andalso', G), infix_expr(V, O, infix_expr_right(Type))), Guards)};
        _ -> {Pattern, Guards}
    end;
do_pattern_transform_op(Pattern, Guards, Arg, Type, prefix_expr) ->
    case operator_name(erl_syntax:prefix_expr_operator(Type)) of
        '-' ->
            {V, [G]} = do_pattern_transform_op(Pattern, [], Arg, erl_syntax:prefix_expr_argument(Type)),
            case type(G) of
                infix_expr -> {V, make_guard(case proplists:get_value(operator_name(infix_expr_operator(G)),
                                                                      [{'<', '>='}, {'>=', '<'},
                                                                       {'>', '=<'}, {'=<', '>'},
                                                                       {'=:=', '=/='}, {'=/=', '=:='},
                                                                       {'==', '/='}, {'/=', '=='}]) of
                                                 undefined -> erl_syntax:prefix_expr(operator('not', G), G);
                                                 O -> infix_expr(infix_expr_left(G), operator(O, G), infix_expr_right(G))
                                             end, Guards)};
                _ -> {Pattern, Guards}
            end;
        _ -> {Pattern, Guards}
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
    {V, make_guard(application(atom(G, Arg), [V]), Guards)}.

make_var_guard(G, Arg, Size, Guards) ->
    V = variable(Arg),
    {V, make_guard(case lists:member(G, [is_function, is_record]) of
                       true -> application(atom(G, Arg), [V, Size]);
                       _ -> infix_expr(application(atom(G, Arg), [V]), operator('=:=', Arg), Size)
                   end, Guards)}.

type_to_guard(Type) when is_atom(Type) ->
    proplists:get_value(Type,
                        [{atom, is_atom},
                         {a, is_atom},
                         {binary, is_binary},
                         {bin, is_binary},
                         {bitstring, is_bitstring},
                         {bit, is_bitstring},
                         {boolean, is_boolean},
                         {bool, is_boolean},
                         {float, is_float},
                         {function, is_function},
                         {func, is_function},
                         {integer, is_integer},
                         {int, is_integer},
                         {i, is_integer},
                         {list, is_list},
                         {l, is_list},
                         {string, is_list},
                         {s, is_list},
                         {map, is_map},
                         {m, is_map},
                         {number, is_number},
                         {num, is_number},
                         {n, is_number},
                         {pid, is_pid},
                         {port, is_port},
                         {reference, is_reference},
                         {ref, is_reference},
                         {record, is_record},
                         {rec, is_record},
                         {r, is_record},
                         {tuple, is_tuple},
                         {t, is_tuple}]).

type_to_size_guard(Type) when is_atom(Type) ->
    proplists:get_value(Type,
                        [{list, length},
                         {l, length},
                         {nil, length},
                         {string, length},
                         {s, length},
                         {tuple, tuple_size},
                         {t, tuple_size},
                         {binary, byte_size},
                         {bin, byte_size},
                         {map, map_size},
                         {m, map_size},
                         {function, is_function},
                         {func, is_function},
                         {record, is_record},
                         {rec, is_record},
                         {r, is_record},
                         {any, size},
                         {term, size}]);
type_to_size_guard(A) when is_tuple(A) ->
    type_to_size_guard(case type(A) of
                           atom -> atom_value(A);
                           T -> T
                       end).

pos(P, T) when is_integer(P) -> erl_syntax:set_pos(P, T);
pos([S|_], T) -> erl_syntax:copy_pos(S, T);
pos(S, T) -> erl_syntax:copy_pos(S, T).

tuple(L) -> pos(hd(L), erl_syntax:tuple(L)).

list(H, T) -> pos(hd(H), erl_syntax:list(H, T)).

atom(A, P) -> pos(P, erl_syntax:atom(A)).

integer(I, P) -> pos(P, erl_syntax:integer(I)).

variable(V, P) when is_atom(V) -> pos(P, erl_syntax:variable(V)).

variable(V) when is_tuple(V) -> variable(erl_syntax:variable_name(V), V).

application(O, A) -> pos(O, erl_syntax:application(O, A)).

%application(M, N, A) -> pos(M, erl_syntax:application(M, N, A)).

operator(O, P) -> pos(P, erl_syntax:operator(O)).

infix_expr(L, O, R) -> pos(L, erl_syntax:infix_expr(L, O, R)).

conjunction(T) -> pos(T, erl_syntax:conjunction(T)).

disjunction(T) -> pos(T, erl_syntax:disjunction(T)).

clause(P, G, B) -> pos(B, erl_syntax:clause(P, G, B)).
