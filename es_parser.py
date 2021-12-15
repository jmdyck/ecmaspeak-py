#!/usr/bin/python3

# ecmaspeak-py/es_parser.py:
# Parse ECMAScript code using an Earley-like approach.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>


import pdb, unicodedata, sys, re
from collections import defaultdict, OrderedDict, namedtuple
from pprint import pprint # mainly for debugging
import misc

from mynamedtuple import mynamedtuple
import shared
from shared import spec, decode_entities, print_tree, stderr
from emu_grammars import GNode

character_named_ = {
    # table-31:
    'ZWNJ'  : '\u200c',
    'ZWJ'   : '\u200d',
    'ZWNBSP': '\ufeff',

    # table-32:
    'TAB'   : '\u0009',
    'VT'    : '\u000b',
    'FF'    : '\u000c',
    # 'ZWNBSP': '\ufeff', # appears above
    # 'USP' : isn't a single character

    # table-33:
    'LF'    : '\u000a',
    'CR'    : '\u000d',
    'LS'    : '\u2028',
    'PS'    : '\u2029',
}

class ParseError(Exception):
    def __init__(self, posn, item_strings):
        self.posn = posn
        self.kernel_item_strings = item_strings

# -----------

# I use very short names here so that when a tokenized RHS is printed, it isn't too long.
# Maybe I'll change my mind about that.
NT            = mynamedtuple('NT', 'n')        # non-terminal
T_lit         = mynamedtuple('T_lit', 'c')     # literal characters
T_u_p         = mynamedtuple('T_u_p', 'p')     # Unicode code point with a Unicode property
T_u_r         = mynamedtuple('T_u_r', 'rlo rhi') # Range of Unicode code points
T_named       = mynamedtuple('T_named', 'n')   # named terminal
C_but_only_if = mynamedtuple('C_but_only_if', 'c')
C_but_not     = mynamedtuple('C_but_not', 'b')
C_no_LT_here  = mynamedtuple('C_no_LT_here', '')
C_lookahead   = mynamedtuple('C_lookahead', 'matches tss')

X_eor         = mynamedtuple('X_eor', '')  # end-of-RHS (Doesn't appear in grammars, is only used in EarleySet.)

END_OF_INPUT  = T_named('_EOI_')
ACCEPTANCE    = T_named('_ACCEPTANCE_')

# -----------

NT           .__str__ = lambda x: x.n
T_lit        .__str__ = lambda x: '"%s"' % x.c
T_u_p        .__str__ = lambda x: f"<any Unicode code point with property '{x.p}'>"
T_u_r        .__str__ = lambda x: f"<range {x.rlo}-{x.rhi}>"
T_named      .__str__ = lambda x: f"<{x.n}>"
C_but_only_if.__str__ = lambda x: f"(but only if {x.c})"
C_but_not    .__str__ = lambda x: f"(but not {' | '.join(str(exc) for exc in x.b)})"
C_no_LT_here .__str__ = lambda x: f"(no LT here)"
C_lookahead  .__str__ = lambda x: f"(lookahead {'is' if x.matches else 'isnt'} {stringify_terminal_sequences(x.tss)})"

def stringify_terminal_sequences(tss):
    return ' | '.join(map(stringify_rthing_sequence, tss))

def stringify_rthing_sequence(ts):
    return ' '.join(str(t) for t in ts)

# -----------

def Rthing_is_nonterminal(rthing):
    return rthing.T == 'NT'

def Rthing_is_terminal(rthing):
    return rthing.T.startswith('T_')

def Rthing_is_constraint(rthing):
    return rthing.T.startswith('C_')

def are_distinct(values):
    return len(set(values)) == len(values)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def simplify_grammar(grammar):
    # Put the grammar in a more parser-friendly form.

    # We simplify it in a few senses:
    # - Convert from GNodes to hashable data structures.
    # - Eliminate certain features:
    #     - Eliminate grammatical parameters (lhs-subscript, rhs-guard, rhs-subscript)
    #       by 'expanding' productions more-or-less as described in the spec.
    #     - Eliminate rhs-labels.
    #     - Eliminate multi-character literals in the lexical grammar.

    # Put the expanded set of productions here:
    grammar.exp_prodns = OrderedDict()

    for (lhs_symbol, production_n) in sorted(grammar.prodn_for_lhs_.items()):
        if 0:
            print()
            print('    ', lhs_symbol, production_n._param_names)
            for rhs_n in production_n._rhss:
                print('        ', rhs_n)

        for params_setting in each_params_setting(production_n._param_names):
            for rhs_n in production_n._rhss:
                simplify_prod(grammar, params_setting, lhs_symbol, rhs_n)

    if grammar.level == 'lexical': make_InputElement_common(grammar)

    # grammar.print_exp_prodns()

    return grammar.exp_prodns

# --------------------------------------------------------------------------

def each_params_setting(params):
    # `params` is a list of grammatical parameters (i.e., just names).
    # Each of them can take on a '+' or '~' setting.
    # Yield every possible combination of settings for these parameters.
    for bools in each_boolean_vector_of_length(len(params)):
        yield [
            ('+' if b else '~') + p
            for (b, p) in zip(bools, params)
        ]

def each_boolean_vector_of_length(n):
    if n == 0:
        yield []
    elif n == 1:
        yield [False]
        yield [True]
    elif n == 2:
        yield [False, False]
        yield [False, True]
        yield [True,  False]
        yield [True,  True]
    elif n == 3:
        yield [False, False, False]
        yield [False, False, True]
        yield [False, True,  False]
        yield [False, True,  True]
        yield [True,  False, False]
        yield [True,  False, True]
        yield [True,  True,  False]
        yield [True,  True,  True]
    else:
        assert 0, n

def expand_nt_wrt_params_setting(nt, params_setting):
    assert type(nt) == GNode
    assert nt.kind == 'GNT'
    result = nt._nt_name
    for (arg_prefix, arg_name) in nt._params:
        if arg_prefix == '?':
            for param_setting in params_setting:
                if param_setting[1:] == arg_name:
                    break
            else:
                # There is no param by that name in params_setting.
                assert 0, nt
            result += param_setting
        elif arg_prefix in ['+', '~']:
            result += arg_prefix + arg_name
            # regardless of whether there's a param_setting
        else:
            assert 0, arg
    return result

# --------------------------------------------------------------------------

def simplify_prod(grammar, params_setting, lhs_symbol, rhs_n):
    exp_lhs_symbol = lhs_symbol + ''.join(params_setting)
    assert rhs_n.kind in ['RHS_LINE', 'BACKTICKED_THING'], rhs_n.kind

    # A RHS_LINE can have a guard.
    if rhs_n.kind == 'RHS_LINE':
        (optional_guard_n, rhs_body_n, optional_label_n) = rhs_n.children

        if all(
            guard_param_n.source_text() in params_setting
            for guard_param_n in optional_guard_n.children
        ):
            # The guard succeeds (in the current `params_setting`).
            pass
        else:
            # The guard fails.
            return

    exp_rhs = []

    for (i, rhs_item_n) in enumerate(rhs_n._rhs_items):

        if rhs_item_n.kind == 'PARAMS':
            # This is a guard, and we've already determined that it succeeds.
            assert i == 0
        elif rhs_item_n.kind == 'LABEL':
            assert i == len(rhs_n._rhs_items)-1

        # ----------------------------------------

        elif rhs_item_n.kind == 'GNT':
            exp_name = expand_nt_wrt_params_setting(rhs_item_n, params_setting)
            nk = grammar.get_name_kind(rhs_item_n._nt_name)
            if nk == 'NT':
                exp_thing = NT(exp_name)
            elif nk == 'T_named':
                exp_thing = T_named(exp_name)
            else:
                assert 0, nk
            if rhs_item_n._is_optional:
                # The spec says that a RHS with N optionals
                # is an abbreviation for 2^N RHSs,
                # one for each combination of optionals being present/absent.
                # However, during parsing,
                # you want all 2^N to be instances of the same production,
                # which is harder if they come from different productions.
                # So instead, treat X? as a non-terminal, defined X? := X | epsilon
                opt_exp_name = exp_name + '?'
                if opt_exp_name not in grammar.exp_prodns:
                    o_lhs = rhs_item_n._nt_name + '?'
                    o_params_setting = params_setting # XXX should be subset
                    add_exp_prod1(grammar, opt_exp_name, [exp_thing], o_lhs, rhs_item_n._nt_name, o_params_setting)
                    add_exp_prod1(grammar, opt_exp_name, [         ], o_lhs,                  '', o_params_setting)
                    # Conceivably, the parser could infer these rules.
                exp_rhs.append(NT(opt_exp_name))
            else:
                exp_rhs.append(exp_thing)

        elif rhs_item_n.kind == 'BACKTICKED_THING':
            chars = rhs_item_n._chars
            if grammar.level == 'lexical' and len(chars) > 1:
                #" A <em>lexical grammar</em> for ECMAScript ...
                #" has as its terminal symbols Unicode code points ...
                #
                # So, in the lexical grammar, we explode multicharacter literals.
                for char in chars:
                    exp_rhs.append(T_lit(char))
            else: 
                exp_rhs.append(T_lit(chars))

        elif rhs_item_n.kind  == 'NAMED_CHAR':
            exp_rhs.append(T_named(rhs_item_n.groups[0]))

        elif rhs_item_n.kind == 'U_PROP':
            exp_rhs.append(T_u_p(rhs_item_n.groups[0]))

        elif rhs_item_n.kind == 'U_RANGE':
            exp_rhs.append(T_u_r(int(rhs_item_n.groups[0],16), int(rhs_item_n.groups[1],16)))

        elif rhs_item_n.kind == 'U_ANY':
            exp_rhs.append(T_u_r(0x0000,0x10FFFF))

        elif rhs_item_n.kind in ['LAC_SINGLE', 'LAC_SET']:

            def convert_terminal_seq_n(terminal_seq_n):
                assert terminal_seq_n.kind == 'TERMINAL_SEQ'
                ts = []
                for terminal_item_n in terminal_seq_n.children:
                    if terminal_item_n.kind == 'BACKTICKED_THING':
                        t = T_lit(terminal_item_n._chars)
                    elif terminal_item_n.kind == 'NAMED_CHAR':
                        t = T_named(terminal_item_n.groups[0])
                    elif terminal_item_n.kind == 'NLTH_BAR':
                        t = C_no_LT_here()
                    else:
                        t = str(terminal_item_n)
                    ts.append(t)
                return tuple(ts)

            if rhs_item_n.kind == 'LAC_SINGLE':
                [lac_single_op, terminal_seq_n] = rhs_item_n.children
                matches = {
                    '==': True,
                    '!=': False,
                }[lac_single_op.source_text()]
                rsymbol = C_lookahead(matches=matches, tss=tuple([convert_terminal_seq_n(terminal_seq_n)]))

            elif rhs_item_n.kind == 'LAC_SET':
                [lac_set_op, lac_set_operand_n] = rhs_item_n.children
                if lac_set_operand_n.kind == 'NT':
                    nt_name = lac_set_operand_n._nt_name
                    # (could precompute these, but probably not worth it)
                    la_prodn = grammar.prodn_for_lhs_[nt_name]
                    tss = []
                    for la_rhs_n in la_prodn._rhss:
                        assert la_rhs_n.kind == 'BACKTICKED_THING'
                        t = T_lit(la_rhs_n._chars)
                        ts = tuple([t])
                        tss.append(ts)
                elif lac_set_operand_n.kind == 'SET_OF_TERMINAL_SEQ':
                    tss = []
                    for terminal_seq_n in lac_set_operand_n.children:
                        tss.append(convert_terminal_seq_n(terminal_seq_n))
                else:
                    assert 0
                rsymbol = C_lookahead(matches=False, tss=tuple(tss))

            else:
                assert 0

            exp_rhs.append(rsymbol)

        elif rhs_item_n.kind == 'BUT_ONLY':
            exp_rhs.append(C_but_only_if(decode_entities(rhs_item_n.groups[0])))

        elif rhs_item_n.kind == 'NLTH':
            exp_rhs.append(C_no_LT_here())

        elif rhs_item_n.kind == 'NT_BUT_NOT':

            def convert_nt(nt_n):
                nt_name = nt_n._nt_name
                if nt_n.kind == 'GNT':
                    assert nt_n._params == []
                    assert nt_n._is_optional == False
                elif nt_n.kind == 'NT':
                    pass
                else:
                    assert 0
                #
                nk = grammar.get_name_kind(nt_name)
                if nk == 'NT':
                    exp_thing = NT(nt_name)
                elif nk == 'T_named':
                    exp_thing = T_named(nt_name)
                else:
                    assert 0, nk
                return exp_thing

            (nt_n, exclusion_n) = rhs_item_n.children

            rsymbol = convert_nt(nt_n)
            exp_rhs.append(rsymbol)

            b = []
            for excludable_n in exclusion_n._excludables:
                if excludable_n.kind == 'NT':
                    ex_symbol = convert_nt(excludable_n)
                elif excludable_n.kind == 'BACKTICKED_THING':
                    ex_symbol = T_lit(excludable_n._chars)
                else:
                    assert 0
                b.append(ex_symbol)
            rsymbol = C_but_not(tuple(b))
            exp_rhs.append(rsymbol)

        else:
            assert 0, rhs_item_n

    add_exp_prod1(grammar, exp_lhs_symbol, exp_rhs, lhs_symbol, rhs_n._reduced, params_setting)

# --------------------------------------------------------------------------

def make_InputElement_common(grammar):
    assert grammar.level == 'lexical'
    lhs = 'InputElement_common'
    for (i, nt_name) in enumerate(['WhiteSpace', 'LineTerminator', 'Comment', 'CommonToken']):
        add_exp_prod1(grammar, lhs, [NT(nt_name)], lhs, nt_name, [])

# --------------------------------------------------------------------------

def add_exp_prod1(grammar, exp_lhs, exp_rhs, og_lhs, og_rhs_reduced, og_params_setting):
    if exp_lhs not in grammar.exp_prodns:
        grammar.exp_prodns[exp_lhs] = []
    exprod = ExProd(exp_lhs, exp_rhs, og_lhs, og_rhs_reduced, og_params_setting)
    grammar.exp_prodns[exp_lhs].append(exprod)

class ExProd(namedtuple('ExProd', 'ex_lhs ex_rhs og_lhs og_rhs_reduced og_params_setting')): pass

# --------------------------------------------------------------------------

def print_exp_prodns(grammar):
    stderr('    print_exp_prodns ...')
    filename = '%s_expanded_grammar' % grammar.name
    f = shared.open_for_output(filename)

    i = 0
    for (exp_lhs, exprods) in grammar.exp_prodns.items():
        for exprod in exprods:
            # print("%3d: " % i, end=None)
            print("%61s -> %s" % (
                    exp_lhs,
                    stringify_rthings(exprod.ex_rhs)
                ),
                file=f
            )
            i += 1
    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

_trace_f = None
_trace_level = None

def trace(*args, **kwargs):
    print(*args, **kwargs, file=_trace_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class _Earley:

    def __init__(this_parser, name, how_much_to_consume, trace_prefix):

        assert how_much_to_consume in ['all', 'as much as possible']

        this_parser.name = name
        this_parser.how_much_to_consume = how_much_to_consume
        this_parser.trace_prefix = trace_prefix

        grammar = spec.grammar_[(name, 'B')]

        this_parser.productions_with_lhs_ = simplify_grammar(grammar)

    # -------------------------------------------------

    def run(
        this_parser,
        goal_symname,
        tip,
        start_ti_pos,
    ):
        # Either returns a single ParseNode, or raises a ParseError.

        def trace_at(trace_level_of_this_msg, *args):
            if trace_level_of_this_msg <= _trace_level:
                print(this_parser.trace_prefix, *args, file=_trace_f)

        def Rsymbol_get_rhs_start_points(rsymbol):
            assert Rthing_is_nonterminal(rsymbol)
            if rsymbol.n not in this_parser.productions_with_lhs_:
                # grammar bug
                raise_parse_error()
            return [
                Point(prod, 0)
                for prod in this_parser.productions_with_lhs_[rsymbol.n]
            ]

        # -------------------------------------------
        # Roughly speaking, a 'Point' is a point in the grammar.
        # i.e., a point in the RHS of some production.
        # (Elsewhere called an LR(0) item,
        # but I'm using "Item" for a slightly bigger concept.)

        class Point(namedtuple('Point', 'prod dot_posn')):

            def __str__(point):
                lhs = point.prod.ex_lhs
                rhs = point.prod.ex_rhs
                # dot = '\u25CF'
                dot = '@'
                return "%s -> %s %s %s " % (
                    lhs,
                    ' '.join(str(r) for r in rhs[0:point.dot_posn]),
                    dot,
                    ' '.join(str(r) for r in rhs[point.dot_posn:])
                )

            def get_rthing_after_dot(point):
                rhs = point.prod.ex_rhs
                if point.dot_posn < len(rhs):
                    return rhs[point.dot_posn]
                elif point.dot_posn == len(rhs):
                    return None
                else:
                    assert 0

            def advance(point):
                # Return the next point after `point`.

                assert point.dot_posn < len(point.prod.ex_rhs)
                # We'd never be asked to advance from the last point in a production.

                return Point(point.prod, point.dot_posn+1)

            def get_prod(point):
                return point.prod

            def get_lhs_symbol(point):
                lhs_symname = point.prod.ex_lhs
                return lhs_symname

        # -------------------------------------------

        class Item(namedtuple('Item', 'cause transit_node resulting_point')):

            def __str__(item):
                return f"_ _ {item.resulting_point}"

            def advance(item, node):
                new_point = item.resulting_point.advance()
                if new_point is None: return None
                return Item(item, node, new_point)

            def get_rthing_after_dot(item):
                rthing = item.resulting_point.get_rthing_after_dot()
                if rthing is None:
                    return X_eor()
                else:
                    return rthing

            def get_derived_items(item, this_set):
                rthing = item.get_rthing_after_dot()

                if rthing is None:
                    assert 0

                elif type(rthing) == X_eor:
                    # There is nothing after the dot.
                    # I.e., the dot is at the end of the RHS.
                    # Perform "Completer":
                    for new_item in item.reduce():
                        yield new_item

                elif Rthing_is_nonterminal(rthing):
                    # Perform "Predictor":
                    for point in Rsymbol_get_rhs_start_points(rthing):
                        yield Item(this_set, None, point)
                    # Aycock + Horspool (2002) say:
                    #     if rthing is nullable, yield item.advance(None)
                    # But if it's *indirectly* nullable,
                    # that would result in a parse tree
                    # that doesn't reflect the substructure.

                elif Rthing_is_terminal(rthing):
                    # Don't perform "Scanner" yet.
                    pass

                elif Rthing_is_constraint(rthing):
                    # trace_at(9, "  CHKING %s" % indent + str(item))
                    trace_at(9, f"  checking constraint {rthing}")
                    constraint_is_satisfied = tip.check_constraint(item.transit_node, this_set.ti_pos, rthing)
                    if constraint_is_satisfied:
                        trace_at(9, f"  constraint is satisfied")
                        yield item.advance(None)
                    else:
                        trace_at(9, f"  constraint is not satisfied, so this item is a dead end")

                    # When closing an Earley-state, and you encounter an item
                    # with a lookahead-constraint in the post-dot position,
                    # what do you do with it? I can think of 3 approaches:
                    #
                    # (1) During closure, ignore the constraint; come back to it later,
                    #     after the requisite number of tokens have been read,
                    #     possibly after all the parsing is done.
                    #
                    #     I think this could work, but might be inefficient,
                    #     because the C_lookahead is there to prevent ambiguities,
                    #     so ignoring it allows ambiguities to multiply.
                    #
                    # (2) During closure, pause and immediately go check
                    #     whether the next few tokens satisfy the constraint.
                    #     If they don't, then delete the item or mark it bad somehow,
                    #     and don't let it contribute to the closure of the state.
                    #
                    #     This would be a sensible approach if ES had a conventional lexer
                    #     (where you can lex a whole text before doing any syntactic parsing).
                    #     But with ES's lexer, the goal symbol depends on the current syntactic context,
                    #     so the lexer can't get ahead of the parser (more than 1 token).
                    #     When you're closing the state, you (theoretically) don't even know
                    #     the current syntactic context, so you can't even get the next token,
                    #     let alone any subsequent ones.
                    #     Practically, the syntactic context is determined by the items in the
                    #     state's kernel, so maybe with some prep-work you could know the context
                    #     and thus get the next token.
                    #     The next+1 would be harder though.
                    #
                    # (3) During closure, allow the item to contribute,
                    #     but modify its contributions so as to enforce the constraint.
                    #     (similar to baking the constraint into the grammar)
                    #
                    #     ?

                else:
                    assert 0, rthing

            def reduce(item):
                trace_at(9, '    reduce:', str(item))

                prod = item.resulting_point.get_prod()

                # "pop items off the stack"
                child_nodes = []
                back_item = item
                while True:
                    if isinstance(back_item.cause, Item):
                        if back_item.transit_node is not None:
                            child_nodes.insert(0, back_item.transit_node)
                        back_item = back_item.cause
                    elif isinstance(back_item.cause, EarleySet):
                        assert back_item.transit_node is None
                        back_set = back_item.cause
                        break
                    else:
                        assert 0, back_item.cause

                if child_nodes:
                    option_bits = ''.join(
                        str(len(child.children))
                        for child in child_nodes
                        if isinstance(child.symbol, str) and child.symbol.endswith('?')
                    )
                    extent = child_nodes
                else:
                    option_bits = ''
                    extent = (eset_ti_pos, eset_ti_pos)

                parent_node = ParseNode((prod, option_bits), extent, tip)

                lhs_symbol = prod.ex_lhs
                back_items = back_set.get_items_expecting_symbol(NT(lhs_symbol))
                if len(back_items) == 0:
                    trace_at(1, )
                    trace_at(1, "no items expecting '%s' in back_set:" % lhs_symbol)
                    back_set.trace(1)
                    assert 0 # because item must have come from somewhere

                # The problem with Earley's algorithm and nullability:
                # If lhs_symbol is nullable,
                # then back_set might be this_set,
                # which is still being built,
                # so back_items might be partial.
                if back_set.is_under_construction:
                    trace_at(1, f"    Set is under construction, so remembering nullable {lhs_symbol}")
                    back_set.nullables.append( (NT(lhs_symbol), parent_node) )
                    # Have back_set remember lhs_symbol and parent_node:
                    # if an item is added to back_set that expects lhs_symbol,
                    # then that's another back_item...

                for back_item in back_items:
                    new_item = back_item.advance(parent_node)
                    if new_item is None:
                        assert 0 # You must be able to advance out of a back_item
                        trace_at(1, "    back_item.advance(...) returned None")
                    else:
                        yield new_item

        # -------------------------------------------

        class EarleySet:
            def __init__(this_set, ti_pos):
                trace_at(9, )
                trace_at(9, f'new set at ti_pos = {ti_pos}...')
                this_set.ti_pos = ti_pos
                this_set.items_with_dot_before_ = defaultdict(list)
                this_set.is_under_construction = True
                this_set.nullables = []

            def trace(this_set, tl):
                trace_at(tl, )
                trace_at(tl, "EarleySet:")
                for (x, items) in sorted(this_set.items_with_dot_before_.items()):
                    trace_at(tl, f'  {x}:')
                    for item in items:
                        trace_at(tl, '    ', str(item))

            def close(this_set, kernel_items):
                for item in kernel_items:
                    this_set._add_and_recurse(item, '')

                this_set.is_under_construction = False

            def _add_and_recurse(this_set, item, indent):
                rthing = item.get_rthing_after_dot()

                if item in this_set.items_with_dot_before_[rthing]:
                    # We've already processed this item, don't have to do anything.
                    return

                trace_at(9, "  ADDING %s" % indent + str(item))
                this_set.items_with_dot_before_[rthing].append(item)

                for (nul_symbol, nul_node) in this_set.nullables:
                    if nul_symbol == rthing:
                        trace_at(9, f"  Recalling nullable {rthing}")
                        new_item = item.advance(nul_node)
                        this_set._add_and_recurse(new_item, indent+' ')

                for new_item in item.get_derived_items(this_set):
                    this_set._add_and_recurse(new_item, indent+' ')

            def get_expected_terminals(this_set):
                result = []
                # XXX optimize
                for (symbol, items) in this_set.items_with_dot_before_.items():
                    if symbol == X_eor(): continue
                    # if Symbol_is_terminal(symbol):
                    for item in items:
                        rthing = item.get_rthing_after_dot()
                        assert rthing == symbol #??
                        if Rthing_is_terminal(rthing) and rthing not in result:
                            result.append(rthing)
                return result

            def get_items_expecting_symbol(this_set, symbol):
                items = this_set.items_with_dot_before_[symbol]
                assert len(items) > 0 or symbol == ACCEPTANCE
                return items

        # -------------------------------------------

        def cannot_continue():
            if this_parser.how_much_to_consume == 'as much as possible':
                #" When a stream of code points is to be parsed
                #" as an ECMAScript |Script| or |Module|,
                #" it is first converted to a stream of input elements
                #" by repeated application of the lexical grammar; ...
                #
                #" The source text is scanned from left to right,
                #" repeatedly taking the longest possible sequence of code points
                #" as the next input element.
                trace_at(2, 'Checking for prior acceptables...')

                if latest_accepting_item is None:
                    trace_at(2, 'nope, none')
                    raise_parse_error()

                else:
                    goal_node = latest_accepting_item.transit_node
                    assert goal_node.production.ex_lhs == goal_symname
                    if _trace_level >= 2:
                        trace_at(2, 'returning prior acceptable:')
                        goal_node.dump(this_parser.trace_prefix + '   ', f=_trace_f)
                    return goal_node

            else:
                #" ... this stream of input elements is then parsed
                #" by a single application of the syntactic grammar.
                #" The input stream is syntactically in error
                #" if the tokens in the stream of input elements
                #" cannot be parsed as a single instance of the goal nonterminal
                #" (|Script| or |Module|), with no tokens left over.
                raise_parse_error()

        def raise_parse_error():
            item_strings = [
                str(item)
                for item in next_kernel_items
            ]
            raise ParseError(eset_ti_pos, item_strings)

        # -------------------------------------------

        trace_at(1, )
        trace_at(1, f"{this_parser.name}.run invoked at ti_pos = {start_ti_pos} with goal '{goal_symname}'")

        if this_parser.how_much_to_consume == 'all':
            # We're looking for an instance of the goal symbol
            # followed by the end of input.
            final_symbol = END_OF_INPUT
        else:
            # We'll accept an instance of the goal symbol
            # that isn't followed by the end of input.
            final_symbol = ACCEPTANCE

        start_production = ExProd(
            ex_lhs = '*START*',
            ex_rhs = [
                NT(n=goal_symname),
                final_symbol
            ],
            og_lhs = '*START*',
            og_rhs_reduced = f"{goal_symname} {final_symbol}",
            og_params_setting = []
        )
        this_parser.productions_with_lhs_['*START*'] = [start_production]

        # And make an item for it:
        initial_item = Item(None, None, Point(start_production, 0))
        next_kernel_items = [initial_item]

        if this_parser.how_much_to_consume == 'as much as possible':
            latest_accepting_item = None

        eset_ti_pos = start_ti_pos
        while True:
            eset = EarleySet(eset_ti_pos)

            eset.close(next_kernel_items)

            if _trace_level >= 3:
                eset.trace(3)

            # -----------------

            expected_terminals = eset.get_expected_terminals()

            if len(expected_terminals) == 0:
                trace_at(2, "No expected terminals! (e.g., due to the failure of a constraint)")
                return cannot_continue()

            if _trace_level >= 9:
                trace_at(9, )
                trace_at(9, 'expected_terminals:')
                strings = [ str(tsymbol) for tsymbol in expected_terminals ]
                for st in sorted(strings):
                    trace_at(9, '  ', st)

            if this_parser.how_much_to_consume == 'as much as possible':
                accepting_items_here = eset.get_items_expecting_symbol(ACCEPTANCE)
                if accepting_items_here:
                    trace_at(9, )
                    trace_at(9, '(there are accepting_items_here)')
                    if len(accepting_items_here) > 1:
                        trace_at(2, "%d items!" % len(accepting_items_here))
                        if _trace_level >= 2:
                            for item in accepting_items_here:
                                trace_at(2, '')
                                item.transit_node.dump(this_parser.trace_prefix + '   ', f=_trace_f)
                        print('NEED TO RESOLVE AMBIGUITY', file=_trace_f) # XXX

                    latest_accepting_item = accepting_items_here[0]

            # -----------------

            ASI_kludge = None
            if this_parser.name.startswith('syntactic') and T_lit(';') in expected_terminals:
                for item in eset.items_with_dot_before_[T_lit(';')]:
                    # trace_at(2, f"point {item.resulting_point}")
                    lhs = item.resulting_point.get_lhs_symbol()
                    if lhs == 'EmptyStatement':
                        assert ASI_kludge is None
                        ASI_kludge = lhs
                    elif lhs.startswith('DoWhileStatement'):
                        assert ASI_kludge is None
                        ASI_kludge = 'DoWhileStatement'

            # -----------------

            result = tip.get_next_terminal_instances(eset_ti_pos, expected_terminals, ASI_kludge)

            trace_at(2, )
            trace_at(2, f"(back in {this_parser.name}.run after return from get_next_terminal_instances...)")

            if result is None:
                # At this point in the source text,
                # none of the expected terminals was seen.
                trace_at(3, "gnti returned no terminal instances!")
                return cannot_continue()

            # -----------------

            (rats, next_ti_pos) = result
            # "rats" = rsymbols and terminal-instances

            if _trace_level >= 3:
                trace_at(3, )
                trace_at(3, f'gnti returned {len(rats)} matches:')
                for (rsymbol, termin) in rats:
                    trace_at(3, "  For the expected terminal symbol:")
                    trace_at(3, "    " + str(rsymbol))
                    trace_at(3, "  we have the terminal instance:")
                    termin.dump(this_parser.trace_prefix + '     ', f=_trace_f)
                    trace_at(3, )
                trace_at(3, f'and next_ti_pos = {next_ti_pos}')

            assert eset_ti_pos <= next_ti_pos
            # It would be strictly less-than, except for inserted semicolons.

            # -------------------------------------

            # print('...', file=sys.stderr)
            next_kernel_items = []
            for (rsymbol, termin) in rats:
                for item in eset.get_items_expecting_symbol(rsymbol):
                    # print(rsymbol, file=sys.stderr)
                    # if _trace_level >= 9 and rsymbol == T_lit(';'): pdb.set_trace()
                    new_item = item.advance(termin)
                    # print(new_item, file=sys.stderr)
                    if new_item is None:
                        print('got None when attempting to advance', item, termin)
                        assert 0
                    else:
                        next_kernel_items.append(new_item)

            if _trace_level >= 9:
                trace_at(9, )
                trace_at(9, 'next_kernel_items:')
                for item in next_kernel_items:
                    trace_at(9, '  ', str(item))
                if len(next_kernel_items) == 0:
                    trace_at(9, '  ', 'None!')

            assert len(next_kernel_items) > 0

            # -------------------------------------

            if len(rats) == 1 and rats[0][1].symbol == END_OF_INPUT:
                trace_at(1, 'success!')
                trace_at(1, "results:")
                valid_trees = []
                for end_item in next_kernel_items:
                    assert end_item.transit_node.symbol == END_OF_INPUT
                    prev_item = end_item.cause
                    assert isinstance(prev_item, Item)
                    goal_node = prev_item.transit_node
                    assert goal_node.symbol == re.sub('[~+]\w+', '', goal_symname)
                    valid_trees.append(goal_node)
                    if _trace_level >= 1:
                        goal_node.dump(f=_trace_f)

                n_valids = len(valid_trees)
                if n_valids == 0:
                    assert 0
                elif n_valids == 1:
                    [result] = valid_trees
                else:
                    print(f'AMBIGUITY? {n_valids} RESULT TREES', file=_trace_f)
                    print('comparing two:', file=_trace_f)
                    show_ambiguity(valid_trees[0], valid_trees[1], _trace_f)
                    result = valid_trees[0]
                return result

            eset_ti_pos = next_ti_pos

        assert 0 # unreachable

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def gather_char_sets(productions_with_lhs_):
    global char_set_

    def recurse(name):
        result = set()
        for prod in productions_with_lhs_[name]:
            assert len(prod.ex_rhs) == 1
            [rsymbol] = prod.ex_rhs
            if rsymbol.T == 'T_lit':
                result.add( rsymbol.c )
            elif rsymbol.T == 'T_named':
                result.add( character_named_[rsymbol.n] )
            elif rsymbol.T == 'NT':
                result.update( recurse(rsymbol.n) )
            else:
                assert 0, rsymbol.T
        # print("recurse: '%s' : %s" % (name, result))
        return result

    char_set_ = {}
    for n in [
        'LineTerminator',
        'EscapeCharacter',
        'HexDigit',
        'OctalDigit',
        'SyntaxCharacter',
        # UnicodeIDContinue
    ]:
        char_set_[n] = recurse(n)
        # print("char set '%s' = %s" % (n, char_set_[n]))

# ------------------------------------------------------------------------------

def gather_ReservedWords(productions_with_lhs_):
    # kludgy, but anything non-kludgy would be over-engineered
    global ReservedWords
    ReservedWords = set()

    def recurse(name):
        for prod in productions_with_lhs_[name]:
            assert len(prod.ex_rhs) == 1
            [rsym] = prod.ex_rhs
            t = rsym.T
            if t == 'NT':
                # (not actually used any more, but keep it just in case)
                recurse(rsym.n)
            elif t == 'T_lit':
                ReservedWords.add(rsym.c)

    recurse('ReservedWord')
    # print('ReservedWords:', sorted(ReservedWords))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

g_outdir = '../ecma262/_main' # XXX Should be able to set this dynamically.
shared.register_output_dir(g_outdir)
spec.restore()

lexical_earley = _Earley('lexical', 'as much as possible', '| ')
syntactic_earley = _Earley('syntactic', 'all', '')

gather_char_sets(lexical_earley.productions_with_lhs_)

gather_ReservedWords(syntactic_earley.productions_with_lhs_) # for "but not ReservedWord"

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse(subject, goal_symname, trace_level=0, trace_f=sys.stdout):
    # Using `lexical_earley` and `syntactic_earley`,
    # attempt to parse the given `subject`,
    # using `goal_symname` as the goal symbol.
    #
    # Return a single node or raise an Error.

    global _trace_f, _trace_level
    _trace_f = trace_f
    _trace_level = trace_level

    assert isinstance(goal_symname, str)
    if '[' in goal_symname:
        # It has grammatical parameters.
        # Convert to the 'expanded' name.
        # E.g., "Pattern[+U, +N]" -> "Pattern+U+N")
        goal_symname = (
            goal_symname
            .replace('[', '')
            .replace(', ', '')
            .replace(']', '')
        )

    if goal_symname in syntactic_earley.productions_with_lhs_:
        if isinstance(subject, str):
            text_posn = 0
            lex_tip = LexicalTIP(subject)
            syn_tip = SyntacticTIP(subject, lex_tip)

        elif isinstance(subject, ParseNode):
            stderr('REPARSE!!')
            assert isinstance(subject.tip, SyntacticTIP)
            syn_tip = subject.tip
            syn_tip.set_reparse_bounds(subject.start_posn, subject.end_posn)
            text_posn = subject.start_posn

        else:
            assert 0

        node = syntactic_earley.run(
            goal_symname,
            syn_tip,
            text_posn
        )

    elif goal_symname in lexical_earley.productions_with_lhs_:
        # This has some commonalities with the syntactic case above,
        # so I could merge+differentiate,
        # but I don't think the result would be clear.
        assert isinstance(subject, str)
        text_posn = 0
        lex_tip = LexicalTIP(subject)

        node = lexical_earley.run(
            goal_symname,
            lex_tip,
            text_posn
        )

        # Since lexical_earley tries to consume "as much as possible",
        # it might return a node that covers
        # some but not all of the available text.
        # But we're only interested in a node that covers all of the available text.
        # (Should there be a different lexical earley that tries to consume all?)
        if node.end_posn != len(subject):
            raise ParseError(node.end_posn, [f"found a valid {goal_symname}, but it did not consume all of subject"])

    else:
        assert 0, f"Unknown goal symbol {goal_symname!r}"

    node.parent = None
    add_parent_links(node)
    return node

# --------------------------------------------------------------------------

def add_parent_links(node):
    # Note that we can't add parent links during the parsing process,
    # because a node can be a provisional child of multiple other nodes
    # (under different competing parses).
    # It's only when one parse 'wins' that a node has a unique parent.
    for child in node.children:
        child.parent = node
        add_parent_links(child)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# TIP = Terminal Instance Provider
# i.e. it provides instances of terminal symbols to an Earley object.
# via the `get_next_terminal_instances` method.
# Also handles `check_constraint`.

class SyntacticTIP:
    def __init__(syn_tip, source_text, lexical_tip):
        syn_tip.source_text = source_text
        syn_tip.lexical_tip = lexical_tip

        syn_tip.temp_posn_of_latest_asi = -1

        syn_tip._input_elements = []  # A list of all input elements (incl tokens).
        syn_tip._tokens = []          # A list of just the tokens.
        syn_tip._current_token_i = -1 # The index in self._tokens of the current token.
        syn_tip._scouting_text_posn = 0
        syn_tip._lexing_is_done = False
        syn_tip._scout_ahead()
        syn_tip._end_token_i = sys.maxsize

    def show_current_state(syn_tip, when_blurb):
        return
        print(when_blurb + ':')
        print('  ies_i tok_i extent  text')
        next_tok_i = 0
        for (ies_i, ie) in enumerate(syn_tip._input_elements):
            if next_tok_i < len(syn_tip._tokens) and ie is syn_tip._tokens[next_tok_i]:
                tok_i_thing = '%4d' % next_tok_i
                if next_tok_i == syn_tip._current_token_i:
                    tok_i_thing += '*'
                else:
                    tok_i_thing += ' '
                next_tok_i += 1
            else:
                tok_i_thing = ''
            assert ie.ies_i == ies_i
            hm = ' ' if ie.ies_i == ies_i else '!'
            print(f"  {ies_i:5} {tok_i_thing:5} {ie.ies_i:5}{hm} [{ie.start_posn:2}:{ie.end_posn:2}] {ie.text()}")
        print('---')

    def get_next_terminal_instances(syn_tip, text_posn, expected_terminals, ASI_kludge):
        if _trace_level >= 2:
            trace()
            trace(f': syn_tip.get_next_terminal_instances called at text_posn = {text_posn}, which starts at text_posn = {text_posn}:')
            trace(':')
            trace(misc.display_position_in_text(syn_tip.source_text, text_posn, indent=': '), end='')

        # But we barely use {text_posn},
        # because we know that Earley will ask for things in order.

        # ------------------------------

        # When the syntactic parser wants its next terminal (token),
        # it runs the lexical parser to find an input element.

        lexical_goal = syn_tip.get_lexical_goal_symbol(expected_terminals)

        if _trace_level >= 2:
            trace(':')
            trace(f': based on expected_terminals, lexical_goal = {lexical_goal}')
            trace(':')

        # ------------------------------

        token = syn_tip.advance_token_cursor(lexical_goal)

        if _trace_level >= 2:
            trace()
            trace(':')
            trace(f': So the input-element stream has returned the token-tree:')
            token.dump(':  ', f=_trace_f)

        # ------------------------------

        named_token = syn_tip.get_named_token(token)
        token_name = '' if named_token is None else named_token.symbol

        token_text = token.text()

        # not sure how to handle this:
        if token.symbol == T_lit(';') and token.start_posn == token.end_posn:
            # This is an automatically-inserted semicolon.
            assert token_text == ''
            token_text = ';'

        # ------------------------------

        if _trace_level >= 2:
            trace(':')
            trace(': Now we check which (if any) of the expected_terminals match that...')

        matches = []
        for expected_symbol in expected_terminals:
            assert type(expected_symbol) in [T_lit, T_named]

            if expected_symbol == END_OF_INPUT and token.symbol == END_OF_INPUT:
                match_token = token

            elif type(expected_symbol) == T_lit and expected_symbol.c == token_text:
                #! match_token = ParseNode(T_lit(token_text), (token_i, token_i+1), syn_tip)
                match_token = ParseNode(T_lit(token_text), (token.start_posn, token.end_posn), syn_tip)

            elif type(expected_symbol) == T_named and expected_symbol.n == token_name:
                match_token = named_token

            else:
                # no match
                continue

            matches.append((expected_symbol, match_token))

        if matches:
            if _trace_level >= 2:
                trace(':')
                trace(': matching symbols:')
                for match in matches:
                    trace(':   ', match[0])
                trace(':')
                trace(f': which syn_tip.get_next_terminal_instances returns with next_text_posn={token.end_posn}')
            return (matches, token.end_posn)

        else:
            if _trace_level >= 2: trace(": The token we found is not expected by the parser.")

            if token.symbol == END_OF_INPUT:
                # ASI rule #2:
                #" When, as the source text is parsed from left to right,
                #" the end of the input stream of tokens is encountered
                #" and the parser is unable to parse the input token stream
                #" as a single instance of the goal nonterminal,
                #" then a semicolon is automatically inserted
                #" at the end of the input stream. 
                if _trace_level >= 2: trace(': so ASI rule #2 says to insert a semicolon at the end of the input stream')

            else:
                # ASI rule 1:
                #" When, as the source text is parsed from left to right,
                #" a token (called the offending token) is encountered
                #" that is not allowed by any production of the grammar,
                #" then a semicolon is automatically inserted
                #" before the offending token
                #" if one or more of the following conditions is true:
                #"  - The offending token is separated from the previous token
                #"    by at least one LineTerminator.
                #"  - The offending token is }.
                #"  - The previous token is ) and the inserted semicolon
                #"    would then be parsed as the terminating semicolon
                #"    of a do-while statement (13.7.2).
                if (
                    syn_tip.a_LineTerminator_occurs_in_gap_before_current_token()
                    or
                    token.text() == '}'
                    or
                    ASI_kludge == 'DoWhileStatement'
                ):
                    if _trace_level >= 2: trace(": ASI rule #1 says to insert a semicolon before it.")
                else:
                    return None

            if text_posn == syn_tip.temp_posn_of_latest_asi:
                if _trace_level >= 2:
                    trace(": but we've already inserted one here.")
                    trace(": Aborting to avoid infinite ASI loop.")
                return None
            syn_tip.temp_posn_of_latest_asi = text_posn

            expected_semicolon_symbols = [
                tsymbol
                for tsymbol in expected_terminals
                if tsymbol.T == 'T_lit' and tsymbol.c == ';'
            ]
            if _trace_level >= 2:
                trace(": expected_semicolon_symbols:")
                for tsymbol in expected_semicolon_symbols:
                    trace(f":     {tsymbol}")
                if len(expected_semicolon_symbols) == 0:
                    trace(":     (none)")

            if len(expected_semicolon_symbols) == 0:
                # e.g. 036f6b8da7e53ee5.js: `({get `
                #  or  0ff3826356c94f67.js: `({function} = 0)`
                if _trace_level >= 2:
                    trace(": but a semicolon isn't expected here, so giving up.")
                return None

            assert len(expected_semicolon_symbols) == 1
            [semicolon_symbol] = expected_semicolon_symbols

            #" 11.9.1 Rules of Automatic Semicolon Insertion
            #" However, there is an additional overriding condition on the preceding rules:
            #" a semicolon is never inserted automatically
            #" [1] if the semicolon would then be parsed as an empty statement
            #" or
            #" [2] if that semicolon would become one of the two semicolons
            #" in the header of a for statement (see 13.7.4). XXX not handling this yet
            if ASI_kludge == 'EmptyStatement':
                if _trace_level >= 2:
                    trace(": but that semicolon would then be parsed as an empty statement, so we can't insert it.")
                return None

            # XXX
            # one is hidden inside LexicalDeclaration.
            # test case: for ( let i = 0 i < 10; i++ ) foo(i);
            # ASI is not allowed to insert the missing semicolon,
            # but my code will currently do so.
            #
            # And I can't just mark the semicolon in LexicalDeclaration as an ASI_override,
            # because that would affect every occurrence of LexicalDeclaration,
            # which would not be correct.
            # (i.e., ASI *is* allowed to insert the semicolon that ends a LexicalDeclaration
            # if it's not the child of a for-loop.)

            node = ParseNode(T_lit(';'), (text_posn, text_posn), syn_tip)

            syn_tip.insert_before_current_token(node)
            return ([(semicolon_symbol, node)], text_posn) # NOT next_text_posn

    # --------------------------------------------------------------------------

    def get_named_token(syn_tip, token):
        # {token} is an InputElement* ParseNode.
        # But the syntactic grammar makes no reference
        # to InputElement or CommonToken or Punctuator etc,
        # and the syntactic parser won't know what to do
        # if we hand it such a thing.

        if token.symbol == END_OF_INPUT:
            return None

        tok = token
        while True:
            if tok.symbol in [
                'InputElementDiv',
                'InputElementRegExp',
                'InputElementRegExpOrTemplateTail',
                'InputElementTemplateTail',
                'InputElement_common',
                    'TemplateSubstitutionTail',
                    'CommonToken',
                        'Template',
            ]:
                # The syntactic parser isn't interested in {tok} per se,
                # so keep descending.
                assert len(tok.children) == 1
                [tok] = tok.children

            elif tok.symbol in [
                'IdentifierName',
                'NoSubstitutionTemplate',
                'NumericLiteral',
                'RegularExpressionLiteral',
                'StringLiteral',
                'TemplateHead',
                'TemplateMiddle',
                'TemplateTail',
                # (This list can be obtained by scanning the syntactic grammar
                # for named symbols that appear on a RHS but but not a LHS.)
            ]:
                # {tok} itself is something that the syntactic parser could be expecting.
                return tok

            elif tok.symbol in [
                'Punctuator',
                'DivPunctuator',
                'RightBracePunctuator',
            ]:
                return None

            elif tok.symbol == T_lit(';'):
                return None

            else:
                assert 0, tok.symbol

        assert 0

    # --------------------------------------------------------------------------

    def get_lexical_goal_symbol(syn_tip, expected_terminals):
        # https://tc39.es/ecma262/#sec-ecmascript-language-source-code
        # 11. ECMAScript Language: Lexical Grammar
        # 
        #" There are several situations where the identification of lexical input elements
        #" is sensitive to the syntactic grammar context that is consuming the input elements.
        #" This requires multiple goal symbols for the lexical grammar.
        #"
        #" The |InputElementRegExpOrTemplateTail| goal
        #" is used in syntactic grammar contexts where
        #" a |RegularExpressionLiteral|, a |TemplateMiddle|, or a |TemplateTail| is permitted.
        #"
        #" The |InputElementRegExp| goal symbol
        #" is used in all syntactic grammar contexts where
        #" a |RegularExpressionLiteral| is permitted
        #" but neither a |TemplateMiddle|, nor a |TemplateTail| is permitted.
        #"
        #" The |InputElementTemplateTail| goal
        #" is used in all syntactic grammar contexts where
        #" a |TemplateMiddle| or a |TemplateTail| is permitted
        #" but a |RegularExpressionLiteral| is not permitted.
        #"
        #" In all other contexts,
        #" |InputElementDiv| is used as the lexical goal symbol.

        permitted = [
            rsymbol.n
            for rsymbol in expected_terminals
            if rsymbol.T == 'T_named'
        ]

        REL_is_permitted = ('RegularExpressionLiteral' in permitted)

        TemplateTail_is_permitted = ('TemplateTail' in permitted)
        assert TemplateTail_is_permitted == ('TemplateMiddle' in permitted)

        if REL_is_permitted and TemplateTail_is_permitted:
            return 'InputElementRegExpOrTemplateTail'
        elif REL_is_permitted and not TemplateTail_is_permitted:
            return 'InputElementRegExp'
        elif TemplateTail_is_permitted and not REL_is_permitted:
            return 'InputElementTemplateTail'
        else:
            return 'InputElementDiv'

    # --------------------------------------------------------------------------

    def check_constraint(syn_tip, prec_node, text_posn, constraint):
        # Return True if the constraint is satisfied, False if not.

        if type(constraint) == C_lookahead:
            any_ts_matches_lookahead = any(
                syn_tip.lookahead_matches_terminal_sequence(ts, text_posn)
                for ts in constraint.tss
            )
            if constraint.matches:
                # The constraint requires that the lookahead match
                # any of the terminal-seqs in the LAC.
                return any_ts_matches_lookahead
            else:
                # The constraint requires that the lookahead not match
                # any of the terminal-seqs in the LAC.
                return not any_ts_matches_lookahead

        elif type(constraint) == C_no_LT_here:
            #" If the phrase "[no LineTerminator here]" appears
            #" in the right-hand side of a production of the syntactic grammar,
            #" it indicates that the production is a restricted production:
            #" it may not be used if a LineTerminator occurs in the input stream
            #" at the indicated position.
            return not syn_tip.a_LineTerminator_occurs_in_gap_after_current_token()

        elif type(constraint) == C_but_not:
            # In the syntactic grammar, there's only one occurrence of "but not":
            # Identifier : IdentifierName but not ReservedWord
            assert prec_node.symbol == 'IdentifierName'
            assert constraint.b == (NT('ReservedWord'),)
            return prec_node.text() not in ReservedWords

        else:
            assert 0, constraint

    # ==========================================================================

    def get_text_posn(syn_tip, token_i):
        if token_i < len(syn_tip._tokens):
            text_posn = syn_tip._tokens[token_i].start_posn
        else:
            assert token_i == len(syn_tip._tokens)
            text_posn = syn_tip._input_elements[-1].end_posn
        return text_posn

    def set_reparse_bounds(syn_tip, start_posn, end_posn):

        # This could be more efficient, but it probably doesn't need to be.
        [token_k_start] = [
            token_k
            for (token_k,token) in enumerate(syn_tip._tokens)
            if token.start_posn == start_posn
        ]
        token_k_end = min(
            token_k
            for (token_k, token) in enumerate(syn_tip._tokens)
            if token.start_posn >= end_posn
        )
        # pprint(ies._tokens[token_k_start].__dict__)
        # pprint(ies._tokens[token_k_end].__dict__)

        syn_tip._current_token_i = token_k_start - 1
        # minus 1 because advance_token_cursor starts by adding 1.
        syn_tip._end_token_i = token_k_end

    def advance_token_cursor(syn_tip, lexical_goal):

        syn_tip._current_token_i += 1
        if _trace_level >= 3:
            trace(f": Advancing _current_token_i to {syn_tip._current_token_i}")

        assert syn_tip._current_token_i <= syn_tip._end_token_i
        if syn_tip._current_token_i == syn_tip._end_token_i:
            token = syn_tip._tokens[syn_tip._current_token_i]
            text_posn = token.start_posn
            input_element = ParseNode(END_OF_INPUT, (text_posn, text_posn), syn_tip.lexical_tip)
            return input_element

        assert syn_tip._current_token_i <= len(syn_tip._tokens)
        if syn_tip._current_token_i < len(syn_tip._tokens):
            if _trace_level >= 3:
                trace(f": ... which is a previously-scouted token.")
        else:
            if _trace_level >= 3:
                trace(f": ... The cursor has caught up with the scouting frontier,")
                trace(f":     so need to scout_ahead...")
            assert syn_tip._get_one_input_element(lexical_goal)
            assert syn_tip._current_token_i < len(syn_tip._tokens)
            syn_tip._scout_ahead()

        return syn_tip._tokens[syn_tip._current_token_i]

    # --------------------------------------------------------------------------

    def _scout_ahead(syn_tip):
        try:
            while syn_tip._get_one_input_element('InputElement_common'):
                pass
        except ParseError:
            # The source_text, starting at syn_tip._scouting_text_posn,
            # doesn't match InputElement_common.
            # It might be that there's a syntax error here,
            # or it might be that we just need to use the correct goal symbol.
            # In general, we can't know which of those is the case
            # until we know the correct goal symbol.
            # So just suspend scouting until then.
            pass
        syn_tip.show_current_state("After _scout_ahead")

    # --------------------------------------------------------------------------

    def _get_one_input_element(syn_tip, lexical_goal):

        if syn_tip._lexing_is_done: return False

        # --------------------------
        # Get the next input element

        if syn_tip._scouting_text_posn == len(syn_tip.source_text):
            syn_tip._lexing_is_done = True
            input_element = ParseNode(END_OF_INPUT, (syn_tip._scouting_text_posn, syn_tip._scouting_text_posn), syn_tip.lexical_tip)

        else:
            input_element = lexical_earley.run(
                lexical_goal,
                syn_tip.lexical_tip,
                syn_tip._scouting_text_posn
            )

            assert isinstance(input_element, ParseNode)

            assert input_element.start_posn == syn_tip._scouting_text_posn
            assert input_element.start_posn < input_element.end_posn

            syn_tip._scouting_text_posn = input_element.end_posn

        # ---------------------
        # Install the input element in the stream

        input_element.ies_i = len(syn_tip._input_elements) 
        syn_tip._input_elements.append(input_element)

        if (
            len(input_element.children) == 1
            and input_element.children[0].symbol in ['WhiteSpace', 'LineTerminator', 'Comment']
        ):
            # It's a non-token
            pass
        else:
            # It's a token
            # (or it's an end-of-source-text marker that we're going to treat as a token)
            syn_tip._tokens.append(input_element)

        syn_tip.show_current_state("In _get_one_input_element, after installing input element")

        return True

    # --------------------------------------------------------------------------

    def insert_before_current_token(syn_tip, token_to_insert):
        current_token = syn_tip._tokens[syn_tip._current_token_i]
        assert syn_tip._input_elements[current_token.ies_i] is current_token

        # Insert token into _input_elements where the current_token is,
        # shifting subsequents one to the right.
        token_to_insert.ies_i = current_token.ies_i
        syn_tip._input_elements.insert(current_token.ies_i, token_to_insert)
        for tok in syn_tip._tokens[syn_tip._current_token_i:]:
            tok.ies_i += 1

        # Insert token into _tokens
        syn_tip._tokens.insert(syn_tip._current_token_i, token_to_insert)

        # Keep syn_tip._current_token_i the same,
        # so the token just inserted is now the current_token.

        syn_tip.show_current_state("After insert_before_current_token")

    # --------------------------------------------------------------------------

    def a_LineTerminator_occurs_in_gap_before_current_token(syn_tip):
        return syn_tip.rel_gap_contains_a_LineTerminator(-1)

    def a_LineTerminator_occurs_in_gap_after_current_token(syn_tip):
        return syn_tip.rel_gap_contains_a_LineTerminator(+1)

    # ----------------------------------------------------------------------

    def lookahead_matches_terminal_sequence(syn_tip, ts, TEMP_text_posn):
        # The "lookahead" is the sequence of input elements that immediately follows
        # the current token.
        # Return True iff the lookahead matches {ts}, a sequence of terminals.

        # More precisely, each element of {ts} is either a T_lit or a C_no_LT_here.
        assert all(
            type(t) in [T_lit, C_no_LT_here]
            for t in ts
        )

        # This is coded very non-generally,
        # but it's clearer than general code would be,
        # and it's unlikely to be invalidated.
        # If the grammar ever changes in such a way that some assertion here fails,
        # I'll consider rewriting.
        if len(ts) == 1:
            [term1] = ts
            assert type(term1) == T_lit
            return (
                syn_tip.rel_token_matches_symbol(1, term1)
            )

        elif len(ts) == 2:
            [term1, term2] = ts
            assert type(term1) == T_lit
            assert type(term2) == T_lit
            return (
                syn_tip.rel_token_matches_symbol(1, term1)
                and
                syn_tip.rel_token_matches_symbol(2, term2)
            )

        elif len(ts) == 3:
            [term1, nlth, term2] = ts
            assert type(term1) == T_lit
            assert type(nlth)  == C_no_LT_here
            assert type(term2) == T_lit
            return (
                syn_tip.rel_token_matches_symbol(1, term1)
                and
                not syn_tip.rel_gap_contains_a_LineTerminator(2)
                and
                syn_tip.rel_token_matches_symbol(2, term2)
            )

        else:
            assert 0

    # ----------------------------------------------------------------------
    # "rel" means "relative to the current token".
    #
    # The current token is at token_offset=0.
    #
    # Tokens to its right are at token_offset=+1, +2, ...
    # Tokens to its left are at token_offset=-1, -2,  ...
    #
    # Between any two adjacent tokens is a "gap",
    # consisting of zero or more non-tokens.
    # Likewise, there's a gap before the first token and after the last.
    # Gaps to the right of the current token are at gap_offset=+1, +2, ...
    # Gaps to the left of the current token are at gap_offset=-1, -2, ...
    # (gap_offset=0 is meaningless)
    #
    # I.e., the neighborhood of the current token (from left to right) is:
    # - token at token_offset = -1 ("the previous token")
    # - gap   at gap_offset   = -1
    # - token at token_offset =  0 ("the current token")
    # - gap   at gap_offset   = +1
    # - token at token_offset = +1 ("the next token")

    def rel_token_matches_symbol(syn_tip, token_offset, terminal):
        assert type(terminal) == T_lit
        token_i = syn_tip._current_token_i + token_offset
        if 0 <= token_i < len(syn_tip._tokens):
            token = syn_tip._tokens[token_i]
            # We can't just test whether (token.symbol == terminal).
            # For one thing, {terminal} is a T_lit,
            # whereas {token.symbol} is an NT for some InputElement*.
            # You might consider going 'down' from {token},
            # looking for a T_lit that matches {terminal},
            # and that might work in some cases, but not in general.
            # Instead, what works is to ignore all of {token}'s substructure,
            # and just ask if its text matches {terminal}'s chars
            return (token.text() == terminal.c)

            trace(terminal)
            token.dump(f=trace_f)
            def is_at_some_level(token, terminal):
                if token.symbol == terminal:
                    return True
                if len(token.children) != 1:
                    return False
                [child] = token.children
                return is_at_some_level(child, terminal)
            return is_at_some_level(token, terminal)
        else:
            # {token_offset} indicates a spot that doesn't exist.
            # It might be past the rightmost token in the source text,
            # or it might be a spot that will eventually be filled in,
            # but hasn't been 'scouted' yet.
            #
            # The spec says:
            #" ... it is considered an editorial error
            #" for a token sequence _seq_ to appear in a lookahead restriction
            #" (including as part of a set of sequences)
            #" if the choices of lexical goal symbols to use
            #" could change whether or not _seq_
            #" would be a prefix of the resulting token sequence.
            #
            # That is, everything in _seq_ must match InputElement_common.
            # So if there is a match, all necessary input elements must have been scouted.
            # Conversely, if an input element hasn't been scouted, it can't be a match.
            return False

    def rel_gap_contains_a_LineTerminator(syn_tip, gap_offset):
        assert syn_tip._current_token_i < len(syn_tip._tokens)
        curr_token_ies_i = syn_tip._tokens[syn_tip._current_token_i].ies_i

        if gap_offset < 0:
            preceding_tok_offset = gap_offset
        elif gap_offset > 0:
            preceding_tok_offset = gap_offset - 1
        else:
            assert 0

        preceding_token_i = syn_tip._current_token_i + preceding_tok_offset
        following_token_i = preceding_token_i + 1

        assert -1 <= preceding_token_i <  len(syn_tip._tokens)
        assert  0 <= following_token_i <= len(syn_tip._tokens)

        prec_token_ies_i = (
            syn_tip._tokens[preceding_token_i].ies_i
            if preceding_token_i >= 0
            else -1
        )
        foll_token_ies_i = (
            syn_tip._tokens[following_token_i].ies_i
            if following_token_i < len(syn_tip._tokens)
            else len(syn_tip._input_elements)
        )

        return syn_tip.a_LineTerminator_occurs_in(syn_tip._input_elements[prec_token_ies_i+1 : foll_token_ies_i])

    def a_LineTerminator_occurs_in(syn_tip, non_tokens):
        assert isinstance(non_tokens, list)
        for non_token in non_tokens:
            assert non_token.symbol.startswith('InputElement')
            assert len(non_token.children) == 1
            [child] = non_token.children
            assert child.symbol in ['WhiteSpace', 'LineTerminator', 'Comment']
            if child.symbol == 'LineTerminator':
                return True
            elif child.symbol == 'Comment' and child.contains_a('LineTerminator'):
                #" if a |MultiLineComment| contains a line terminator code point,
                #" then the entire comment is considered to be a |LineTerminator|
                #" for purposes of parsing by the syntactic grammar.
                return True
        return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class LexicalTIP:
    def __init__(lex_tip, source_text):
        lex_tip.source_text = source_text

    def get_next_terminal_instances(lex_tip, text_posn, expected_terminals, ASI_kludge):
        # For LexicalTIP, a "ti_position" is an index into the source_text.

        assert ASI_kludge is None

        if text_posn > len(lex_tip.source_text):
            assert 0
        elif text_posn == len(lex_tip.source_text):
            if _trace_level >= 2:
                trace("|+")
                trace("|+   posn: %d  (at end of input)" % text_posn)

            return None

        c = lex_tip.source_text[text_posn]

        if _trace_level >= 2:
            trace("|+")
            trace("|+   posn: %d  char: '%s'" % (text_posn, c))

        rats = []
        for rthing in expected_terminals:
            if lexical_Rsymbol_matches_char(rthing, c):
                node = ParseNode(rthing, (text_posn, text_posn+1), lex_tip)
                rats.append((rthing, node))

        if len(rats) == 0:
            if _trace_level >= 2:
                trace('|+')
                trace("|+   which doesn't match anything in expected_terminals!")

            return None

        else:
            if _trace_level >= 2:
                trace('|+')
                trace('|+   which matches the following expected_terminals:')
                for (rsymbol, node) in rats:
                    trace('|+   ', rsymbol)

            return (rats, text_posn+1)

    # --------------------------------------------------------------------------

    def check_constraint(lex_tip, prec_node, text_posn, constraint):
        if type(constraint) == C_but_not:
            return not char_matches_any_of_the_symbols(prec_node.text(), constraint.b)

        elif type(constraint) == C_but_only_if:
            if 'MV of |HexDigits|' in constraint.c:
                assert prec_node.symbol == 'HexDigits'
                HexDigits_text = prec_node.text()
                # XXX Properly, we should invoke the MV SDO here.
                HexDigits_MV = int(HexDigits_text, 16)
                if constraint.c == 'MV of |HexDigits| &le; 0x10FFFF':
                    return (HexDigits_MV <= 0x10FFFF)
                elif constraint.c == 'MV of |HexDigits| > 0x10FFFF':
                    return (HexDigits_MV > 0x10FFFF)
                else:
                    assert 0, constraint.c

            elif 'MV of |Hex4Digits|' in constraint.c:
                assert prec_node.symbol == 'Hex4Digits'
                Hex4Digits_text = prec_node.text()
                # XXX Properly, we should invoke the MV SDO here.
                Hex4Digits_MV = int(Hex4Digits_text, 16)
                if constraint.c == 'the MV of |Hex4Digits| is in the inclusive range 0xD800 to 0xDBFF':
                    return (0xD800 <= Hex4Digits_MV <= 0xDBFF)
                elif constraint.c == 'the MV of |Hex4Digits| is in the inclusive range 0xDC00 to 0xDFFF':
                    return (0xDC00 <= Hex4Digits_MV <= 0xDFFF)
                elif constraint.c == 'the MV of |Hex4Digits| is not in the inclusive range 0xD800 to 0xDFFF':
                    return not (0xD800 <= Hex4Digits_MV <= 0xDFFF)
                else:
                    assert 0, constraint.c

            elif constraint.c == 'the CapturingGroupNumber of |DecimalEscape| is &le; _NcapturingParens_':
                # We don't know what _NcapturingParens_ is yet,
                # so we can't enforce this constraint yet.
                # Ignore it for now, enforce it later.
                return True

            else:
                assert 0, constraint.c

        elif type(constraint) == C_lookahead:
            if text_posn < len(lex_tip.source_text):
                next_char = lex_tip.source_text[text_posn]

                any_ts_matches_lookahead = False
                for ts in constraint.tss:
                    assert len(ts) == 1
                    [t] = ts
                    if lexical_Rsymbol_matches_char(t, next_char):
                        any_ts_matches_lookahead = True
                        break
            else:
                # We're at the end of the source_text,
                # so there isn't a lookahead character,
                # so no terminal-sequence can match.
                any_ts_matches_lookahead = False

            if constraint.matches:
                # The constraint requires that the lookahead match
                # any of the terminal-seqs in the LAC.
                return any_ts_matches_lookahead
            else:
                # The constraint requires that the lookahead not match
                # any of the terminal-seqs in the LAC.
                return not any_ts_matches_lookahead

        else:
            assert 0, constraint

    # XXX not invoked, but I'll need something like this...

    def lexical_node_satisfies_adhoc_checks(node):
        # B.1.2 "String Literals":
        #" This definition of EscapeSequence
        #  [whose second RHS is LegacyOctalEscapeSequence rather than `0` [lookahead <! DecimalDigit]]
        #" is not used in strict mode or when parsing TemplateCharacter.
        # XXX This only handles the "parsing TemplateCharacter" case.
        if node.symbol == 'TemplateCharacter' and uses_B12_definition_of_EscapeSequence(node):
            return False
        return True

    def uses_B12_definition_of_EscapeSequence(tc):
        assert tc.symbol == 'TemplateCharacter'
        if len(tc.children) == 2:
            es = tc.children[1]
            if es.symbol == 'EscapeSequence':
                if es.children[0].symbol == 'LegacyOctalEscapeSequence':
                    return True
        return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class ParseNode:

    def __init__(self, shape, extent, tip):

        # ----
        # tip:

        assert isinstance(tip, SyntacticTIP) or isinstance(tip, LexicalTIP)
        self.tip = tip

        self.whole_text = self.tip.source_text

        # ------
        # shape:

        if type(shape) in [T_lit, T_named, T_u_p, T_u_r]:
            # terminal
            self.symbol = shape
            self.production = None
            self.option_bits = None
            self.is_terminal = True

        elif type(shape) == tuple and len(shape) == 2:
            # nonterminal
            (self.production, self.option_bits) = shape
            self.symbol = self.production.og_lhs
            self.is_terminal = False

            assert isinstance(self.production, ExProd)
            assert isinstance(self.option_bits, str)
            assert all(
                bit in ['0','1']
                for bit in self.option_bits
            )

            assert type(self.symbol) == str
            self.puk = (self.symbol, self.production.og_rhs_reduced, self.option_bits)
            # "production use key"

        else:
            assert 0, shape

        # -------
        # extent:

        if type(extent) == list and len(extent) > 0:
            assert not self.is_terminal
            self.children    = extent
            self.start_posn  = self.children[0].start_posn
            self.end_posn    = self.children[-1].end_posn

            # if isinstance(self.tip, SyntacticTIP):
                # self.start_token_k = self.children[0].start_token_k
                # print(f"1839 stk = {self.start_token_k} for {self}")
                # self.end_token_k   = self.children[-1].end_token_k
                # assert 0 <= self.start_token_k <= self.end_token_k <= len(self.tip._tokens)

        elif type(extent) == tuple and len(extent) == 2:
            self.children = []

            (start, end) = extent

            if isinstance(self.tip, LexicalTIP):
                self.start_posn = start
                self.end_posn = end
            elif isinstance(self.tip, SyntacticTIP):
                # self.start_token_k = start
                # print(f"1851 stk = {self.start_token_k} for {self}")
                # self.end_token_k = end
                # assert 0 <= self.start_token_k <= self.end_token_k <= len(self.tip._tokens)

                # # XXX
                # # Problem: the ParseNode that we're in the process of creating
                # # hasn't been inserted into self.tip yet.

                # self.start_posn = self.tip._tokens[self.start_token_k].start_posn
                # self.end_posn   = self.tip._tokens[self.end_token_k-1].end_posn
                self.start_posn = start
                self.end_posn = end
            else:
                assert 0, self.tip

        else:
            assert 0, extent

        assert type(self.start_posn) == int
        assert type(self.end_posn) == int
        assert 0 <= self.start_posn <= self.end_posn <= len(self.whole_text)

        # --------------------------
        # Is this an instance of a chain production?
        # "A <dfn>chain production</dfn> is a production that has
        # exactly one nonterminal symbol on its right-hand side
        # along with zero or more terminal symbols."
        nt_children = []
        for child in self.children:
            if not child.is_terminal:
                if child.symbol.endswith('?'):
                    if child.children:
                        [nt_child] = child.children
                        nt_children.append(nt_child)
                else:
                    nt_children.append(child)
        if len(nt_children) == 1:
            self.is_instance_of_chain_prod = True
            [self.direct_chain] = nt_children
        else:
            self.is_instance_of_chain_prod = False

    # ------------------------------------------------------------------

    def __str__(self):
        return "<ParseNode symbol=%s, %d children>" % (self.symbol, len(self.children))

    def text(self):
        return self.whole_text[self.start_posn:self.end_posn]

    def dump(self, prefix='  ', f=sys.stdout):
        print_tree(self, prefix, f)

    def tree_slug(self):
        return (
              ('(omitted)' if self.symbol is None else str(self.symbol))
            + f' [{self.start_posn}:{self.end_posn}]'
            + (' ' + escape(self.text()) if self.children == [] else '')
        )

    def is_nonterminal(self):
        return not self.is_terminal

    def contains_a(self, symbol):
        return (
            self.symbol == symbol
            or
            any(child.contains_a(symbol) for child in self.children)
        )

    def unit_derives_a(self, symbol):
        if self.symbol == symbol:
            return self
        elif len(self.children) == 1:
            [child] = self.children
            return child.unit_derives_a(symbol)
        else:
            return None

    def each_ancestor(self):
        n = self.parent
        while n is not None:
            yield n
            n = n.parent

    def root(self):
        n = self
        while True:
            if n.parent is None:
                return n
            n = n.parent

    def preorder_traverse(self):
        yield self
        for child in self.children:
            yield from child.preorder_traverse()

def show_ambiguity(A_tree, B_tree, f):
    def put(*args): print(*args, file=f)

    if A_tree.symbol != B_tree.symbol:
        put(f"Posn {A_tree.start_posn} - {A_tree.end_posn}, text:")
        put(A_tree.text())
        put('-----')
        put(f"A symbol: {A_tree.symbol}")
        put(f"B symbol: {B_tree.symbol}")
        return

    if (
        hasattr(A_tree, 'production')
        and
        hasattr(B_tree, 'production')
        and
        A_tree.production != B_tree.production
    ):
        put(f"Posn {A_tree.start_posn} - {A_tree.end_posn}, text:")
        put(A_tree.text())
        put('-----')
        put(f"A production: {A_tree.production['lhs']} -> {stringify_rthing_sequence(A_tree.production['rhs'])}")
        put(f"B production: {B_tree.production['lhs']} -> {stringify_rthing_sequence(B_tree.production['rhs'])}")
        return

    assert len(A_tree.children) == len(B_tree.children)
    for (A_child, B_child) in zip(A_tree.children, B_tree.children):
        show_ambiguity(A_child, B_child, f)

def escape(s):
    def uify(mo):
        c = mo.group(0)
        assert len(c) == 1
        return 'U+%x' % ord(c[0])
    return re.sub(r'[^ -~]', uify, s)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def char_matches_any_of_the_symbols(char, rsymbols):
    assert len(char) == 1
    for rsymbol in rsymbols:
        # trace(rsymbol)
        if lexical_Rsymbol_matches_char(rsymbol, char):
            return True
    return False

def lexical_Rsymbol_matches_char(rsymbol, char):
    assert len(char) == 1

    T = rsymbol.T

    if rsymbol == ACCEPTANCE:
        return False

    elif T == 'T_lit':
        assert len(rsymbol.c) == 1
        return (rsymbol.c == char)

    elif T == 'T_named':
        n = rsymbol.n
        if n == 'USP':
            #" Any Unicode 'Space_Separator' code point
            return (
                unicodedata.category(char) == 'Zs'
            )
        else:
            return (char == character_named_[n])

    elif T == 'T_u_r':
        rlo = rsymbol.rlo
        rhi = rsymbol.rhi
        return (rlo <= ord(char) <= rhi)

    elif T == 'T_u_p':
        p = rsymbol.p
        Other_ID_Start = "\u1885\u1886\u309b\u309c\u2118\u212e"
        Other_ID_Continue = "\u1369\u136A\u136b\u136c\u136d\u136e\u136f\u1370\u1371\u19d1\u00b7\u0387"

        if p == 'ID_Start':
            # see http://unicode.org/reports/tr31/
            # "Unicode Identifier and Pattern Syntax"
            cat = unicodedata.category(char)
            return cat in ['Lu', 'Ll', 'Lt', 'Lm', 'Lo', 'Nl'] or char in Other_ID_Start
            # XXX - Pattern_Syntax - Pattern_White_Space

        elif p == 'ID_Continue':
            cat = unicodedata.category(char)
            return (
                cat in ['Lu', 'Ll', 'Lt', 'Lm', 'Lo', 'Nl',     'Mn', 'Mc', 'Nd', 'Pc']
                or char in Other_ID_Start
                # + Other_ID_Continue - Pattern_Syntax - Pattern_White_Space
                or char in Other_ID_Continue
                # XXX - Pattern_Syntax - Pattern_White_Space
            ) and char != '\u2e2f'

        else:
            assert 0, p

        # See http://www.unicode.org/Public/10.0.0/ucd/PropList.txt
        # Other_ID_Start:
        #     6 code points:
        #     Mn: 1885 1886
        #     Sk: 309B 309C
        #     Sm: 2118
        #     So: 212E
        #     cats: Mn Sk Sm So
        #
        # Other_ID_Continue:
        #     12 code points:
        #     No: 1369..1371 19D1
        #     Po: 00B7 0387
        #     cats: No Po
        #
        # Pattern_Syntax:
        #     2760 code points (in 0021 to FE46)
        #     cats: Cn Lm Pd Pe Pf Pi Po Ps Sc Sk Sm So
        #     I think the only effect of "- Pattern_Syntax" is
        #     to exclude U+2E2F VERTICAL TILDE (category Lm).
        #
        # Pattern_White_Space:
        #     11 code points (in 0009 to 2029)
        #     cats: Cc Cf Zl Zp Zs
        #     so "- Pattern_White_Space" has no effect in this version.

    elif T == 'NT':
        assert rsymbol.n in char_set_, rsymbol.n
        return (char in char_set_[rsymbol.n])

    else:
        assert 0, rsymbol

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

if __name__ == '__main__':
    # test

    script_text = '`\\07`'

    tree = parse(script_text, 'Script', trace_level=9, trace_f=open('/home/michael/tmp/trace.new', 'w'))
    print()
    print('=================')
    print()
    tree.dump()
    print('----------')

# vim: sw=4 ts=4 expandtab
