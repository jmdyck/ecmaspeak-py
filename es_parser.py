#!/usr/bin/python3

# ecmaspeak-py/es_parser.py:
# Parse ECMAScript code using an Earley-like approach.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>


import json, pdb, unicodedata, sys, re
from collections import defaultdict
from pprint import pprint # mainly for debugging
import misc

from emu_grammar_tokens import *

character_named_ = {
    # table-31:
    'ZWNJ'  : '\u200c',
    'ZWJ'   : '\u200d',
    'ZWNBSP': '\ufeff',

    # table-32:
    'TAB'   : '\u0009',
    'VT'    : '\u000b',
    'FF'    : '\u000c',
    'SP'    : '\u0020',
    'NBSP'  : '\u00a0',
    # 'ZWNBSP': '\ufeff', # appears above
    # 'USP' : isn't a single character

    # table-33:
    'LF'    : '\u000a',
    'CR'    : '\u000d',
    'LS'    : '\u2028',
    'PS'    : '\u2029',
}

Rush = mynamedtuple('Rush', 'pre rsymbol post')

class ParseError(Exception):
    def __init__(self, posn, item_strings):
        self.posn = posn
        self.kernel_item_strings = item_strings

def my_object_hook(d):
    if 'T' in d:
        T = d['T']
        del d['T']

        if False: assert 0
        elif T == 'Arg'          : return Arg(**d)
        elif T == 'GNT'          : return GNT(**d)
        elif T == 'T_lit'        : return T_lit(**d)
        elif T == 'T_nc'         : return T_nc(**d)
        elif T == 'T_named'      : return T_named(**d)
        elif T == 'T_u_p'        : return T_u_p(**d)
        elif T == 'A_but_not'    : return A_but_not(**d)
        elif T == 'A_but_only_if': return A_but_only_if(**d)
        elif T == 'A_no_LT'      : return A_no_LT(**d)
        elif T == 'LAX'          : return LAX(**d)
        elif T == 'LAI'          : return LAI(**d)
        else: assert 0, T

    elif 'pre' in d and 'post' in d and 'rsymbol' in d:
        return Rush(**d)

    else:
        return d

T_EOI = mynamedtuple('T_EOI', 'n')

def are_distinct(values):
    return len(set(values)) == len(values)

class _Earley:

    def __init__(this_parser, name, how_much_to_consume):

        assert how_much_to_consume in ['all', 'as much as possible']

        this_parser.name = name
        this_parser.how_much_to_consume = how_much_to_consume

        this_parser.trace_prefix = '| ' if this_parser.name == 'lexical' else ''

        filename = '../ecma262/_editorial/%sB_cfps.json' % this_parser.name
        cfps_from_file = json.load(open(filename, 'r'), object_hook=my_object_hook)
        #
        ns = [ prod['n'] for prod in cfps_from_file ]
        assert misc.are_distinct(ns)
        assert 0 not in ns # so we can use it for start_production

        this_parser.start_symname = '*START*' # S' of the augmented grammar
        this_parser.finished_goal_symbol = '!end of goal!'
        this_parser.end_of_input_rsymbol = T_EOI(n=this_parser.finished_goal_symbol)
        this_parser.end_of_input_rush = Rush(rsymbol=this_parser.end_of_input_rsymbol, pre=None, post=None)
        # or should each _Earley have a distinct EOI symbol?

        start_production = {
            'n': 0,
            'lhs': this_parser.start_symname,
            'params': [],
            'guard': None,
            'rhs': [
                # For any particular parsing task,
                # we will replace the following Rush with one for the goal_rsymbol:
                Rush( rsymbol = None, pre = None, post = None),
                this_parser.end_of_input_rush
            ]
        }

        this_parser.cfps = [start_production] + cfps_from_file

        n_points = 0
        for prod in this_parser.cfps:
            n_points += 1 + len(prod['rhs'])

        this_parser.productions_with_lhs_ = defaultdict(list)
        for prod in this_parser.cfps:
            this_parser.productions_with_lhs_[prod['lhs']].append(prod)

    # -------------------------------------------------

    def run(
        this_parser,
        start_text_posn,
        goal_symname,
        get_next_terminal_instances,
        make_nonterminal_node,
        make_Node_here,
        node_matches_rush,
        trace_level,
        trace_f
    ):
        # Either returns a single Node, or raises a ParseError.

        def trace(trace_level_of_this_msg, *args):
            if trace_level_of_this_msg <= trace_level:
                print(this_parser.trace_prefix, *args, file=trace_f)

        def Rsymbol_get_rhs_start_points(rsymbol, psettings):
            assert Rsymbol_is_nonterminal(rsymbol)
            return [
                (prod['n'], 0)
                for prod in this_parser.productions_with_lhs_[rsymbol.n]
                if guard_is_satisfied(prod['guard'], psettings)
            ]

        def guard_is_satisfied(guard, psettings):
            if guard is None: return True
            s = guard['s']
            assert s in ['+', '~']
            n = guard['n']
            assert n in psettings
            assert psettings[n] in ['+', '~']
            return s == psettings[n]

        # -------------------------------------------
        # Roughly speaking, a 'Point' is a point in the grammar.
        # i.e., a point in the RHS of some production.
        # (Elsewhere called an LR(0) item,
        # but I'm using "Item" for a slightly bigger concept.)
        #
        # 'Point' should logically be a nested class,
        # except that its methods wouldn't get access to this_parser.cfps.
        # (Unless you pass down a reference to it,
        # and every Item saves it as an instance variable,
        # but that seems excessive.)

        def Point_make(prod_num, dot_posn):
            return (prod_num, dot_posn)

        def Point_stringify(point):
            (prod_num, dot_posn) = point
            prod = this_parser.cfps[prod_num] # XXX
            lhs = prod['lhs']
            params = prod.get('params', []) # XXX
            rhs = prod['rhs']
            # dot = '\u25CF'
            dot = '@'
            return "%s%s -> %s %s %s " % (
                lhs,
                ('' if params == [] else '[' + ','.join(params) + ']'),
                ' '.join(Rush_stringify(r) for r in rhs[0:dot_posn]),
                dot,
                ' '.join(Rush_stringify(r) for r in rhs[dot_posn:])
            )

        def Point_get_rush_after_dot(point):
            (prod_num, dot_posn) = point
            prod = this_parser.cfps[prod_num]
            rhs = prod['rhs']
            if dot_posn < len(rhs):
                return rhs[dot_posn]
            elif dot_posn == len(rhs):
                return None
            else:
                assert 0

        def Point_advance(point, node):
            # Get the next point after `point`,
            # where `node` is (about to be) an instance of the intervening rush.

            # Normally, this would be really simple.
            # But it's also the occasion to do any extra checks on `node`.
            # If `node` fails those checks, return None.

            (prod_num, dot_posn) = point

            # pdb.set_trace()

            prod = this_parser.cfps[prod_num]
            assert dot_posn < len(prod['rhs'])
            # We'd never be asked to advance from the last point in a production.

            rush = prod['rhs'][dot_posn]

            # Does `node` qualify as an instance of `rush`?
            if node_matches_rush(node, rush):
                return Point_make(prod_num, dot_posn+1)
            else:
                return None

        def Point_get_prod(point):
            (prod_num, dot_posn) = point
            prod = this_parser.cfps[prod_num]
            return prod

        def Point_get_lhs_symbol(point, psettings):
            (prod_num, _) = point
            prod = this_parser.cfps[prod_num]
            lhs_symname = prod['lhs']
            params_suffix = ''.join(
                psettings[param_name] + param_name
                for param_name in prod['params']
            )
            return lhs_symname + params_suffix
            # return { 'T': 'GNT', 'n': lhs_symname, 'a': [], 'o': False } # XXX different for params

        # -------------------------------------------

        def Item_make(cause, transit_node, psettings, resulting_point):
            return (cause, transit_node, psettings, resulting_point)

        def Item_stringify(item):
            (_, _, psettings, point) = item
            return "_ _ {%s} %s" % (
                ', '.join(setting+name for (name, setting) in sorted(psettings.items())),
                Point_stringify(point)
            )

        def Item_get_rush_after_dot(item):
            (_, _, _, point) = item
            return Point_get_rush_after_dot(point)

        def Item_advance(item, node):
            (_, _, psettings, point) = item
            new_point = Point_advance(point, node)
            if new_point is None: return None
            return Item_make(item, node, psettings, new_point)

        def Item_get_symbol_after_dot(item):
            (_, _, psettings, point) = item

            rush = Point_get_rush_after_dot(point)
            if rush is None:
                return '!end of rhs!'
            else:
                return Rsymbol_exify(rush.rsymbol, psettings)

        def Item_get_derived_items(item, this_set):
            (_, _, psettings, point) = item

            rush = Point_get_rush_after_dot(point)
            if rush is None:
                # There is no runit/rsymbol after the dot.
                # I.e., the dot is at the end of the RHS.
                #?? Don't perform "Completer" yet.
                # for new_item in Item_reduce(item): yield new_item
                pass

            elif Rush_is_nonterminal(rush):
                # Perform "Predictor":
                rsymbol = rush.rsymbol

                # if rush.pre: print("290 rush w pre:", Rush_stringify(rush))

                new_psettings = dict(
                    Rsymbol_expand_args(rsymbol, psettings)
                )

                for point in Rsymbol_get_rhs_start_points(rsymbol, new_psettings):
                    yield Item_make(this_set, None, new_psettings, point)

                if rsymbol.o:
                    # make_terminal_node
                    empty_node = make_Node_here(None, set_text_posn)
                    # pdb.set_trace()
                    new_item = Item_advance(item, empty_node)
                    if new_item is not None: yield new_item

            elif Rush_is_terminal(rush):
                # Don't perform "Scanner" yet.
                pass

            else:
                assert 0, rush

        def Item_reduce(item):
            trace(9, '    Item_reduce:', Item_stringify(item))
            (_, _, psettings, point) = item

            if 0:
                lhs_symbol = Point_get_lhs_symbol(point, psettings)
                trace(1, "reducing to %s ..." % lhs_symbol)
                parent_node = make_Node_here(lhs_symbol, set_text_posn)
            else:
                prod = Point_get_prod(point)
                parent_node = make_nonterminal_node(prod, psettings, set_text_posn)
                lhs_symbol = prod['lhs'] + ''.join(
                    psettings[param_name] + param_name
                    for param_name in prod['params']
                )

            if lhs_symbol.startswith('Cover') or lhs_symbol.startswith('LeftHandSideExpression'):
                print(f'MAY NEED TO REPARSE {lhs_symbol}', file=trace_f)

            p_item = item
            while True:
                (cause, transit_node, _, point) = p_item # XXX
                if transit_node is None:
                    back_set = cause
                    break
                parent_node.push_child(transit_node)
                p_item = cause

            # if not node_is_valid(parent_node): return

            back_items = Set_get_items_expecting_symbol(back_set, lhs_symbol)
            if len(back_items) == 0:
                trace(1, )
                trace(1, "no items expecting '%s' in back_set:" % lhs_symbol)
                Set_trace(1, back_set)
                assert 0 # because item must have come from somewhere

            for back_item in back_items:
                new_item = Item_advance(back_item, parent_node)
                if new_item is None:
                    trace(1, "    Item_advance(...) returned None")
                else:
                    yield new_item

        # -------------------------------------------
        # (Similarly.)

        class EarleySet:
            def __init__(this_set, text_posn):
                trace(9, )
                trace(9, f'new set at posn {text_posn}...')
                this_set.items_with_dot_before_ = defaultdict(list)

        def Set_trace(tl, this_set):
            trace(tl, )
            trace(tl, "EarleySet:")
            for (x, items) in sorted(this_set.items_with_dot_before_.items()):
                trace(tl, '  %s:' % x)
                for item in items:
                    trace(tl, '    ', Item_stringify(item))

        def Set_close(this_set, kernel_items):
            for item in kernel_items:
                Set_add_and_recurse(this_set, item, '')

            # Now that we've gone as far as we can with "Predictor",
            # run "Completer"...

            if '!end of rhs!' in this_set.items_with_dot_before_:
                for item in this_set.items_with_dot_before_['!end of rhs!']:
                    for new_item in Item_reduce(item):
                        Set_add_and_recurse(this_set, new_item, '')


        def Set_add_and_recurse(this_set, item, indent):
            symbol = Item_get_symbol_after_dot(item)

            if item in this_set.items_with_dot_before_[symbol]:
                # already there, don't have to do anything
                return

            trace(9, "  ADDING %s" % indent + Item_stringify(item))
            this_set.items_with_dot_before_[symbol].append(item)

            for new_item in Item_get_derived_items(item, this_set):
                Set_add_and_recurse(this_set, new_item, indent+' ')

        def Set_get_expected_terminals(this_set):
            result = []
            # XXX optimize
            for (symbol, items) in sorted(this_set.items_with_dot_before_.items()):
                # if Symbol_is_terminal(symbol):
                for item in items:
                    rush = Item_get_rush_after_dot(item)
                    if rush is not None and Rush_is_terminal(rush) and rush not in result:
                        result.append(rush)
            return result

        def Set_get_items_expecting_rush(this_set, rush):
            psettings = {} # XXX
            if rush is None:
                symbol = '!end of rhs!'
            else:
                symbol = Rsymbol_exify(rush.rsymbol, psettings)
            items = Set_get_items_expecting_symbol(this_set, symbol)
            return [
                item
                for item in items
                if Item_get_rush_after_dot(item) == rush
            ]

        def Set_get_items_expecting_symbol(this_set, symbol):
            items = this_set.items_with_dot_before_[symbol]
            assert len(items) > 0 or symbol == this_parser.finished_goal_symbol
            return items

        # -------------------------------------------

        def cannot_continue(text_posn):
            if this_parser.how_much_to_consume == 'as much as possible':
                #" When a stream of code points is to be parsed
                #" as an ECMAScript |Script| or |Module|,
                #" it is first converted to a stream of input elements
                #" by repeated application of the lexical grammar; ...
                #
                #" The source text is scanned from left to right,
                #" repeatedly taking the longest possible sequence of code points
                #" as the next input element.
                trace(2, 'Checking for prior acceptables...')

                if latest_accepting_item is None:
                    trace(2, 'nope, none')
                    pass # fall through to ParseError

                else:
                    (_, goal_node, _, _) = latest_accepting_item
                    assert goal_node.symbol == goal_symname
                    if trace_level >= 2:
                        trace(2, 'returning prior acceptable:')
                        goal_node.dump(this_parser.trace_prefix + '   ', f=trace_f)
                    return goal_node

            else:
                #" ... this stream of input elements is then parsed
                #" by a single application of the syntactic grammar.
                #" The input stream is syntactically in error
                #" if the tokens in the stream of input elements
                #" cannot be parsed as a single instance of the goal nonterminal
                #" (|Script| or |Module|), with no tokens left over.
                pass # fall through to ParseError

            item_strings = [
                Item_stringify(item)
                for item in next_kernel_items
            ]
            raise ParseError(text_posn, item_strings)

        # -------------------------------------------

        trace(1, )
        trace(1, f"{this_parser.name}.run invoked at posn {start_text_posn} with goal '{goal_symname}'")

        # Tweak the start production 
        goal_rsymbol = GNT(n=goal_symname, a=[], o=False)
        goal_rush = Rush(rsymbol=goal_rsymbol, pre=None, post=None)
        this_parser.cfps[0]['rhs'][0] = goal_rush
        # And make an item for it:
        initial_item = Item_make(None, None, {}, Point_make(0,0))
        next_kernel_items = [initial_item]

        if this_parser.how_much_to_consume == 'as much as possible':
            latest_accepting_item = None

        set_text_posn = start_text_posn
        while True:
            eset = EarleySet(set_text_posn)

            Set_close(eset, next_kernel_items)

            if trace_level >= 3:
                Set_trace(3, eset)

            # -----------------

            expected_terminal_rushes = Set_get_expected_terminals(eset)

            if len(expected_terminal_rushes) == 0:
                trace(2, "No expected terminals! (e.g., due to application of a 'but not')")
                return cannot_continue(set_text_posn)

            if trace_level >= 9:
                trace(9, )
                trace(9, 'expected_terminal_rushes:')
                strings = [ Rush_stringify(rush) for rush in expected_terminal_rushes ]
                for st in sorted(strings):
                    trace(9, '  ', st)

            if this_parser.how_much_to_consume == 'as much as possible':
                accepting_items_here = Set_get_items_expecting_symbol(eset, this_parser.finished_goal_symbol)
                if accepting_items_here:
                    trace(9, )
                    trace(9, '(there are accepting_items_here)')
                    if len(accepting_items_here) > 1:
                        trace(2, "%d items!" % len(accepting_items_here))
                        if trace_level >= 2:
                            for item in accepting_items_here:
                                (_, node, _, _) = item
                                trace(2, '')
                                node.dump(this_parser.trace_prefix + '   ', f=trace_f)
                        print('NEED TO RESOLVE AMBIGUITY', file=trace_f) # XXX

                    latest_accepting_item = accepting_items_here[0]

            # -----------------

            result = get_next_terminal_instances(set_text_posn, expected_terminal_rushes)

            trace(2, )
            trace(2, f"(back in {this_parser.name}.run after return from get_next_terminal_instances...)")

            if result is None:
                # At this point in the source text,
                # none of the expected terminals was seen.
                trace(3, "gnti returned no terminal instances!")
                return cannot_continue(set_text_posn)

            # -----------------

            (rats, next_text_posn) = result
            # "rats" = rushes and terminal-instances

            if trace_level >= 3:
                trace(3, )
                trace(3, f'gtni returned {len(rats)} matches:')
                for (rush, termin) in rats:
                    trace(3, "  For the expected terminal rush:")
                    trace(3, "    " + Rush_stringify(rush))
                    trace(3, "  we have the terminal instance:")
                    termin.dump(this_parser.trace_prefix + '     ', f=trace_f)
                    trace(3, )
                trace(3, f'and next_text_posn = {next_text_posn}')

            assert set_text_posn <= next_text_posn
            # It would be strictly less-than, except for inserted semicolons.

            # -------------------------------------

            # print('...', file=sys.stderr)
            next_kernel_items = []
            for (rush, termin) in rats:
                for item in Set_get_items_expecting_rush(eset, rush):
                    # print(rush, file=sys.stderr)
                    # if trace_level >= 9 and rush.rsymbol == T_lit(';'): pdb.set_trace()
                    new_item = Item_advance(item, termin)
                    # print(new_item, file=sys.stderr)
                    if new_item is None:
                        print('got None when attempting to advance', item, termin)
                        assert 0
                    else:
                        next_kernel_items.append(new_item)

            if trace_level >= 9:
                trace(9, )
                trace(9, 'next_kernel_items:')
                for item in next_kernel_items:
                    trace(9, '  ', Item_stringify(item))
                if len(next_kernel_items) == 0:
                    trace(9, '  ', 'None!')

            assert len(next_kernel_items) > 0

            # -------------------------------------

            if len(rats) == 1 and rats[0][1].symbol == this_parser.end_of_input_rsymbol: # this_parser.finished_goal_symbol:
                trace(1, 'success!')
                trace(1, "results:")
                valid_trees = []
                for end_item in next_kernel_items:
                    (prev_item, n0, _, _) = end_item
                    assert n0.symbol == this_parser.end_of_input_rsymbol # this_parser.finished_goal_symbol
                    (_, goal_node, _, _) = prev_item
                    assert goal_node.symbol == goal_symname
                    trace(1, "  ", goal_node)
                    valid_trees.append(goal_node)

                n_valids = len(valid_trees)
                if n_valids == 0:
                    assert 0
                elif n_valids == 1:
                    [result] = valid_trees
                else:
                    # assert 0
                    print(f'NEED TO SELECT FROM {n_valids} RESULT TREES', file=trace_f) # XXX
                    result = valid_trees[0]
                return result

            set_text_posn = next_text_posn

        assert 0 # unreachable

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

#    def _gather_character_sets(cfps):
#
#        prods_for_lhs_ = defaultdict(list)
#        for prod in cfps:
#            prods_for_lhs_[prod['lhs']].append(prod)
#
#        something_ = {}
#
#        def recurse(lhs):
#            if lhs in something_:
#                return something_[lhs]
#
#            prods = prods_for_lhs_[lhs]
#            assert prods
#
#            charset_so_far = set()
#            for prod in prods:
#                if prod['guard']: print(lhs, prod)
#
#                rhs = prod['rhs']
#                if len(rhs) != 1:
#                    charset_so_far = None
#                    break
#                    # print(' '.join(Rush_stringify(rush) for rush in rhs))
#
#                [rush] = rhs
#
#                if rush.rsymbol.T == 'T_lit':
#                    assert len(rush.rsymbol.c) == 1
#                    charset_so_far.add(rush.rsymbol.c)
#
#                elif rush.rsymbol.T == 'T_nc':
#                    if rush.rsymbol.n == 'USP':
#                        pass # XXX
#                    else:
#                        charset_so_far.add(character_named_[rush.rsymbol.n])
#
#                elif rush.rsymbol.T == 'T_u_p':
#                    # XXX
#                    charset_so_far.add({
#                        None:             'a',
#                        'ID_Start':       'b',
#                        'ID_Continue':    'c',
#                    }[rush.rsymbol.p])
#
#                elif rush.rsymbol.T == 'GNT':
#                    if rush.rsymbol.o:
#                        charset_so_far = None
#                        break
#                    r = recurse(rush.rsymbol.n)
#                    if r is None:
#                        charset_so_far = None
#                        break
#                    charset_so_far.update(r)
#                    # print(Rush_stringify(rush))
#                    # ignore rush.rsymbol.a?
#
#                else:
#                    assert 0, rush.rsymbol.T
#
#                assert rush.pre is None
#                if rush.post is None or rush.post.T == 'LAX':
#                    pass
#                elif rush.post.T == 'A_but_not':
#                    # XXX: remove chars from charset
#                    pass
#                else:
#                    assert 0, rush.post
#
#            # assert charset_so_far is not None
#            if charset_so_far:
#                # print('is charset:', lhs)
#                something_[lhs] = charset_so_far
#            return charset_so_far
#
#        for (lhs,prods) in sorted(prods_for_lhs_.items()):
#            if lhs == '*START*': continue
#            recurse(lhs)

def gather_char_sets(cfps):
    global char_set_

    def recurse(name):
        result = set()
        for prod in cfps:
            if prod['lhs'] == name:
                assert prod['params'] == []
                assert prod['guard'] is None
                assert len(prod['rhs']) == 1
                [rush] = prod['rhs']
                assert rush.pre is None
                assert rush.post is None
                rsymbol = rush.rsymbol
                if rsymbol.T == 'T_lit':
                    result.add( rsymbol.c )
                elif rsymbol.T == 'T_nc':
                    result.add( character_named_[rsymbol.n] )
                elif rsymbol.T == 'GNT':
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
        # SyntaxCharacter
        # UnicodeIDContinue
    ]:
        char_set_[n] = recurse(n)
        # print("char set '%s' = %s" % (n, char_set_[n]))

# ------------------------------------------------------------------------------

def gather_ReservedWords(cfps):
    # kludgy, but anything non-kludgy would be over-engineered
    global ReservedWords
    ReservedWords = set()

    def recurse(name):
        for prod in cfps:
            if prod['lhs'] == name:
                assert prod['params'] == []
                assert prod['guard'] is None
                assert len(prod['rhs']) == 1
                [rush] = prod['rhs']
                assert rush.pre is None
                assert rush.post is None
                rsym = rush.rsymbol
                t = rsym.T
                if t == 'GNT':
                    assert rsym.a == []
                    assert rsym.o == False
                    recurse(rsym.n)
                elif t == 'T_lit':
                    ReservedWords.add(rsym.c)

    recurse('ReservedWord')
    # print('ReservedWords:', sorted(ReservedWords))

# ------------------------------------------------------------------------------

A_ASI_rule_1c = mynamedtuple('A_ASI_rule_1c', '')
A_ASI_override = mynamedtuple('A_ASI_override', '')

def do_ASI_prep(cfps):

    ASI_rule_1c_count = 0
    def prep_ASI_rule_1c(prod):

        #" ...
        #"  - The previous token is ) and the inserted semicolon
        #"    would then be parsed as the terminating semicolon
        #"    of a do-while statement (13.7.2).

        if prod['lhs'] != 'IterationStatement': return
        rhs = prod['rhs']

        rush0 = rhs[0]
        rsymbol0 = rush0.rsymbol
        if not( rsymbol0.T == 'T_lit' and rsymbol0.c == 'do'): return

        rush2 = rhs[2]
        rsymbol2 = rush2.rsymbol
        assert rsymbol2.T == 'T_lit' and rsymbol2.c == 'while'

        rush5 = rhs[5]
        rsymbol5 = rush5.rsymbol
        assert rsymbol5.T == 'T_lit' and rsymbol5.c == ')'

        rush6 = rhs[6]
        rsymbol6 = rush6.rsymbol
        assert rsymbol6.T == 'T_lit' and rsymbol6.c == ';'
        assert rush6.pre is None
        assert rush6.post is None

        rhs[6] = Rush(rsymbol=rsymbol6, pre=A_ASI_rule_1c(), post=None)

        nonlocal ASI_rule_1c_count
        ASI_rule_1c_count += 1
        
    #" 11.9.1 Rules of Automatic Semicolon Insertion
    #" However, there is an additional overriding condition on the preceding rules:
    #" a semicolon is never inserted automatically
    #" if the semicolon would then be parsed as an empty statement
    #" or if that semicolon would become one of the two semicolons
    #" in the header of a for statement (see 13.7.4).

    ASI_override_1_count = 0
    def prep_ASI_override_1(prod):
        if prod['lhs'] != 'EmptyStatement': return 0
        rhs = prod['rhs']

        rush0 = rhs[0]
        rsymbol0 = rush0.rsymbol
        assert rsymbol0.T == 'T_lit' and rsymbol0.c == ';'
        assert rush0.pre is None
        assert rush0.post is None

        rhs[0] = Rush(rsymbol=rsymbol0, pre=A_ASI_override(), post=None)

        nonlocal ASI_override_1_count
        ASI_override_1_count += 1

    ASI_override_2_count = 0
    def prep_ASI_override_2(prod):
        if prod['lhs'] != 'IterationStatement': return 0
        rhs = prod['rhs']

        rush0 = rhs[0]
        rsymbol0 = rush0.rsymbol
        if not( rsymbol0.T == 'T_lit' and rsymbol0.c == 'for'): return 0

        for (r, rush) in enumerate(rhs):
            rsymbol = rush.rsymbol
            if rsymbol.T == 'T_lit' and rsymbol.c == ';':
                assert rush.pre is None
                assert rush.post is None
                rhs[r] = Rush(rsymbol=rsymbol, pre=A_ASI_override(), post=None)
                nonlocal ASI_override_2_count
                ASI_override_2_count += 1

    for prod in cfps:
        prep_ASI_rule_1c(prod)
        prep_ASI_override_1(prod)
        prep_ASI_override_2(prod)

    assert ASI_rule_1c_count == 1
    assert ASI_override_1_count == 1
    assert ASI_override_2_count == 5
    # XXX should be 6, but one is hidden inside LexicalDeclaration.
    # test case: for ( let i = 0 i < 10; i++ ) foo(i);
    # ASI is not allowed to insert the missing semicolon,
    # but my code will currently do so.
    #
    # And I can't just mark the semicolon in LexicalDeclaration as an ASI_override,
    # because that would affect every occurrence of LexicalDeclaration,
    # which would not be correct.
    # (i.e., ASI *is* allowed to insert the semicolon that ends a LexicalDeclaration
    # if it's not the child of a for-loop.)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

lexical = _Earley('lexical', 'as much as possible')
syntactic = _Earley('syntactic', 'all')

# _gather_character_sets(lexical.cfps)
gather_char_sets(lexical.cfps)

gather_ReservedWords(syntactic.cfps) # for "but not ReservedWord"
do_ASI_prep(syntactic.cfps)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse(source_text, goal_symname, trace_level=0, trace_f=sys.stdout):
    # Using the `lexical` and `syntactic` Parsers
    # created at the global level of this module,
    # attempt to parse the given `source_text`,
    # using `goal_symname` as the goal symbol.
    #
    # Return a single node or raise an Error.

    temp_posn_of_latest_asi = -1
    lexical_trace_level = trace_level

    def put(*args, **kwargs):
        print(*args, **kwargs, file=trace_f)

    def parse_main():
        # First, consume any non-tokens at the start:
        text_posn = find_any_following_non_tokens(0) # can create Node
        # Then go from there:
        node = syntactic.run(
            text_posn,
            goal_symname,
            _syntactic_get_next_terminal_instances, # can create Node
            _make_nonterminal_node,                 # can create Node
            _syntactic_make_Node_here,              # can create Node
            _syntactic_node_matches_rush,
            trace_level,
            trace_f
        )
        return node

    # --------------------------------------------------------------------------

    class InputElementStream:
        def __init__(self):
            self.input_elements = []
            self.is_done = False

        def position(self):
            N = len(self.input_elements)
            assert N % 2 == 1
            return N

        def appendToken(self, token):
            assert isinstance(token, Node)
            assert token.symbol.startswith('_Token')
            assert not self.is_done
            N = len(self.input_elements) 
            assert N % 2 == 1

            token.ies_start = N
            token.ies_end = N+1
            if N >= 3:
                assert self.input_elements[N-2].end_posn <= token.start_posn
            self.input_elements.append(token)

        def appendNonTokens(self, non_tokens):
            assert isinstance(non_tokens, list)
            for non_token in non_tokens:
                assert non_token.symbol == '_NonToken'
            assert not self.is_done
            N = len(self.input_elements) 
            assert N % 2 == 0
            self.input_elements.append(non_tokens)
            # 'append' rather than 'extend', mainly so that we can easily grab 
            # the span of non-tokens immediately preceding/following a token.

        def backtrack(self):
            # pop off the latest token and any following non-tokens
            assert not self.is_done
            N = len(self.input_elements)
            assert N % 2 == 1
            self.input_elements.pop(-1)
            self.input_elements.pop(-1)

        def end(self):
            self.is_done = True

        def a_LineTerminator_occurs_before_current_token(self):
            N = len(self.input_elements)
            assert N % 2 == 1
            return self._a_LineTerminator_occurs_in(N-3)

        def a_LineTerminator_occurs_after_current_token(self):
            N = len(self.input_elements)
            assert N % 2 == 1
            return self._a_LineTerminator_occurs_in(N-1)

        def _a_LineTerminator_occurs_in(self, i):
            non_tokens = self.input_elements[i]
            assert isinstance(non_tokens, list)
            for non_token in non_tokens:
                assert non_token.symbol == '_NonToken'
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

        def matches_syntactic_lookahead_sequence(self, n, las):
            assert n % 2 == 1
            # put("checking lookahead sequence:", las)
            for (i, lookahead_unit) in enumerate(las):
                if n+i < len(self.input_elements):
                    ie = self.input_elements[n + i]

                    if i % 2 == 0:
                        token = ie
                        assert token.symbol.startswith('_Token')
                        if token.text() != lookahead_unit:
                            # put(f"    mismatch: '{token.text()}' != '{lookahead_unit}'")
                            return False
                    else:
                        non_tokens = ie
                        assert isinstance(non_tokens, list)
                        if lookahead_unit == '*':
                            pass
                        elif lookahead_unit == 'nLTh':
                            if self._a_LineTerminator_occurs_in(n+i):
                                # put(f"    mismatch: LineTerminator != nLTh")
                                return False
                        else:
                            assert 0
                else:
                    # input_elements isn't long enough.
                    # i.e., the lookahead-restriction 'reaches' past the symbol it immediately precedes.
                    if self.is_done:
                        # input_elements won't get any longer than it is,
                        # so the lookahead sequence fails to match.
                        return False
                    else:
                        # input_elements might get longer,
                        # allowing us to say whether the lookahead sequence matches or not.
                        # For now, say it doesn't match, and check it later.
                        if 0:
                            put("When checking lookahead sequence:", las)
                            put("against:")
                            for (i, ie) in enumerate(self.input_elements):
                                put(' @ ' if i == n else ' ', end='')
                                if isinstance(ie, list):
                                    put('_', end='')
                                else:
                                    put(ie.text(), end='')
                            if n == len(self.input_elements):
                                put(' @')
                            else:
                                put()
                            put(f"input element stream isn't long enough, NEED TO CHECK later")
                        return False

            # put("    matched!")
            return True

    ies = InputElementStream()

    # --------------------------------------------------------------------------

    def _syntactic_get_next_terminal_instances(text_posn, expected_terminal_rushes):

        def maybe_insert_a_semicolon(rule_num):

            nonlocal temp_posn_of_latest_asi
            if text_posn == temp_posn_of_latest_asi:
                if trace_level >= 2:
                    put("+ but we've already inserted one here.")
                    put("+ Aborting to avoid infinite ASI loop.")
                return None
            temp_posn_of_latest_asi = text_posn

            semicolon_rushes = [
                rush
                for rush in expected_terminal_rushes
                if rush.rsymbol.T == 'T_lit' and rush.rsymbol.c == ';'
            ]
            if trace_level >= 2:
                put("+ semicolon_rushes:")
                for rush in semicolon_rushes:
                    put("+     %s" % Rush_stringify(rush))
                if len(semicolon_rushes) == 0:
                    put("+     (none)")

            if len(semicolon_rushes) == 0:
                # e.g. 036f6b8da7e53ee5.js: `({get `
                #  or  0ff3826356c94f67.js: `({function} = 0)`
                if trace_level >= 2:
                    put("+ but a semicolon isn't expected here, so giving up.")
                return None

            assert len(semicolon_rushes) == 1
            [semicolon_rush] = semicolon_rushes

            #" 11.9.1 Rules of Automatic Semicolon Insertion
            #" However, there is an additional overriding condition on the preceding rules:
            #" a semicolon is never inserted automatically
            #" if the semicolon would then be parsed as an empty statement
            #" or if that semicolon would become one of the two semicolons
            #" in the header of a for statement (see 13.7.4).
            if semicolon_rush.pre and semicolon_rush.pre.T == 'A_ASI_override':
                if trace_level >= 2:
                    put("+ but we're not allowed to insert a semicolon here, so giving up.")
                return None

            if rule_num == 1:
                # insert *before* the offending token.
                ies.backtrack()
            elif rule_num == 2:
                pass
            else:
                assert 0

            # make_terminal_node
            node = _syntactic_make_Node_here(T_lit(c=';'), text_posn) # can create Node
            return ([(semicolon_rush, node)], text_posn) # NOT next_text_posn

        # -------------------------------

        if trace_level >= 2:
            put()
            put(f'+ _syntactic_get_next_terminal_instances called at posn {text_posn}')
            put('+')
            put(misc.display_position_in_text(source_text, text_posn, indent='+ '), end='')

        # ------------------------------

        if text_posn == len(source_text):
            if trace_level >= 2:
                put('+')
                put('+ We are at the end of the input')

            ies.end()

            eoi_rushes = [
                rush
                for rush in expected_terminal_rushes
                if rush.rsymbol.T == 'T_EOI'
            ]
            if eoi_rushes:
                if trace_level >= 2: put('+ and EOI is one of the expected terminals')
                assert len(eoi_rushes) == 1
                [rush] = eoi_rushes
                # make_terminal_node
                node = _syntactic_make_Node_here(syntactic.end_of_input_rsymbol, text_posn) # can create Node
                return ([(rush, node)], text_posn)
            else:
                if trace_level >= 2: put('+ but EOI is not expected here')
                # ASI rule #2:
                #" When, as the source text is parsed from left to right,
                #" the end of the input stream of tokens is encountered
                #" and the parser is unable to parse the input token stream
                #" as a single instance of the goal nonterminal,
                #" then a semicolon is automatically inserted
                #" at the end of the input stream. 
                if trace_level >= 2: put('+ so ASI rule #2 says to insert a semicolon')
                return maybe_insert_a_semicolon(2) # can create Node

        # ------------------------------

        # When the syntactic parser wants its next terminal (token),
        # it runs the lexical parser to find an input element.

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
        #" In all other contexts, |InputElementDiv| is used as the lexical goal symbol.
        permitted = [
            rush.rsymbol.n
            for rush in expected_terminal_rushes
            if rush.rsymbol.T == 'T_named'
        ]

        REL_is_permitted = ('RegularExpressionLiteral' in permitted)

        TemplateTail_is_permitted = ('TemplateTail' in permitted)
        assert TemplateTail_is_permitted == ('TemplateMiddle' in permitted)

        if REL_is_permitted and TemplateTail_is_permitted:
            lexical_goal = '_TokenRegExpOrTemplateTail'
        elif REL_is_permitted and not TemplateTail_is_permitted:
            lexical_goal = '_TokenRegExp'
        elif TemplateTail_is_permitted and not REL_is_permitted:
            lexical_goal = '_TokenTemplateTail'
        else:
            lexical_goal = '_TokenDiv'

        if trace_level >= 2:
            put('+')
            put(f'+ based on expected_terminal_rushes, lexical_goal = {lexical_goal}')

        # ------------------------------

        token = lexical.run(
            text_posn,
            lexical_goal,
            _lexical_get_next_terminal_instances, # can create Node
            _make_nonterminal_node,               # can create Node
            _lexical_make_Node_here,              # can create Node
            _lexical_node_matches_rush,
            lexical_trace_level,
            trace_f
        )

        assert token is not None
        # because _Earley::run either returns a Node or raises a ParseError

        # ------------------------------

        assert token.start_posn == text_posn
        assert token.start_posn < token.end_posn

        ies.appendToken(token)

        # ------------------------------

        if trace_level >= 2:
            put()
            put('+')
            put('+ We also get any subsequent non_tokens')
            put()

        # Offhand, it seems like it'd make more sense to get non-tokens *before* the token.
        # Instead, we do this this way (*after* getting a token)
        # so that we can handle rush.post.T == 'A_no_LT'
        # in _syntactic_node_matches_rush
        # (for any rush [at any level] whose last token we've just got).
        #
        # (Theoretically, we could make matching non-tokens a completely
        # separate call to this function, i.e. A_no_LT wouldn't be some rush's 'post',
        # but a 'free-standing' right-hand-side-thing.
        # But then we'd need to know when to skip non-tokens *without* caring about LTs,
        # so we'd need to make that explicit in the syntactic grammar,
        # or else make the Earley code aware of the distinction.)

        next_text_posn = find_any_following_non_tokens(token.end_posn) # can create Node

        assert token.end_posn <= next_text_posn

        # ------------------------------

        if trace_level >= 2:
            put()
            put('+')
            put('+ So we have the token (tree) returned by the lexical parser:')
            token.dump('+  ', f=trace_f)
            put('+ and also the subsequent non-tokens:')
            put('+   ....')

        # We have a token, but:
        # (a) it isn't necessarily a token that the syntactic parser is expecting, and
        # (b) even if it is, there's a varying amount of 'superstructure'
        #     that we don't want.

        subtree = token
#        subtree = convert_from_token_to_syntactic_terminal(token) # can create a Node
#
#        assert subtree.start_posn == token.start_posn
#        assert subtree.end_posn == token.end_posn
#
#        if trace_level >= 2:
#            put('+')
#            put('+ The specific subtree that holds what the syntactic parser wants (if anything):')
#            subtree.dump('+  ', f=trace_f)

        # ---------

        if trace_level >= 2:
            put('+')
            put('+ Now we check which (if any) of the expected_terminal_rushes match that...')

        matches = []
        for rush in expected_terminal_rushes:
            terminal_node = syntactic_terminal_node_if_token_matches_rush(token, rush) # can create Node
            if terminal_node:
                matches.append((rush, terminal_node))

        if len(matches) == 0:
            if trace_level >= 2: put("+ The token we found is not expected by the parser.")
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
                ies.a_LineTerminator_occurs_before_current_token()
                or
                subtree.text() == '}'
                or
                any(rush.pre and rush.pre.T == 'A_ASI_rule_1c' for rush in expected_terminal_rushes)
            ):
                if trace_level >= 2: put("+ ASI rule #1 says to insert a semicolon before it.")
                return maybe_insert_a_semicolon(1) # can create Node
            else:
                return None

        else:
            if trace_level >= 2:
                put('+')
                put('+ matching rushes:')
                for match in matches:
                    put('+   ', match[0])
                put('+')
                put(f'+ which _syntactic_get_next_terminal_instances returns with next_text_posn={next_text_posn}')

            return (matches, next_text_posn)

    # --------------------------------------------------------------------------

#    def convert_from_token_to_syntactic_terminal(token):
#        assert token.symbol.startswith('_Token')
#
#        assert len(token.children) == 1
#        [child] = token.children
#        cn = child.symbol
#
#        if cn == 'RegularExpressionLiteral':
#            subtree = child
#
#        else:
#
#            if cn == 'DivPunctuator':
#                assert len(child.children) in [1,2]
#                # make_terminal_node
#                subtree = Node('"' + child.text() + '"', child.whole_text, child.start_posn, child.end_posn)
#
#            elif cn == 'RightBracePunctuator':
#                assert len(child.children) == 1
#                [grandchild] = child.children
#                subtree = grandchild
#
#            elif cn == 'TemplateSubstitutionTail':
#                assert len(child.children) == 1
#                [grandchild] = child.children
#                subtree = grandchild
#                assert subtree.symbol in ['TemplateMiddle', 'TemplateTail']
#
#            elif cn == 'CommonToken':
#                assert len(child.children) == 1
#                [grandchild] = child.children
#                gcn = grandchild.symbol
#
#                if gcn == 'IdentifierName':
#                    subtree = grandchild
#
#                elif gcn in ['NumericLiteral', 'StringLiteral']:
#                    subtree = grandchild
#
#                elif gcn == 'Punctuator':
#                    subtree = grandchild
#
#                elif gcn == 'Template':
#                    assert len(grandchild.children) == 1
#                    [greatgrandchild] = grandchild.children
#                    subtree = greatgrandchild
#                    assert subtree.symbol in ['NoSubstitutionTemplate', 'TemplateHead']
#
#                else:
#                    assert 0
#            else:
#                assert 0
#
#        return subtree

    # --------------------------------------------------------------------------

    def find_any_following_non_tokens(start_text_posn):

        if lexical_trace_level >= 2:
            put('find_any_following_non_tokens:')
            put()
            put(misc.display_position_in_text(source_text, start_text_posn))

        non_tokens = []
        text_posn = start_text_posn
        while True:
            try:
                non_token_node = lexical.run(
                    text_posn,
                    '_NonToken',
                    _lexical_get_next_terminal_instances, # can create lexical Node 
                    _make_nonterminal_node,               # can create Node
                    _lexical_make_Node_here,              # can create Node
                    _lexical_node_matches_rush,
                    lexical_trace_level,
                    trace_f
                )
            except ParseError:
                # Not a problem,
                # we've just consumed all the non-tokens,
                # and are now up against a token.
                ies.appendNonTokens(non_tokens)
                return text_posn

            assert non_token_node.symbol == '_NonToken'
            non_tokens.append(non_token_node)

            text_posn = non_token_node.end_posn

    # --------------------------------------------------------------------------

    def syntactic_terminal_node_if_token_matches_rush(token, rush):

        terminal_node = syntactic_terminal_node_if_token_matches_rsymbol(token, rush.rsymbol) # can create Node

        assert terminal_node is None or isinstance(terminal_node, Node)

        if (
            terminal_node is not None
            and
            syntactic_node_satisfies_pre(terminal_node, rush.pre)
            and
            syntactic_node_satisfies_post(terminal_node, rush.post)
        ):
            return terminal_node
        else:
            return None

    # --------------------------------------------------------------------------

    def _syntactic_node_matches_rush(node, rush):
        x = (
            (
                node.symbol == rush.rsymbol
                or
                rush.rsymbol.T == 'GNT' and rush.rsymbol.o and node.symbol is None
                or 
                rush.rsymbol.T == 'GNT' and node.symbol and node.symbol.startswith(rush.rsymbol.n) # XXX
            )
            and
            syntactic_node_satisfies_pre(node, rush.pre)
            and
            syntactic_node_satisfies_post(node, rush.post)
            and
            syntactic_node_satisfies_adhoc_checks(node)
        )
        return x

    def syntactic_node_satisfies_adhoc_checks(node):
        if node.symbol == goal_symname:
            # Have to go back and check any LAX
            # for which we didn't have enough info at the time.
            # (For simplicity, just recheck all LAX.)
            return tree_satisfies_LAX(node)
        else:
            return True

    def tree_satisfies_LAX(node):
        if not hasattr(node, 'production'):
            return True

        rhs = node.production['rhs']
        children = node.children
        assert len(rhs) == len(children)
        for (rush, child) in zip(rhs, children):
            if rush.pre and rush.pre.T == 'LAX':
                if not syntactic_LAX_is_satisfied(node, rush.pre):
                    return False
            if not tree_satisfies_LAX(child):
                return False

        return True

    # --------------------------------------------------------------------------

    def syntactic_node_satisfies_pre(node, pre):
        if pre is None: return True

        if pre.T in ['A_ASI_rule_1c', 'A_ASI_override']:
            return True

        elif pre.T == 'LAX':
            #" If the phrase &ldquo;[lookahead &notin; _set_]&rdquo;
            #" appears in the right-hand side of a production,
            #" it indicates that the production may not be used
            #" if the immediately following input token sequence
            #" is a member of the given _set_.
            return syntactic_LAX_is_satisfied(node, pre)

        else:
            assert 0, pre

    def syntactic_LAX_is_satisfied(node, lax):
        for lat in lax.ts:
            assert lat.T == 'T_lit'
            if lat.c in ['class', 'function', 'let', '{']:
                x = [lat.c]
            elif lat.c == 'let` `[':
                x = ['let', '*', '[']
            elif lat.c == 'async nLTh function':
                x = ['async', 'nLTh', 'function']
            else:
                assert 0, lat
            if ies.matches_syntactic_lookahead_sequence(node.ies_start, x):
                return False
        return True

    # --------------------------------------------------------------------------

    def syntactic_node_satisfies_post(node, post):
        if post is None:
            return True

        elif post.T == 'A_no_LT':
            #" If the phrase "[no LineTerminator here]" appears
            #" in the right-hand side of a production of the syntactic grammar,
            #" it indicates that the production is a restricted production:
            #" it may not be used if a LineTerminator occurs in the input stream
            #" at the indicated position.
            if ies.a_LineTerminator_occurs_after_current_token():
                return False

        else:
            # assert rush.rsymbol.n == 'IdentifierName'
            assert post == A_but_not(b=[GNT(n="ReservedWord", a=[], o=False)])
            # put("checking '%s' wrt ReservedWords" % node.text())
            if node.text() in ReservedWords:
                return False

        return True

    # --------------------------------------------------------------------------

    def _syntactic_make_Node_here(symbol, text_posn):
        node = Node(symbol, source_text, text_posn, text_posn)
        ies_pos = ies.position()
        # if node.ies_start != ies_pos: print(f"!! for {symbol}, {node.ies_start} != {ies_pos}")
        node.ies_start = ies_pos
        node.ies_end = ies_pos
        return node

    # ==========================================================================

    def _lexical_get_next_terminal_instances(text_posn, expected_terminal_rushes):

        if text_posn > len(source_text):
            assert 0
        elif text_posn == len(source_text):
            # at end of source_text
            return None

        c = source_text[text_posn]

        if lexical_trace_level >= 2:
            put("|+")
            put("|+   posn: %d  char: '%s'" % (text_posn, c))

        rats = []
        for rush in expected_terminal_rushes:
            if lexical_Rsymbol_matches_char(rush.rsymbol, c):
                # make_terminal_node
                node = Node(Rsymbol_exify(rush.rsymbol, {}), source_text, text_posn, text_posn+1) # psettings
                if _lexical_node_matches_rush(node, rush):
                    rats.append((rush, node))

        if len(rats) == 0:
            if lexical_trace_level >= 2:
                put('|+')
                put("|+   which doesn't match anything in expected_terminal_rushes!")

            return None

        else:
            if lexical_trace_level >= 2:
                put('|+')
                put('|+   which matches the following expected_terminal_rushes:')
                for (rush, node) in rats:
                    put('|+   ', Rush_stringify(rush))

            return (rats, text_posn+1)

    # --------------------------------------------------------------------------

    def _lexical_node_matches_rush(node, rush):

        # put('rush:', Rush_stringify(rush))

        # Do we need something like this?:
        # match = lexical_Rsymbol_matches_char(rush.rsymbol, node)

        rsymbol = rush.rsymbol
        if hasattr(rsymbol, 'o') and rsymbol.o and node.symbol is None:
            pass
        elif Rsymbol_exify(rsymbol, {}) == node.symbol:
            # XXX eliminate Rsymbol_exify???
            pass
        else:
            assert 0

        return (
            lexical_node_satisfies_pre(node, rush.pre)
            and 
            lexical_node_satisfies_post(node, rush.post)
            and
            lexical_node_satisfies_adhoc_checks(node)
        )

    def lexical_node_satisfies_pre(node, pre):
        assert pre is None
        return True

    def lexical_node_satisfies_post(node, post):
        if post is None:
            return True

        elif post.T == 'A_but_not':
            c = node.text()
            return not char_matches_any_of_the_symbols(c, post.b)

        elif post.T == 'LAX':
            # (LAX is only a *post* when it occurs at the end of the RHS.)
            if node.end_posn >= len(source_text):
                # There is no following source character,
                # so the lookahead-exclusion can't be violated.
                return True
            else:
                next_c = source_text[node.end_posn]
                return not char_matches_any_of_the_symbols(next_c, post.ts)

        elif post.T == 'A_but_only_if':
            # assert rush.rsymbol.n == 'HexDigits'
            mv = int(node.text(), 16) # XXX should do it by invoking MV
            if post.c == 'MV of HexDigits &le; 0x10FFFF ':
                return (mv <= 0x10ffff)
            elif post.c == 'MV of HexDigits > 0x10FFFF ':
                return (mv > 0x10ffff)
            else:
                assert 0, post.c

        else:
            assert 0, post

    def char_matches_any_of_the_symbols(char, rsymbols):
        assert len(char) == 1
        for rsymbol in rsymbols:
            # put(rsymbol)
            if lexical_Rsymbol_matches_char(rsymbol, char):
                return True
        return False

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

    # --------------------------------------------------------------------------

    def _lexical_make_Node_here(symbol, text_posn):
        return Node(symbol, source_text, text_posn, text_posn)

    def _make_nonterminal_node(prod, psettings, text_posn):
        lhs_symname = prod['lhs']
        node = Node(lhs_symname,  source_text, text_posn, text_posn)
        # XXX clean this up:
        node.production = prod
        node.psettings = psettings
        return node

    # ==========================================================================
    # body of parse():

    return parse_main()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Node:
    def __init__(self, symbol, whole_text, start_posn, end_posn):
        self.symbol = symbol
        self.children = []
        self.whole_text = whole_text
        self.start_posn = start_posn
        self.end_posn = end_posn
        self.ies_start = None
        self.ies_end = None

    def push_child(self, new_child):
        # new_child becomes the new oldest child
        self.children.insert(0, new_child)
        if self.whole_text is None: self.whole_text = new_child.whole_text
        self.start_posn = new_child.start_posn
        self.ies_start = new_child.ies_start
        if len(self.children) == 1:
            self.end_posn = new_child.end_posn
            self.ies_end = new_child.ies_end

    def __str__(self):
        return "<Node symbol=%s, %d children>" % (self.symbol, len(self.children))

    def text(self):
        return self.whole_text[self.start_posn:self.end_posn]

    def dump(self, prefix='  ', self_is_last_child=True, f=sys.stdout):
        # hor_char = ('\u2517' if self_is_last_child else '\u2523')
        hor_char = ("'-" if self_is_last_child else '|-')
        n_children = len(self.children)
        print(
            prefix
            + hor_char
            + ' '
            + ('(omitted)' if self.symbol is None else str(self.symbol))
            + f' [{self.start_posn}:{self.end_posn}]'
            + (' ' + escape(self.text()) if n_children == 0 else ''),
            file=f
        )
        if n_children > 0:
            # sub_hor_char = (' ' if self_is_last_child else '\u2503')
            sub_hor_char = ('  ' if self_is_last_child else '| ')
            child_prefix = prefix + sub_hor_char + ' '
            for (i,child) in enumerate(self.children):
                child.dump(child_prefix, (i == n_children-1), f=f)

    def contains_a(self, symbol):
        return (
            self.symbol == symbol
            or
            any(child.contains_a(symbol) for child in self.children)
        )

def escape(s):
    def uify(mo):
        c = mo.group(0)
        assert len(c) == 1
        return 'U+%x' % ord(c[0])
    return re.sub(r'[^ -~]', uify, s)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# "Rush" is an anagram of RHSU ("Right-Hand-Side Unit")

def Rush_is_nonterminal(rush):
    return Rsymbol_is_nonterminal(rush.rsymbol)

def Rush_is_terminal(rush):
    return Rsymbol_is_terminal(rush.rsymbol)

def Rush_stringify(rush):
    pre = rush.pre
    if pre is None:
        pre_s = ''
    else:
        T = pre.T
        if T == 'LAX':
            pre_s = '[LAX ...] '
        elif T == 'A_no_LT':
            assert len(pre) == 1
            pre_s = '[A_no_LT] '
        elif T == 'A_ASI_rule_1c':
            pre_s = '[ASI rule 1c]'
        elif T == 'A_ASI_override':
            pre_s = '[ASI override]'
        else:
            assert 0, T

    rsymbol_s = Rsymbol_stringify(rush.rsymbol)

    post = rush.post
    if post is None:
        post_s = ''
    elif post.T == 'A_but_not':
        post_s = ' BUT NOT ' + ' '.join(
            Rsymbol_stringify(x) for x in post.b
        )
    elif post.T == 'LAX':
        post_s = ' [lookahead != %s]' % (
            ' '.join(Rsymbol_stringify(t) for t in post.ts)
        )
    else:
        post_s = ' ' + str(post)

    return pre_s + rsymbol_s + post_s

#def Rush_expects_rsymbol(rush, r_rsymbol):
#    l_rsymbol = rush.rsymbol
#    if l_rsymbol == r_rsymbol: return True
#    if (
#        l_rsymbol.T == 'GNT'
#        and r_rsymbol.T == 'GNT'
#        and l_rsymbol.n == r_rsymbol.n
#    ):
#        if l_rsymbol.o and not r_rsymbol.o:
#            return True
#
#        print()
#        print('?', l_rsymbol)
#        print('?', r_rsymbol)
#        sys.exit(0)
#    return False

# -------------------

def Rsymbol_is_nonterminal(rsymbol):
    return rsymbol.T == 'GNT'

def Rsymbol_is_terminal(rsymbol):
    return rsymbol.T.startswith('T_')

def Rsymbol_exify(rsymbol, psettings):
    T = rsymbol.T
    if T == 'GNT':
        a_suffix = ''.join(
            s + n
            for (n, s) in Rsymbol_expand_args(rsymbol, psettings)
        )
        return rsymbol.n + a_suffix # + ('?' if rsymbol.o else '')
    elif T == 'T_EOI':
        return rsymbol.n
    else:
        return Rsymbol_stringify(rsymbol)

def Rsymbol_stringify(rsymbol):
    T = rsymbol.T
    if T == 'GNT':
        if rsymbol.a:
            a_s = '[' + ', '.join(arg.s + arg.n for arg in rsymbol.a) + ']'
        else:
            a_s = ''
        return rsymbol.n + a_s + ('?' if rsymbol.o else '')
    elif T == 'T_EOI':
        return rsymbol.n
    elif T == 'T_lit':
        return '"%s"' % rsymbol.c
    elif T == 'T_named':
        return rsymbol.n
    elif T == 'T_nc':
        return '<%s>' % rsymbol.n
    elif T == 'T_u_p':
        p = rsymbol.p
        if p is None:
            return "> any Unicode code point"
        else:
            return "> any Unicode code point with property '%s'" % p
    else:
        assert 0, rsymbol

def Rsymbol_expand_args(rsymbol, psettings):
    # nset = set()
    for arg in rsymbol.a:
        assert arg.T == 'Arg'
        n = arg.n
        # assert n not in nset; nset.add(n)
        s = arg.s
        if s in ['+', '~']:
            new_s = s
        elif s == '?':
            new_s = psettings[n]
        else:
            assert 0, s
        yield (n, new_s)

def lexical_Rsymbol_matches_char(rsymbol, char):
    assert len(char) == 1

    T = rsymbol.T

    if T == 'T_EOI':
        return False

    elif T == 'T_lit':
        assert len(rsymbol.c) == 1
        return (rsymbol.c == char)

    elif T == 'T_nc':
        n = rsymbol.n
        if n == 'USP':
            #" Any other Unicode 'Space_Separator' code point
            # (where, in this context, "other" means "other than SP and NBSP")
            return (
                unicodedata.category(char) == 'Zs'
                and
                char not in ['\u0020', '\u00a0']
            )
        else:
            return (char == character_named_[n])

    elif T == 'T_u_p':
        p = rsymbol.p
        if p is None:
            return True

        elif p == 'ID_Start':
            # see http://unicode.org/reports/tr31/
            # "Unicode Identifier and Pattern Syntax"
            Other_ID_Start = "\u1885\u1886\u309b\u309c\u2118\u212e"
            cat = unicodedata.category(char)
            return cat in ['Lu', 'Ll', 'Lt', 'Lm', 'Lo', 'Nl'] or char in Other_ID_Start
            # XXX - Pattern_Syntax - Pattern_White_Space

        elif p == 'ID_Continue':
            Other_ID_Continue = "\u1369\u136A\u136b\u136c\u136d\u136e\u136f\u1370\u1371\u19d1\u00b7\u0387"
            cat = unicodedata.category(char)
            return (
                cat in ['Lu', 'Ll', 'Lt', 'Lm', 'Lo', 'Nl', 'Mn', 'Mc', 'Nd', 'Pc']
                # + Other_ID_Continue - Pattern_Syntax - Pattern_White_Space
                or char in Other_ID_Continue
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

    elif T == 'GNT':
        assert rsymbol.a == []
        assert rsymbol.o == False
        assert rsymbol.n in char_set_, rsymbol.n
        return (char in char_set_[rsymbol.n])

    else:
        assert 0, rsymbol

def syntactic_terminal_node_if_token_matches_rsymbol(token, rsymbol):

    # print()
    # print('compare')
    # print(rsymbol)
    # token.dump()

    def descend(lex_node, n):
        if n == 0:
            return lex_node
        else:
            if len(lex_node.children) != 1: return None
            [child] = lex_node.children
            return descend(child, n-1)

    T = rsymbol.T
    if T == 'T_EOI':
        if token.symbol == rsymbol.n:
            something = token
        else:
            something = None

    elif T == 'T_lit':
        lex_text = token.text()

        lex_text = lex_text.replace('\\u0074', 't') # XXX hard-code for pass/3dbb6e166b14a6c0.js

        # print(f"compare '{lex_text}' and '{rsymbol.c}'")
        if lex_text == rsymbol.c:
            # success (so far)
            # make_terminal_node
            something = token

        elif rsymbol.c == ';' and token.text() == '':
            # ASI-inserted semicolon
            something = token

        else:
            something = None

    elif T == 'T_named':
        if rsymbol.n == 'RegularExpressionLiteral':
            n_levels_down = 1
        elif rsymbol.n in ['IdentifierName', 'NumericLiteral', 'StringLiteral', 'TemplateMiddle', 'TemplateTail']:
            n_levels_down = 2
        elif rsymbol.n in ['NoSubstitutionTemplate', 'TemplateHead']:
            n_levels_down = 3
        else:
            assert 0, rsymbol.n
        descendant = descend(token, n_levels_down)
        if descendant is None:
            something = None
        elif descendant.symbol == rsymbol.n:
            something = descendant
        else:
            something = None

    elif T == 'GNT':
        something = token # XXX?

    else:
        assert 0, T

    if something is None:
        if 0:
            print('vvvvvvvv')
            print('syntactic_terminal_node_if_token_matches_rsymbol returning None for:')
            token.dump()
            print('---')
            print(rsymbol)
            print('^^^^^^^^')
        # pdb.set_trace()
        return None

    else:
        # terminal_node = _syntactic_make_Node_here(rsymbol, text_posn)
        terminal_node = Node(
            rsymbol,
            token.whole_text,
            token.start_posn,
            token.end_posn)
        terminal_node.ies_start = token.ies_start
        terminal_node.ies_end   = token.ies_end
        # pdb.set_trace()

        return terminal_node

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

if __name__ == '__main__':
    # test
    tree = parse('14* 3;\n', 'Script', trace_level=0)
    print()
    print('=================')
    print()
    tree.dump()
    print('----------')

# vim: sw=4 ts=4 expandtab
