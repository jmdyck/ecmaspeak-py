#!/usr/bin/python3

# ecmaspeak-py/emu_grammars.py:
# Analyze <emu-grammar> elements.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import atexit, subprocess, re, time, sys, pdb
from collections import namedtuple, defaultdict, OrderedDict

import DFA
import shared
from shared import stderr, msg_at_node, msg_at_posn, spec, SpecNode, decode_entities

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_stuff_with_emu_grammars():
    stderr('do_stuff_with_emu_grammars...')

    emu_grammars_of_type_ = {
        'definition': [],
        'example'   : [],
        'reference' : [],
    }
    for emu_grammar in spec.doc_node.each_descendant_named('emu-grammar'):
        parse_emu_grammar(emu_grammar)
        if 'example' in emu_grammar.attrs:
            t = 'example'
        else:
            t = emu_grammar.attrs.get('type', 'reference')
        emu_grammars_of_type_[t].append(emu_grammar)

    stderr('<emu-grammar> counts:')
    for (t, emu_grammars) in sorted(emu_grammars_of_type_.items()):
        stderr('    ', len(emu_grammars), t)

    process_defining_emu_grammars(emu_grammars_of_type_['definition'])
    check_reachability() # not that useful?

    check_non_defining_prodns(emu_grammars_of_type_['reference'])
    # check_order_of_RHSs_within_each_SDO_clause()
    # too many complaints

    check_emu_prodrefs(spec.doc_node)
    approximate_annex_A()

    check_nonterminal_refs(spec.doc_node)

    make_grammars()
    do_grammar_left_right_stuff()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_grammar(emu_grammar):
    assert emu_grammar.element_name == 'emu-grammar'

    if '\n' in emu_grammar.source_text():
        # one or more productions, indented wrt the <emu-grammar> tag, separated by blank line.
        goal = 'EMU_GRAMMAR_CONTENT_2'
        line_start_posn = 1 + shared.spec_text.rfind('\n', 0, emu_grammar.start_posn)
        emu_grammar_indent = emu_grammar.start_posn - line_start_posn
        assert emu_grammar_indent in [2, 4, 6, 8, 10]

    else:
        # a single one-line production (no line-breaks)
        goal = 'EMU_GRAMMAR_CONTENT_1'
        emu_grammar_indent = None

    gnode = simple_parse(
        metagrammar,
        goal,
        emu_grammar.inner_start_posn,
        emu_grammar.inner_end_posn,
        emu_grammar_indent)

    emu_grammar._gnode = gnode

    if gnode is None:
        stderr(f"    parse_emu_grammar is returning None for {emu_grammar.source_text()}")
        return None

    # --------------------------------------------
    # Perform some checks that could have been expressed in the meta-grammar,
    # but weren't.
    # Also, decorate some nodes for ease of subsequent processing

    gnode.preorder_traversal(decorate_misc)

    if gnode.kind == 'BLOCK_PRODUCTIONS':
        gnode._productions = gnode.children
    elif gnode.kind == 'ONELINE_PRODUCTION':
        gnode._productions = [gnode]
    else:
        assert 0, gnode.kind

    for production_n in gnode._productions:

        (gnt_n, colons_n, r_n) = production_n.children
        (_, params_n, opt_n) = gnt_n.children

        # --------------------------------------------

        production_n._lhs_symbol = gnt_n._nt_name

        # --------------------------------------------

        assert params_n.kind in ['OMITTED_OPTIONAL', 'PARAMS']

        # On LHS, prodn params must have no prefix.
        params_n.preorder_traversal(lambda n: check_param_prefix(n, False))

        # On RHS, prodn params must have a prefix.
        r_n.preorder_traversal(lambda n: check_param_prefix(n, True))

        production_n._param_names = [
            param_n.groups[1]
            for param_n in params_n.children
        ]

        # --------------------------------------------

        # LHS can't be optional.
        if opt_n.source_text() != '':
            msg_at_node(opt_n, "LHS cannot be optional")

        # --------------------------------------------

        production_n._num_colons = len(colons_n.source_text())

        # --------------------------------------------

        rhss = []
        if production_n.kind == 'MULTILINE_PRODUCTION':
            if r_n.kind == 'MULTILINE_RHSS':
                # The standard case: each line is a separate RHS.
                for rhs_line_n in r_n.children:
                    assert rhs_line_n.kind == 'RHS_LINE'
                    rhss.append(rhs_line_n)
                    # -----
                    (optional_guard_n, rhs_body_n, optional_label_n) = rhs_line_n.children
                    items = []
                    if optional_guard_n.source_text() != '':
                        items.append(optional_guard_n)
                    if rhs_body_n.kind == 'EMPTY':
                        pass
                    elif rhs_body_n.kind in ['U_RANGE', 'U_PROP', 'U_ANY', 'NT_BUT_NOT']:
                        items.append(rhs_body_n)
                    elif rhs_body_n.kind == 'RHS_ITEMS':
                        items.extend(rhs_body_n.children)
                    else:
                        assert 0, rhs_body_n.kind
                    if optional_label_n.source_text() != '':
                        items.append(optional_label_n)
                    rhs_line_n._rhs_items = items

            elif r_n.kind == 'MULTILINE_ONE_OF':
                # Each backticked_thing on each line is a separate RHS.
                [lines_of_backticked_things_n] = r_n.children
                assert lines_of_backticked_things_n.kind == 'LINES_OF_BACKTICKED_THINGS'
                for backticked_things_n in lines_of_backticked_things_n.children:
                    assert backticked_things_n.kind == 'BACKTICKED_THINGS'
                    for backticked_thing_n in backticked_things_n.children:
                        rhss.append(backticked_thing_n)
                        # -----
                        backticked_thing_n._rhs_items = [backticked_thing_n]

            else:
                assert 0

        elif production_n.kind == 'ONELINE_PRODUCTION':
            if r_n.kind == 'EMPTY':
                rhss.append(r_n)
                # -----
                r_n._rhs_items = []

            elif r_n.kind == 'RHS_ITEMS':
                rhss.append(r_n)
                # -----
                r_n._rhs_items = r_n.children

            elif r_n.kind == 'NT_BUT_NOT':
                rhss.append(r_n)
                # -----
                r_n._rhs_items = [r_n]

            elif r_n.kind == 'ONELINE_ONE_OF':
                [backticked_things_n] = r_n.children
                for backticked_thing_n in backticked_things_n.children:
                    rhss.append(backticked_thing_n)
                    # -----
                    backticked_thing_n._rhs_items = [backticked_thing_n]

            else:
                assert 0, r_n.kind

        else:
            assert 0, production_n.kind

        for rhs in rhss:
            rhs._reduced = reduce_rhs(rhs)

        production_n._rhss = rhss

def reduce_rhs(rhs_n):
    pieces = []
    for r_item in rhs_n._rhs_items:
        if r_item.kind in [
            'BACKTICKED_THING',
            'NAMED_CHAR',
            'NT_BUT_NOT',
            'U_ANY',
            'U_PROP',
            'U_RANGE',
        ]:
            pieces.append(r_item.source_text())

        elif r_item.kind == 'GNT':
            # Drop the params
            (nt_n, params_n, opt_n) = r_item.children
            pieces.append(nt_n.source_text() + opt_n.source_text())

        elif r_item.kind in [
            'BUT_ONLY',
            'LABEL',
            'LAC_SET',
            'LAC_SINGLE',
            'NLTH',
            'PARAMS',
        ]:
            pass

        else:
            assert 0, r_item.kind

    rr = ' '.join(pieces)
    return rr

def decorate_misc(node):
    if node.kind == 'GNT':
        (nt_n, params_n, opt_n) = node.children
        node._nt_name = nt_n.source_text()
        node._params = [param_n.groups for param_n in params_n.children]
        node._is_optional = opt_n.source_text() == '?'
        return 'prune'

    elif node.kind == 'NT_BUT_NOT':
        (nt_n, exclusion_n) = node.children
        nt_n._nt_name = nt_n.source_text()
        if exclusion_n.kind == 'EXCLUDABLES':
            exclusion_n._excludables = exclusion_n.children
            assert len(exclusion_n._excludables) > 1
        else:
            exclusion_n._excludables = [exclusion_n]
        # may have to treat `node` like a GNT:
        node._nt_name = nt_n._nt_name
        node._params = []
        node._is_optional = False

    elif node.kind == 'NT':
        node._nt_name = node.source_text()

    elif node.kind == 'BACKTICKED_THING':
        node._chars = decode_entities(node.groups[0])
        return 'prune'

def check_param_prefix(node, must_have_prefix):
    if node.kind != 'OPTIONAL_PREFIX': return
    o_p_text = node.source_text()
    if o_p_text != '' and not must_have_prefix:
        msg_at_node(node, "On LHS, param must not have a prefix")
    elif o_p_text == '' and must_have_prefix:
        msg_at_node(node, "On RHS, param must have a prefix")
    return 'prune'

    assert optionality.source_text() == ''

# ------------------------------------------------------------------------------

metagrammar = {
    'EMU_GRAMMAR_CONTENT_1': ('_', '^', 'ONELINE_PRODUCTION', 'EOI'),
    'EMU_GRAMMAR_CONTENT_2': ('_', '^', 'INDENT', 'BLOCK_PRODUCTIONS', 'OUTDENT', 'NLAI', 'EOI'),

    'BLOCK_PRODUCTIONS'    : ('+', 'n', 'BLOCK_PRODUCTION', r'\n'),
    'BLOCK_PRODUCTION'     : ('|', '^', 'MULTILINE_PRODUCTION', '_ONELINE_PRODUCTION'),

    'MULTILINE_PRODUCTION' : ('_', 'n', 'OPTIONAL_COMMENT_LINE', 'NLAI', 'GNT', ' ', 'COLONS', 'MULTILINE_R'),
    'OPTIONAL_COMMENT_LINE': ('?', ' ', 'NLAI', '// emu-format ignore'),
    'MULTILINE_R'          : ('|', '^', 'MULTILINE_ONE_OF', 'MULTILINE_RHSS'),
    'MULTILINE_ONE_OF'     : ('_', 'n', ' one of', 'INDENT', 'NLAI', 'LINES_OF_BACKTICKED_THINGS', 'OUTDENT'),
    'LINES_OF_BACKTICKED_THINGS': ('+', 'n', 'BACKTICKED_THINGS', 'NLAI'),

    '_ONELINE_PRODUCTION'  : ('_', '^', 'NLAI', 'ONELINE_PRODUCTION'),
    'ONELINE_PRODUCTION'   : ('_', 'n', 'GNT', ' ', 'COLONS', ' ', 'ONELINE_R'),
    'ONELINE_R'            : ('|', '^', 'ONELINE_ONE_OF', 'RHS_BODY'),
    'ONELINE_ONE_OF'       : ('_', 'n', 'one of ', 'BACKTICKED_THINGS'),

    'BACKTICKED_THINGS'    : ('+', 'n', 'BACKTICKED_THING', ' '),

    'MULTILINE_RHSS'       : ('+', 'n', 'RHS_LINE', '', 'INDENT', 'OUTDENT'),
    'RHS_LINE'             : ('_', 'n', 'NLAI', 'OPTIONAL_GUARD', 'RHS_BODY', 'OPTIONAL_LABEL'),
    'OPTIONAL_GUARD'       : ('?', '^', 'PARAMS', ' '),
    'OPTIONAL_LABEL'       : ('?', '^', ' ', 'LABEL'),
    'RHS_BODY'             : ('|', '^', 'U_RANGE', 'U_PROP', 'U_ANY', 'EMPTY', 'NT_BUT_NOT', 'RHS_ITEMS'),

    'NT_BUT_NOT'           : ('_', 'n', 'NT', ' but not ', 'EXCLUSION'),
    'EXCLUSION'            : ('|', '^', 'EXCLUDABLES', 'EXCLUDABLE'),
    'EXCLUDABLES'          : ('+', 'n', 'EXCLUDABLE', ' or | ', 'one of ', ''),
    'EXCLUDABLE'           : ('|', '^', 'NT', 'BACKTICKED_THING'),

    'RHS_ITEMS'            : ('+', 'n', 'RHS_ITEM', ' '),
    'RHS_ITEM'             : ('|', '^', 'GNT', 'BACKTICKED_THING', 'NAMED_CHAR', 'LOOKAHEAD_CONSTRAINT', 'NLTH', 'BUT_ONLY'),

    'GNT'                  : ('_', 'n', 'NT', 'OPTIONAL_PARAMS', 'OPTIONAL_OPT'),
    'OPTIONAL_PARAMS'      : ('?', '^', 'PARAMS'),
    'PARAMS'               : ('+', 'n', 'PARAM', ', ', r'\[', r'\]'),
    'OPTIONAL_OPT'         : ('?', 'n', r'\?'),

    'LOOKAHEAD_CONSTRAINT' : ('|', '^', 'LAC_SINGLE', 'LAC_SET'),
    'LAC_SINGLE'           : ('_', 'n', r'\[lookahead ', 'LAC_SINGLE_OP', ' ', 'TERMINAL_SEQ', r'\]'),
    'LAC_SINGLE_OP'        : ('/', 'n', '==|!='),
    'LAC_SET'              : ('_', 'n', r'\[lookahead ', 'LAC_SET_OP', ' ', 'LAC_SET_OPERAND', r'\]'),
    'LAC_SET_OP'           : ('/', 'n', '&isin;|&notin;'),
    'LAC_SET_OPERAND'      : ('|', '^', 'NT', 'SET_OF_TERMINAL_SEQ'),
    'SET_OF_TERMINAL_SEQ'  : ('+', 'n', 'TERMINAL_SEQ', ', ', '{ ', ' }'),
    'TERMINAL_SEQ'         : ('+', 'n', 'TERMINAL_ITEM', ' '),
    'TERMINAL_ITEM'        : ('|', '^', 'BACKTICKED_THING', 'NAMED_CHAR', 'NLTH'),

    'BUT_ONLY'             : ('/', 'n', r'\[> but only if ([^][]+)\]'),

    'INDENT'           : ('/', ' ', ''),
    'OUTDENT'          : ('/', ' ', ''),
    'EOI'              : ('/', ' ', ''),
    'NLAI'             : ('/', ' ', r'\n +'),

    'COLONS'           : ('/', 'n', r':+'),
    'PARAM'            : ('/', 'n', r'([~+?]?)([A-Z][a-zA-Z]*)'),
    'NT'               : ('/', 'n', r'[A-Z]\w*|uri\w*|@'),
    'LABEL'            : ('/', 'n', r'#\w+'),
    'EMPTY'            : ('/', 'n', r'\[empty\]'),
    'NLTH'             : ('/', 'n', r'\[no LineTerminator here\]'),
    'U_RANGE'          : ('/', 'n', r'&gt; any Unicode code point in the inclusive range (0x[0-9A-F]+) to (0x[0-9A-F]+)'),
    'U_PROP'           : ('/', 'n', r'&gt; any Unicode code point with the Unicode property &ldquo;(\w+)&rdquo;'),
    'U_ANY'            : ('/', 'n', r'&gt; any Unicode code point'),
    'BACKTICKED_THING' : ('/', 'n', r'`([^` ]+|`)`'),
    'NAMED_CHAR'       : ('/', 'n', r'&lt;([A-Z]+)&gt;'),
}

# ------------------------------------------------------------------------------

def simple_parse(grammar, goal, start_posn, end_posn, start_indent):
    max_error_posn = start_posn
    max_error_expectations = []

    def maybe_log_expectation(posn, expectation):
        nonlocal max_error_posn, max_error_expectations
        if posn > max_error_posn:
            max_error_posn = posn
            max_error_expectations = [expectation]
        elif posn == max_error_posn:
            max_error_expectations.append(expectation)

    t = False # shared.spec_text.startswith('\n        ReservedWord', start_posn)

    def attempt(goal, at_start_posn, at_start_indent, level):
        # Consider shared.spec_text[at_start_posn:end_posn]
        # and attempt to match some prefix of it to `goal`.
        # If it doesn't match, return None.
        # If it does, return a tuple containing:
        #   - the posn after the match.
        #   - the current indent after the match.
        #   - a GNode representing the match, or None.

        _ind = '  '*level
        def trace(*args):
            if not t: return
            print(_ind, end='')
            print(*args)

        trace(f"{goal}")
        trace(f"At {at_start_posn} {shared.spec_text[at_start_posn:at_start_posn+20]!r}")

        if goal in grammar:
            (pkind, rkind, *args) = grammar[goal]
        else:
            assert not re.fullmatch(r'[A-Z_]+', goal), goal
            pkind = '/'
            rkind = ' '
            args = [goal]

        if pkind == '|': # alternatives
            for alt in args:
                r = attempt(alt, at_start_posn, at_start_indent, level+1)
                if r is not None:
                    assert rkind == '^'
                    return r
                    # Note that this doesn't create a GNode corresponding to `goal` itself.
            return None

        elif pkind == '_': # concatenation
            posn = at_start_posn
            indent = at_start_indent
            children = []
            for child_goal in args:
                r = attempt(child_goal, posn, indent, level+1)
                if r is None: return None
                (posn, indent, child) = r
                if child: children.append(child)

            if rkind == 'n':
                result = GNode(at_start_posn, posn, goal, children)
            elif rkind == '^':
                # pass-up
                assert len(children) == 1
                [result] = children
            else:
                assert 0, rkind

            return (posn, indent, result)

        elif pkind == '?': # optional
            posn = at_start_posn
            indent = at_start_indent
            children = []
            for child_goal in args:
                r = attempt(child_goal, posn, indent, level+1)
                if r is None:
                    # We failed to find an instance of {child_goal},
                    # and so we've failed to find an instance of {goal}.
                    # I.e., the optional thing has been omitted.
                    # So (maybe) make a GNode to hold the representation of that absence.
                    if rkind == 'n':
                        result = GNode(at_start_posn, at_start_posn, goal, [])
                    elif rkind == '^':
                        result = GNode(at_start_posn, at_start_posn, 'OMITTED_OPTIONAL', [])
                    elif rkind == ' ':
                        result = None
                    else:
                        assert 0, rkind
                    return (at_start_posn, indent, result)
                (posn, indent, child) = r
                if child: children.append(child)
            # optional thing is there
            if rkind == 'n':
                result = GNode(at_start_posn, posn, goal, children)
            elif rkind == '^':
                assert len(children) == 1
                [result] = children
            elif rkind == ' ':
                result = None
            else:
                assert 0, rkind
            return (posn, indent, result)

        elif pkind == '+': # list of one or more
            if len(args) == 2:
                (element_name, separator) = args
                left_delim = None; right_delim = None
            elif len(args) == 4:
                (element_name, separator, left_delim, right_delim) = args
            else:
                assert 0, args

            elements = []

            posn = at_start_posn
            indent = at_start_indent

            if left_delim:
                r = attempt(left_delim, posn, indent, level+1)
                if r is None:
                    trace("failed at left_delim")
                    return None
                (posn, indent, _) = r

            while True:

                r = attempt(element_name, posn, indent, level+1)
                if r is None:
                    if elements == []:
                        # This would have been the first element in the list,
                        # so a failure to parse it is a syntax error.
                        trace("failed at first element")
                        return None
                    else:
                        # We've already recognized some elements,
                        # so failure to parse another isn't necessarily a syntax error,
                        # it could just be that we should have stopped after the latest element,
                        # i.e. just before the separator.
                        posn = latest_sep_start_posn
                        break

                (posn, indent, element) = r
                elements.append(element)

                latest_sep_start_posn = posn
                r = attempt(separator, posn, indent, level+1)
                if r is None: break
                (posn, indent, _) = r

            if right_delim:
                r = attempt(right_delim, posn, indent, level+1)
                if r is None:
                    trace("failed at right delim")
                    return None
                (posn, indent, _) = r

            node = GNode(at_start_posn, posn, goal, elements)
            return (posn, indent, node)

        elif pkind == '/': # regular expression
            [pattern] = args

            mo = re.compile(pattern).match(shared.spec_text, at_start_posn)
            if mo is None:
                if goal == pattern:
                    expectation = repr(pattern)
                else:
                    expectation = f"{goal} {pattern!r}"
                maybe_log_expectation(at_start_posn, expectation)
                trace("failed to match regex")
                return None

            assert mo.start() == at_start_posn
            at_end_posn = mo.end()

            trace(f"{at_start_posn}-{at_end_posn} found {goal!r}: {shared.spec_text[at_start_posn:at_end_posn]!r}")

            indent = at_start_indent
            if goal == 'INDENT':
                indent += 2
                trace(f"indent increased to {indent}")
            elif goal == 'OUTDENT':
                indent -= 2
                trace(f"indent decreased to {indent}")
            elif goal == 'NLAI':
                this_indent = at_end_posn - at_start_posn - 1
                assert this_indent % 2 == 0
                if this_indent != at_start_indent:
                    maybe_log_expectation(at_end_posn, f"indent = {at_start_indent}")
                    trace(f"failed to match indent = {at_start_indent}")
                    return None
            elif goal == 'EOI':
                if at_end_posn < end_posn:
                    maybe_log_expectation(at_end_posn, "end-of-input")
                    trace("failed to match eoi")
                    return None

            if rkind == 'n':
                result = GNode(mo.start(), mo.end(), goal, [])
                result.groups = mo.groups()
            elif rkind == ' ':
                result = None
            else:
                assert 0, rkind
            return (at_end_posn, indent, result)

        else:
            assert 0, pkind

    # input('continue? ')
    r = attempt(goal, start_posn, start_indent, 0)
    if r is None:
        msg_at_posn(max_error_posn, f"Syntax error: was expecting: {', '.join(max_error_expectations)}")
        return None
    (at_end_posn, at_end_indent, node) = r
    assert at_end_posn == end_posn
    assert at_end_indent == start_indent
    return node

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class GNode(SpecNode):
    def __init__(self, start_posn, end_posn, kind, children):
        SpecNode.__init__(self, start_posn, end_posn)
        self.kind = kind
        self.children = children

    def __str__(self):
        st = self.source_text()
        snippet = st if len(st) <= 50 else (st[0:47] + '...')
        return f"({self.kind} {snippet!r})"

    def tree_slug(self):
        return str(self)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

info_for_nt_ = None

def process_defining_emu_grammars(emu_grammars):
    stderr('process_defining_emu_grammars...')

    global info_for_nt_
    grammar_f = shared.open_for_output('def_prodns')
    info_for_nt_ = defaultdict(NonterminalInfo)

    # Each defining production is assigned a doc_i,
    # giving its index in document order.
    next_doc_i = 0

    for emu_grammar in emu_grammars:
        # emu_grammar is an HNode (see static.py)
        # representing an <emu-grammar> element
        # that contains rules that *define* a chunk of the grammar
        # (as opposed to merely reference it).

        assert emu_grammar.attrs['type'] == 'definition'

        cc_section = emu_grammar.closest_containing_section()

        print(file=grammar_f)
        print('#', cc_section.section_num, cc_section.section_title, file=grammar_f)
        print(file=grammar_f)
        print(decode_entities(trim_newlines(emu_grammar.inner_source_text())), file=grammar_f)

        # stderr(cc_section.section_num, cc_section.section_title)

        gnode = emu_grammar._gnode
        assert gnode.kind == 'BLOCK_PRODUCTIONS'

        for production_n in gnode.children:
            production_n.doc_i = next_doc_i; next_doc_i += 1
            defining_production_check_left(production_n, cc_section)

    for emu_grammar in emu_grammars:
        gnode = emu_grammar._gnode
        for production_n in gnode.children:
            defining_production_check_right(production_n)

            if production_n._augments:
                stderr(f"    augmenting {production_n._lhs_symbol}")
                nt_info = info_for_nt_[production_n._lhs_symbol]
                base_production_n = nt_info.get_appropriate_def_occ('A')
                production_n._rhss = base_production_n._rhss + production_n._rhss

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def defining_production_check_left(production_n, cc_section):
    assert production_n.kind == 'MULTILINE_PRODUCTION'
    assert cc_section.element_name in ['emu-clause', 'emu-annex']

    # ------------------

    production_n._arena = get_grammar_arena_for_section(cc_section)

    if production_n._arena == 'B':
        # Some are replacements, and some are augments. Need to know which.
        # Could detect it based on whether the preceding para says
        #   "The following augments the <Foo> production in <section-num>:"
        # but easier to hard-code it:
        production_n._augments = (cc_section.section_title in [
            'FunctionDeclarations in IfStatement Statement Clauses',
            'Initializers in ForIn Statement Heads',
        ])
    else:
        production_n._augments = False

    # ------------------

    # This function looks at only the LHS and colons of the production.

    # ------------------

    if cc_section.section_title == 'URI Syntax and Semantics':
        lhs_nt_pattern = r'^uri([A-Z][a-z]+)?$'
    else:
        lhs_nt_pattern = r'^[A-Z][a-zA-Z0-9]+$'
    assert re.match(lhs_nt_pattern, production_n._lhs_symbol), production_n._lhs_symbol

    # ==============================================

    if production_n._lhs_symbol not in info_for_nt_:
        nt_info = NonterminalInfo()
        info_for_nt_[production_n._lhs_symbol] = nt_info
        # initialize nt_info with this production's data
        nt_info.num_colons = production_n._num_colons
        nt_info.level = 'syntactic' if nt_info.num_colons == 1 else 'lexical'

    else:
        nt_info = info_for_nt_[production_n._lhs_symbol]
        # check that this production's data agrees with previously-extracted data
        assert production_n._num_colons == nt_info.num_colons
        # msg_at_posn(prodn_posn, f"ERROR: colons mismatch for {production_n._lhs_symbol}: was {nt_info.num_columns}, here {production_n._num_colons}")
        assert production_n._arena not in nt_info.def_occs
        # msg_at_posn(prodn_posn, f"Additional defining production for: {production_n._lhs_symbol}")

    nt_info.def_occs[production_n._arena] = production_n

# ------------------------------------------------------------------------------

class NonterminalInfo:
    def __init__(self):
        self.def_occs = defaultdict()

#        if augments:
#            assert arena != 'A'
#            (_, params_from_arena_a, rhss_from_arena_a) = self.def_occs['A']
#            assert params == params_from_arena_a
#            rhss = rhss_from_arena_a + rhss

    def get_appropriate_def_occ(self, arena):
        if arena in self.def_occs:
            a = arena
        else:
            if 'A' in self.def_occs:
                a = 'A'
            else:
                return None
        return self.def_occs[a]

def check_reachability():
    stderr("check_reachability...")
    queue = []
    lexical_symbols = set()

    def reach(symbol):
        if symbol in lexical_symbols:
            return
        else:
            lexical_symbols.add(symbol)
            if symbol in queue:
                pass
            else:
                # print('    push', symbol)
                queue.append(symbol)

    reach('InputElementDiv')
    reach('InputElementRegExp')
    reach('InputElementRegExpOrTemplateTail')
    reach('InputElementTemplateTail')
    reach('uri')
    reach('StringNumericLiteral')
    reach('Pattern')

    while queue:
        symbol = queue.pop(0)
        nt_info = info_for_nt_[symbol]
        production_n = nt_info.def_occs['A']
        for rhs_n in production_n._rhss:
            for rhs_item_n in rhs_n._rhs_items:
                rthing_kind = rhs_item_n.kind
                if rthing_kind in ['GNT', 'NT']:
                    reach(rhs_item_n._nt_name)
                elif rthing_kind == 'NT_BUT_NOT':
                    (nt_n, exclusion_n) = rhs_item_n.children
                    reach(nt_n._nt_name)
                    for but_n in exclusion_n._excludables:
                        if but_n.kind == 'NT':
                            reach(but_n._nt_name)

    for (nt, nt_info) in sorted(info_for_nt_.items()):
        if 'A' in nt_info.def_occs and nt_info.num_colons != 1 and nt not in lexical_symbols:
            stderr('    lexical symbol not reached:', nt)

# ------------------------------------------------------------------------------

# g_current_branch_name = subprocess.check_output('git rev-parse --abbrev-ref HEAD'.split(' ')).rstrip()

def defining_production_check_right(production_n):

    for (rhs_i, rhs_n) in enumerate(production_n._rhss):
        if rhs_n.kind == 'RHS_LINE':
            (optional_guard_n, rhs_body_n, optional_label_n) = rhs_n.children

            guards = []
            for param_n in optional_guard_n.children:
                (prefix, param_name) = param_n.groups
                assert prefix in ['+', '~']
                assert param_name in production_n._param_names
                guards.append( (prefix, param_name) )

            # Could test that optional_label_n is unique within this production,
            # but they're used so little, it's not really worth the bother?

            if rhs_body_n.kind == 'RHS_ITEMS':
                for rhs_item_n in rhs_body_n.children:

                    if rhs_item_n.kind != 'GNT':
                        continue

                    (nt_n, optional_params_n, optional_opt_n) = rhs_item_n.children

                    r_arg_signs = []
                    r_arg_names = []
                    for r_arg in optional_params_n.children:
                        (prefix, arg_name) = r_arg.groups
                        if prefix not in ['+', '~', '?']:
                            msg_at_node(r_arg,
                                f"ERROR: arg is missing +~?"
                            )
                        r_arg_signs.append(prefix)
                        r_arg_names.append(arg_name)

                    r_nt_name = rhs_item_n._nt_name

                    if r_nt_name not in info_for_nt_:
                        msg_at_node(nt_n,
                            f"ERROR: reference to undefined nonterminal 'r_nt_name'"
                        )
                        continue

                    d_production_n = info_for_nt_[r_nt_name].get_appropriate_def_occ(production_n._arena)
                    d_param_names = d_production_n._param_names

                    if len(r_arg_names) == len(d_param_names):
                        if r_arg_names != d_param_names:
                            msg_at_node(optional_params_n,
                                f"ERROR: args are ordered {r_arg_names} but should be {d_param_names}"
                            )
                    else:
                        msg_at_node(optional_params_n,
                            f"ERROR: {r_nt_name} takes {d_param_names} but is invoked with {r_arg_names}"
                        )

                    # Look for valid-but-anomalous args...
                    # for (r_arg_sign, r_arg_name) in zip(r_arg_signs, r_arg_names):
                    for r_arg in optional_params_n.children:
                        (prefix, arg_name) = r_arg.groups

                        if arg_name in production_n._param_names:
                            # This arg refers to a parameter that appears on the prodn's LHS.
                            # So normally, we'd expect a '?' prefix.
                            if prefix == '?': 
                                # Good.
                                pass
                            elif (prefix, arg_name) in guards:
                                # This is equivalent to '?'
                                pass
                            else:
                                msg_at_node(r_arg,
                                    f"WARNING: {production_n._lhs_symbol} has {arg_name} param, so you'd normally expect [?{arg_name}] in its rhss"
                                )
                        else:
                            # This arg refers to parameter
                            # that does not appear on the prodn's LHS.
                            # assert prefix != '?', rhs
                            if prefix == '?':
                                msg_at_node(production_n,
                                    f"ERROR: {arg_name} does not appear on the prodn's LHS, so cannot be referenced with '?'"
                                )
                            # because you can only use '?' on the RHS
                            # when the parameter is 'declared' on the LHS

        elif rhs_n.kind == 'BACKTICKED_THING':
            # nothing to check?
            pass

        else:
            assert 0, rhs_n.kind

# ------------------------------------------------------------------------------

def get_grammar_arena_for_section(section):
    if section.section_title == 'Grammar Notation':
        return 'E' # Examples
    elif section.section_num.startswith('B'):
        return 'B'
    else:
        return 'A'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_non_defining_prodns(emu_grammars):
    stderr("check_non_defining_prodns...")

    for emu_grammar in emu_grammars:
        emu_grammar.puk_set = set()

        # The production(s) in this emu_grammar are (in some sense)
        # instances of productions defined elsewhere,
        # and we'll be comparing the two to determine if these are correct.
        # To distinguish, we'll use two different prefixes:
        # 'd_' for the defining production, and
        # 'u_' for the 'use' production.
        # (You might expect 'r_' for 'referencing',
        # but I already use 'r_' for 'right-hand side'.)

        cc_section = emu_grammar.closest_containing_section()
        u_arena = get_grammar_arena_for_section(cc_section)

        gnode = emu_grammar._gnode

        lhs_nt_for_this_emu_grammar = set()

        for u_production_n in gnode._productions:
            assert u_production_n.kind in ['ONELINE_PRODUCTION', 'MULTILINE_PRODUCTION']
            (u_gnt_n, u_colons_n, _) = u_production_n.children
            (u_nt_n, u_params_n, _) = u_gnt_n.children

            # -----------------------

            lhs_nt = u_production_n._lhs_symbol

            if lhs_nt not in info_for_nt_:
                msg_at_node(u_nt_n,
                    f"ERROR: lhs symbol {lhs_nt} in 'use' production does not match any defined nonterminal"
                )
                continue

            nt_info = info_for_nt_[lhs_nt]

            # Disable this because too many hits:
            if False and lhs_nt in lhs_nt_for_this_emu_grammar:
                msg_at_node(u_nt_n,
                    f"{lhs_nt} already appears as a lhs symbol in this <emu-grammar>"
                )
            lhs_nt_for_this_emu_grammar.add(lhs_nt)

            # -----------------------

            u_num_colons = u_production_n._num_colons
            if u_num_colons != nt_info.num_colons:
                msg_at_node(u_colons_n,
                    f"ERROR: #colons in use ({u_num_colons}) does not match #colons in defn ({nt_info.num_colons})"
                )

            # -----------------------

            u_param_names = u_production_n._param_names

            d_production_n = nt_info.get_appropriate_def_occ(u_arena)

            if d_production_n._param_names:
                # The 'def' production has parameters.
                if u_param_names:
                    # The 'use' production also shows parameters.
                    u_lhs_args_are_suppressed = False

                    if u_param_names != d_production_n._param_names:
                        msg_at_node(u_params_n,
                            f"ERROR: params in use ({u_param_names}) does not match params in defn ({d_production_n._param_names})"
                        )

                    elif cc_section.attrs['id'] in [
                        'sec-rules-of-automatic-semicolon-insertion',
                        'sec-identifiers-static-semantics-early-errors',
                        'sec-primary-expression',
                        'sec-static-semantics-template-early-errors',
                        'sec-arrow-function-definitions',
                    ]:
                        # This is an uncommon case (~20 occurrences),
                        # where the 'def' production has parameters
                        # and the 'use' production repeats them
                        # (because accompanying prose needs to refer to them).
                        pass

                    else:
                        msg_at_node(u_params_n,
                            f"INFO: params in a 'use' prodn is unusual: {u_param_names}"
                        )

                else:
                    # This is a typical case (~958 occurrences),
                    # where a 'use' production elides the parameters
                    # specified in the 'def' production.
                    u_lhs_args_are_suppressed = True
            else:
                # The 'def' production doesn't have parameters.
                # (~430 occurrences)
                u_lhs_args_are_suppressed = None
                if u_param_names:
                    msg_at_node(u_params_n,
                        f"ERROR: 'use' prodn has lhs-parameters but def prodn does not"
                    )

            # In the use-prodn, we expect rhs-args iff there are lhs-params.
            # u_expect_rhs_args = len(u_prodn_params) > 0

            # --------------------------
            # In 'use' productions, we don't usually have annotations

            u_rhss = u_production_n._rhss

            for u_rhs_n in u_rhss:

                annotations = []
                for u_rhs_item_n in u_rhs_n._rhs_items:
                    if u_rhs_item_n.kind in ['GNT', 'NT_BUT_NOT', 'BACKTICKED_THING', 'NAMED_CHAR']:
                        pass
                    elif u_rhs_item_n.kind in ['LAC_SINGLE', 'LAC_SET', 'NLTH', 'PARAMS', 'LABEL']:
                        annotations.append(u_rhs_item_n)
                    else:
                        assert 0, u_rhs_item_n.kind

                for annotation_n in annotations:
                    if cc_section.section_title == 'Rules of Automatic Semicolon Insertion' and annotation_n.kind in ['NLTH', 'PARAMS', 'LABEL']:
                        # allow it
                        pass
                    elif (lhs_nt, annotation_n.kind) in [
                        ('NotEscapeSequence',     'LAC_SET'),
                        ('NotEscapeSequence',     'LAC_SINGLE'),
                        ('CharacterEscape',       'LAC_SET'),
                        ('ClassAtomNoDash',       'LAC_SINGLE'),
                        ('ExtendedAtom',          'LAC_SINGLE'),
                    ]:
                        # allow it
                        pass
                    else:
                        msg_at_node(annotation_n,
                            f"INFO: unusual to include annotation in 'use' production"
                        )

            # --------------------------

            # Match 'use' RHSs against 'defining' RHSs.

            matches = []

            d_rhss = d_production_n._rhss

            for (u_i, u_rhs_n) in enumerate(u_rhss):
                for (d_i, d_rhs_n) in enumerate(d_rhss):
                    # Does u_rhs_n match d_rhs_n?

                    notes = u_rhs_matches_d_rhs_(u_rhs_n, d_rhs_n)
                    if notes == False:
                        # Nope, doesn't match. Try the next d_rhs_n.
                        continue

                    # Yes, it does match...

                    matches.append( (u_i, d_i) )

                    # ------------------

                    if u_lhs_args_are_suppressed is None:
                        pass
                    elif u_lhs_args_are_suppressed:
                        notes['nt-args suppressed'].insert(0, lhs_nt)
                    else:
                        notes['nt-args intact'].insert(0, lhs_nt)

                    if notes['nt-args suppressed'] and notes['nt-args intact']:
                        msg_at_node(u_production_n, "ERROR: RHS suppresses args for %s but not for %s" %
                            (notes['nt-args suppressed'], notes['nt-args intact'])
                        )

                    # ------------------

                    if notes['annotations suppressed'] and notes['annotations intact']:
                        msg_at_node(u_production_n,
                            f"WARNING: RHS suppresses some annotations ({notes['annotations suppressed']}) but leaves some intact ({notes['annotations intact']})"
                        )

                    # ------------------

                    if 0 and notes['optional-GNT']:
                        print(lhs_nt, d_i, notes['optional-GNT'])

                    # ------------------

                    if 0:
                        for (k,v) in notes.items():
                            if k.startswith('L-'):
                                for one in v:
                                    assert one == 1
                                    print(k)

                    # ------------------

                    def each_optbits_covered_by(optionals):
                        if optionals == []:
                            yield ''
                        else:
                            [head, *tail] = optionals
                            (nt, optionality) = head
                            assert optionality in ['omitted', 'required', 'either']
                            if optionality in ['omitted', 'either']:
                                for tail_optbits in each_optbits_covered_by(tail):
                                    yield '0' + tail_optbits
                            if optionality in ['required', 'either']:
                                for tail_optbits in each_optbits_covered_by(tail):
                                    yield '1' + tail_optbits

                    for optbits in each_optbits_covered_by(notes['optional-GNT']):
                        # Production Use Key
                        puk = (lhs_nt, d_rhs_n._reduced, optbits)
                        emu_grammar.puk_set.add(puk)

            # --------------------------

            # process matches

            # Each 'use' RHS should match exactly one 'def' RHS.
            dis_for_ui_ = defaultdict(list)
            for (u_i, d_i) in matches:
                dis_for_ui_[u_i].append(d_i)
            for u_i in range(len(u_rhss)):
                dis = dis_for_ui_[u_i]
                u_rhs = u_rhss[u_i]
                L = len(dis)
                if L == 0:
                    msg_at_node(u_rhs,
                        f"ERROR: This RHS does not match any defining RHS for {lhs_nt}"
                    )
                    u_rhs.d_i = None
                elif L == 1:
                    # good
                    [u_rhs.d_i] = dis
                else:
                    msg_at_node(u_rhs,
                        f"WARNING: This RHS matches {L} defining RHSs for {lhs_nt} [but probably resolved by guards]"
                    )
                    u_rhs.d_i = min(dis)
                u_rhs.d_production_n = d_production_n

            # As you walk through the 'use' RHSs in order,
            # the corresponding 'def' RHSs should also be in order
            # (though with possible 'holes' of course).
            uis = [u_i for (u_i, d_i) in matches]
            dis = [d_i for (u_i, d_i) in matches]
            assert uis == sorted(uis)
            if dis == sorted(dis):
                # good
                pass
            else:
                msg_at_node(u_rhss[-1],
                    f"ERROR: 'use' RHSs are out-of-order wrt corresponding def RHSs: {[i+1 for i in dis]}"
                )

            # Each 'def' RHS should match at most one 'use' RHS.
            # (Actually, it *could* legitimately match more than one.
            # E.g. consider a def RHS that has 2 optional NTs,
            # and imagine that if both are omitted, then one algorithm applies,
            # but in any other case, another algorithm applies.
            # For the latter, you'd need at least two 'use' RHSs to cover the 3 possibilities.
            # So then a single 'def' RHS would match 2 'use' RHSs.
            # However, that's pretty unlikely, so I'll deal with it if it ever happens.)
            uis_for_di_ = defaultdict(list)
            for (u_i, d_i) in matches:
                uis_for_di_[d_i].append(u_i)
            for d_i in range(len(d_rhss)):
                d_rhs = d_rhss[d_i]
                uis = uis_for_di_[d_i]
                L = len(uis)
                if L in [0, 1]:
                    # fine
                    pass
                else:
                    # Likely a 'use' RHS has been pasted twice?
                    u_j_s = [u_i+1 for u_i in u_i_s]
                    msg_at_node(u_rhss[-1],
                        f"ERROR: RHS#{','.join(u_j_s)} all match def RHS#{d_i+1}"
                    )

        if not emu_grammar.puk_set:
            stderr(f"    no puk_set for {emu_grammar.source_text()}")

def u_rhs_matches_d_rhs_(u_rhs_n, d_rhs_n):
    notes = defaultdict(list)
    u_items = u_rhs_n._rhs_items
    d_items = d_rhs_n._rhs_items
    u_offset = 0

    for d_item_n in d_items:
        if u_offset < len(u_items):
            u_item_n = u_items[u_offset]
            note = u_item_matches_d_item(u_item_n, d_item_n)
            if note is not None:
                # good so far
                u_offset += 1
                for (key, val) in note.items(): notes[key].append(val)
                continue

        note = d_item_doesnt_require_a_matching_u_item(d_item_n)
        if note is not None:
            # Assume that the item was omitted from the u_rhs_n,
            # and see if we can get a match that way.
            for (key, val) in note.items(): notes[key].append(val)
            continue

        return False

    # We've exhausted the d_rhs_n.
    # In order to match, we need to have exhausted the u_rhs_n too.
    if u_offset != len(u_items):
        return False

    return notes

def u_item_matches_d_item(u_item_n, d_item_n):
    # Returns None if they do not match.
    # Otherwise, returns a dict containing notes about the comparison.

    if u_item_n.kind != d_item_n.kind:
        # 3058 occurrences
        return None

    # Now we know they have the same kind.

    k = u_item_n.kind

    note = {}

    if k == 'GNT':
        if u_item_n._nt_name != d_item_n._nt_name:
            # They can't possibly match.
            return None

        nt_name = u_item_n._nt_name

        note['L-670'] = 1
        # 2505 occurrences

        if d_item_n._is_optional:
            # In the definition, this GNT has a '?'.
            # So in the use, the GNT could have a '?' or not
            # (or the GNT could be absent entirely, but that's handled elsewhere).
            if u_item_n._is_optional:
                note['optional-GNT'] = (nt_name, 'either')
                note['L-678'] = 1
                # 149 occurrences
            else:
                note['optional-GNT'] = (nt_name, 'required')
                note['L-682'] = 1
                # 71 occurrences
        else:
            # In the definition, this GNT does not have a '?'
            # So in the use, it can't have a '?' either.
            if u_item_n._is_optional:
                msg_at_node(u_item_n,
                    f"ERROR: use has '?' but def does not"
                )
            note['L-687'] = 1
            # 2285 occurrences

        if d_item_n._params:
            # In the definition, this GNT has args.
            if u_item_n._params:
                # assert u_item_n._params == d_item_n._params
                if u_item_n._params != d_item_n._params:
                    msg_at_node(u_item_n.children[1],
                        f"ERROR: use says {u_item_n._params} but def says {d_item_n._params}"
                    )
                # XXX Shouldn't generate an error yet,
                # because the matching might fail later.
                # (But the assert was similarly problematic.)
                note['nt-args intact'] = nt_name
                note['L-695'] = 1
                # 23 occurrences
            else:
                note['nt-args suppressed'] = nt_name
                note['L-699'] = 1
                # 1884 occurrences
        else:
            # In the definition, this GNT has no args.
            # assert not u_item_n._params
            if u_item_n._params:
                msg_at_node(u_item_n.children[1],
                    f"ERROR: use has params where def has none"
                )
            # XXX Shouldn't generate an error yet, etc.
            note['L-703'] = 1
            # 598 occurrences

    else:

        if u_item_n.source_text() != d_item_n.source_text():
            return None

        note['L-711'] = 1
        # 2523 occurrences

        if k.startswith('LAC_') or k == 'NLTH':
            note['annotations intact'] = u_item_n

    return note

def d_item_doesnt_require_a_matching_u_item(d_item_n):
    if d_item_n.kind in ['PARAMS', 'LABEL', 'BUT_ONLY', 'LAC_SINGLE', 'LAC_SET', 'NLTH']:
        return {'annotations suppressed': d_item_n, 'L-900': 1}

    if d_item_n.kind == 'GNT' and d_item_n._is_optional:
        return {'optional-GNT': (d_item_n._nt_name, 'omitted'), 'L-903': 1}

    return None

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_order_of_RHSs_within_each_SDO_clause():
    stderr("check_order_of_RHSs_within_each_SDO_clause ...")

    for section in spec.root_section.each_descendant_that_is_a_section():
        if section.section_kind != 'syntax_directed_operation': continue

        prev_key = (-1, -1)

        for emu_grammar in section.each_descendant_named('emu-grammar'):
            # We only want <emu-grammar> elements that are directly contained by this section,
            # and not by a nested section.
            # HasCallInTailPosition is the only example, I think.
            if emu_grammar.closest_containing_section() is not section:
                continue

            # We only want <emu-grammar> elements that are the "syntax-directed" part of the SDO,
            # and not embedded within an emu-alg, e.g.:
            # "1. If |Statement| is <emu-grammar>Statement : LabelledStatement</emu-grammar> ..."
            if emu_grammar.nearest_ancestor_satisfying(lambda anc: anc.element_name == 'emu-alg'):
                continue

            for u_production_n in emu_grammar._gnode._productions:
                for u_rhs_n in u_production_n._rhss:
                    d_prodn_n = u_rhs_n.d_production_n
                    key = (d_prodn_n.doc_i, u_rhs_n.d_i)
                    if key < prev_key:
                        if key[0] == prev_key[0]:
                            msg = f"ORDER: This is {d_prodn_n._lhs_symbol}'s RHS #{u_rhs_n.d_i}, but we just handled RHS #{prev_key[1]}"
                        else:
                            msg = f"ORDER: This LHS is {d_prodn_n._lhs_symbol} (#{d_prodn_n.doc_i}), but we just handled LHS #{prev_key[0]}"
                        msg_at_node(u_rhs_n, msg)
                    # key == prev_key is okay.
                    # E.g., a defining RHS might have an optional nonterminal,
                    # and an SDO needs to handle presence/absence differently,
                    # so two 'use' productions will legitimately
                    # map to the same 'def' RHS.

                    prev_key = key

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_emu_prodrefs(doc_node):
    stderr("check_emu_prodrefs...")

    referenced_names = []

    for emu_prodref in doc_node.each_descendant_named('emu-prodref'):
        name = emu_prodref.attrs['name']

        assert name in info_for_nt_
        nt_info = info_for_nt_[name]
        assert 'A' in nt_info.def_occs

        if 'a' in emu_prodref.attrs:
            # This is a reference to a particular alternative (RHS)
            # of the named production.
            assert name in referenced_names
            continue

        if name in referenced_names:
            msg_at_node(emu_prodref, f"WARNING: duplicate emu-prodref for '{name}'")

        referenced_names.append(name)

    arena_A_names_with_posn = []

    for (nt_name, nt_info) in info_for_nt_.items():
        if 'A' in nt_info.def_occs:
            production_n = nt_info.def_occs['A']
            lhs_posn = production_n.children[0].start_posn
            arena_A_names_with_posn.append((lhs_posn, nt_name))

    arena_A_names_with_posn.sort()
    for (lhs_posn, nt_name) in arena_A_names_with_posn:
        if nt_name not in referenced_names:
            msg_at_posn(lhs_posn, f"ERROR: This production is not referenced in Annex A")

    if 0:
        # too many diffs?

        arena_A_names = [
            nt_name
            for (_, nt_name) in arena_A_names_with_posn
        ]

        stderr("comparing Annex A order to main-body order:")
        import difflib
        for line in difflib.context_diff(referenced_names, arena_A_names, lineterm=''):
            print(line, file=shared.g_errors_f)

# ------------------------------------------------------------------------------

def approximate_annex_A():
    stderr("approximate_annex_A...")

    lines = []
    def put(line=''):
        lines.append(line)

    # sections in the main body of the text that correspond to sections in Annex A:
    grouping_sections = []
    for section in spec.root_section.each_descendant_that_is_a_section():
        # caast = corresponding_annex_a_section_title
        mo = re.fullmatch(r'ECMAScript Language: (.+)', section.section_title)
        if mo:
            title_part = mo.group(1)

            if title_part == 'Source Text':
                # Annex A doesn't have a separate section corresponding to 10 "Source Code".
                # Instead, it slips its single production for SourceCharacter into "Lexical Grammar"
                caast = None

            elif title_part == 'Statements and Declarations':
                caast = 'Statements'

            else:
                caast = title_part

        elif section.section_title == 'Type Conversion':
            caast = 'Number Conversions'

        elif section.section_title == 'URI Syntax and Semantics':
            caast = 'Universal Resource Identifier Character Classes'

        elif section.section_title in ['Patterns', 'Syntax for Patterns']: # "Syntax for Patterns" is from #1651
            caast = 'Regular Expressions'
        
        else:
            caast = None
        if caast: grouping_sections.append((section, caast))


    put()
    put(f'<emu-annex id="sec-grammar-summary">')
    put(f'  <h1>Grammar Summary</h1>')

    for (grouping_section, aa_section_title) in grouping_sections:
        aa_section_id = 'sec-' + aa_section_title.lower().replace(' ', '-')
        put(f'# {aa_section_title} !start')
        put()
        put(f'  <emu-annex id="{aa_section_id}">')
        put(f'    <h1>{aa_section_title}</h1>')

        if aa_section_title == 'Lexical Grammar':
            lhs_symbol = 'SourceCharacter'
            put(f'    <emu-prodref name="{lhs_symbol}"></emu-prodref>')

        for section in grouping_section.each_descendant_that_is_a_section():
            syntaxes = [
                numless
                for numless in section.numless_children
                if (
                    numless.title in ['Syntax', 'Supplemental Syntax']
                    or
                    grouping_section.section_title == 'Syntax for Patterns'
                )
            ]
            if not syntaxes: continue

            put(f'# {section.section_title} !start')
            for syntax in syntaxes:
                put(f'# {section.section_title} / {syntax.title} !start')

                for bc in syntax.block_children:
                    if bc.element_name == 'emu-grammar':
                        prodns = bc._gnode
                        assert prodns.kind == 'BLOCK_PRODUCTIONS'
                        for prodn in prodns.children:
                            assert prodn.kind == 'MULTILINE_PRODUCTION'
                            (gnt, _, _) = prodn.children
                            assert gnt.kind == 'GNT'
                            (nt, _, _) = gnt.children
                            assert nt.kind == 'NT'
                            lhs_symbol = nt.source_text()
                            put(f'    <emu-prodref name="{lhs_symbol}"></emu-prodref>')

                        if syntax.title == 'Supplemental Syntax':
                            put(f'    <p>&nbsp;</p>')

                    elif bc.element_name  == 'p':

                        if syntax.title == 'Supplemental Syntax':
                            ptext = bc.source_text()

                            ptext = re.sub(r'<emu-grammar>(\w+).+?</emu-grammar>', r'<emu-prodref name="\1"></emu-prodref>', ptext)

                            for (nt, a) in [
                                ('PrimaryExpression',    'parencover'),
                                ('CallExpression',       'callcover'),
                                ('AssignmentExpression', 'assignment'),
                                ('ArrowParameters',      'parencover'),
                                ('AsyncArrowFunction',   'callcover'),
                            ]:
                                ptext = ptext.replace(f'name="{nt}">', f'name="{nt}" a="{a}">')

                            ptext = re.sub(r'\n +', r'\n      ', ptext)

                            put(f'    {ptext}')

                        elif section.section_title == 'ToNumber Applied to the String Type':
                            ptext = bc.source_text()
                            ptext = re.sub(
                                r'(All grammar symbols not explicitly defined) above (have the definitions used in the) (Lexical Grammar for numeric literals) \((<.+>)(<.+>)\)',
                                r'\1 by the |StringNumericLiteral| grammar \2 \4\3\5.',
                                ptext)
                            put(f'    {ptext}')

                        elif section.section_title == 'Patterns':
                            ptext = bc.source_text()
                            put(f'    {ptext}')
                            put(f'    <p>&nbsp;</p>')
                            
                    elif bc.element_name  == 'emu-note':
                        pass

                    else:
                        assert 0

                put(f'# {section.section_title} / {syntax.title} !end')

            put(f'# {section.section_title} !end')

        put('  </emu-annex>')
        put(f'# {aa_section_title} !end')

    put('</emu-annex>')
    put()

    # -----------------------------------------------------------------
    # In Annex A, various things are out of order wrt the main text,
    # so we need to move chunks of lines around.

    def move(X, before, after):
        def find(substring):
            matching_indexes = [
                i
                for (i, line) in enumerate(lines)
                if substring in line
            ]
            if len(matching_indexes) != 1:
                stderr(f"find({substring!r}) has {len(matching_indexes)} matches:")
                for i in matching_indexes:
                    stderr(f"    {lines[i]}")
                sys.exit(1)
            return matching_indexes[0]

        X_start_i = find(f"# {X} !start")
        X_end_i   = find(f"# {X} !end")
        assert X_start_i < X_end_i
        X_lines = lines[X_start_i:X_end_i+1]
        del lines[X_start_i:X_end_i+1]

        before_i = find(before)
        after_i  = find(after)
        if before_i + 1 != after_i:
            stderr()
            stderr("move-to point is ill-defined, because `before` and `after` are not adjacent:")
            stderr(f"{before} matches:")
            stderr(f"  {before_i:2d}: {lines[before_i]}")
            stderr(f"{after} matches:")
            stderr(f"  {after_i:2d}: {lines[after_i]}")
            sys.exit(1)
        lines[after_i:after_i] = X_lines

    move('Number Conversions',
        # to between:
        '# Scripts and Modules !end',
        '# Universal Resource Identifier Character Classes !start',
    )

    move('Left-Hand-Side Expressions / Supplemental Syntax',
        # to between:
        'name="CallExpression">',
        'SuperCall'
    )

    move('Async Arrow Function Definitions',
        # to between:
        '# Arrow Function Definitions !end',
        '# Method Definitions !start'
    )

    move('Async Function Definitions',
        # to between:
        '# Async Generator Function Definitions !end',
        '# Class Definitions !start'
    )

    # ------------------------------------------------------------------

    aaa_f = shared.open_for_output('approximate_annex_a')
    for line in lines:
        if line.startswith('#'): continue
        print(line, file=aaa_f)
    aaa_f.close()

# ------------------------------------------------------------------------------

def check_nonterminal_refs(doc_node):
    # Check references to nonterminals outside of <emu-grammar> elements
    stderr("check_nonterminal_refs...")

    # kludge:
    B_start = shared.spec_text.find('namespace="annexB"')

    # TODO: Simply scanning through the whole of shared.spec_text
    # will find matches in some <code class="javascript">,
    # where we don't want it to.
    for mo in re.finditer(r'\|\w[^|]+\|', shared.spec_text):
        posn = mo.start()
        ref = mo.group(0)
        mo2 = re.fullmatch(r'\|(\w+)(?:\[(.+?)\])?(\?)?\|', ref)
        if mo2 is None:
            msg_at_posn(posn, "ERROR: malformed nonterminal-reference")
            continue
        (nt, args, maybe_opt) = mo2.groups()
        if nt not in info_for_nt_:
            msg_at_posn(posn, "ERROR: unrecognized nonterminal: %s" % nt)
            continue

        nt_info = info_for_nt_[nt]

        # Check that args (if any) are compatible with nt's definition.
        if args:
            param_names_in_args = []
            for arg in re.split(', *', args):
                c = arg[0]
                if c not in ['?', '+', '~']:
                    msg_at_posn(posn,
                        "WARNING: nonterminal-ref has arg '%s', with no ?+~ prefix" % arg
                    )
                    # Actually, this is okay if it's referring to
                    # an occurrence in the LHS of a use production.
                    # But it's worth calling out for checking.
                    param_name = arg
                else:
                    param_name = arg[1:]
                param_names_in_args.append(param_name)

            arena = 'A' if posn < B_start else 'B' # kludge
            def_production_n = nt_info.get_appropriate_def_occ(arena)
            def_prodn_params = def_production_n._param_names

            if param_names_in_args != def_prodn_params:
                msg_at_posn(posn,
                    "ERROR: nonterminal-ref has args '%s', but nonterminal's definition has params '%s'" %
                    (args, ', '.join(def_prodn_params))
                )

        # XXX: Should check that maybe_opt is compatible with nt's use.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def make_grammars():
    spec.grammar_ = {}
    for level in ['lexical', 'syntactic']:
        for arena in ['A', 'B']:
            spec.grammar_[(level,arena)] = Grammar(level, arena)

    for (lhs_symbol, nt_info) in sorted(info_for_nt_.items()):

        # From a parsing point of view, there's really just two grammars,
        # each with multiple goal symbols.
        grammar_level = 'syntactic' if nt_info.num_colons == 1 else 'lexical'

        # See Bug 4088: https://tc39.github.io/archives/bugzilla/4088/
        if grammar_level == 'lexical' and lhs_symbol in [
            'ReservedWord',
            'NullLiteral',
            'BooleanLiteral',
        ]:
            stderr('    Changing from lexical to syntactic:', lhs_symbol)
            grammar_level = 'syntactic'

        for arena in ['A', 'B']:
            production_n = nt_info.get_appropriate_def_occ(arena)
            if production_n is None: continue

            spec.grammar_[(grammar_level, arena)].add_prodn(production_n)

def do_grammar_left_right_stuff():
    grammar_lr_f = shared.open_for_output('grammar_lr')
    def put(*args):
        print(*args, file=grammar_lr_f)

    for (_, g) in sorted(spec.grammar_.items()):
        g.do_left_right_stuff(put)

# ------------------------------------------------------------------------------

class Grammar:
    def __init__(this_grammar, level, arena):
        this_grammar.level = level
        this_grammar.arena = arena
        this_grammar.name = level + arena
        this_grammar.prodn_for_lhs_ = {}

    # --------------------------------------------------------------------------

    def add_prodn(this_grammar, production_n):
        lhs_symbol = production_n._lhs_symbol
        assert lhs_symbol not in this_grammar.prodn_for_lhs_, lhs_symbol
        this_grammar.prodn_for_lhs_[lhs_symbol] = production_n

    # --------------------------------------------------------------------------

    def get_name_kind(this_grammar, name):
        if name in this_grammar.prodn_for_lhs_:
            return 'NT'
        else:
            return 'T_named'

    # --------------------------------------------------------------------------

    def do_left_right_stuff(this_grammar, put):
        put()
        put(this_grammar.name)
        lhs_symbols = set()
        rhs_symbols = set()
        for (lhs_symbol, production_n) in sorted(this_grammar.prodn_for_lhs_.items()):
            lhs_symbols.add(lhs_symbol)
            for rhs_n in production_n._rhss:
                def visit(n):
                    if n.kind == 'GNT':
                        rhs_symbols.add(n._nt_name)
                        return 'prune'
                    elif n.kind == 'NT':
                        rhs_symbols.add(n._nt_name)
                rhs_n.preorder_traversal(visit)

        lhs_not_rhs = lhs_symbols - rhs_symbols
        this_grammar.goal_symbols = sorted(list(lhs_not_rhs))
        put('named symbols that appear on LHS but not RHS:')
        for symbol in this_grammar.goal_symbols:
            put('    ', symbol)
        # kludge:
        if this_grammar.name == 'syntactic':
            this_grammar.goal_symbols.insert(0, 'ArrowFormalParameters')
            # because, while it does appear on a RHS (for AsyncArrowHead),
            # it's still a goal symbol (re CoverParenthesizedExpressionAndArrowParameterList)

        rhs_not_lhs = rhs_symbols - lhs_symbols
        this_grammar.named_terminals = sorted(list(rhs_not_lhs))
        put('named symbols that appear on RHS but not LHS:')
        for symbol in this_grammar.named_terminals:
            put('    ', symbol)

        for (lhs_symbol, production_n) in sorted(this_grammar.prodn_for_lhs_.items()):
            for rhs_n in production_n._rhss:
                def visit(n):
                    if n.kind == 'GNT' and n._nt_name in this_grammar.named_terminals:
                        pass
                        #XXX change n from a 'GNT' node to a 'named terminal' node?
                rhs_n.preorder_traversal(visit)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def split_indentation(line):
    # Returns a tuple (i,r)
    # where i is the amount of indentation (an integer),
    # and r is the rest of the line
    mo = re.match(r'^( *)(.+)', line)
    return (len(mo.group(1)), mo.group(2))

def trim_newlines(subject):
    r = subject
    r = re.sub(r'^\n+', '', r)
    r = re.sub(r'\n+\s*$', '', r)
    return r

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

if __name__ == '__main__':
    shared.register_output_dir('_test')
    g = Grammar('test')
    g.exp_prodns = OrderedDict()
    g.exp_prodns['S'] = [
        [SNT('E'), T_named('EOI')],
    ]
    g.exp_prodns['E'] = [
        [SNT('A'), T_named('a')],
        [SNT('B'), T_named('b')]
    ]
    g.exp_prodns['A'] = [
        [SNT('A'), SNT('C')],
        [SNT('C')]
    ]
    g.exp_prodns['B'] = [
        [SNT('B'), SNT('C')],
        [SNT('C')]
    ]
    g.exp_prodns['C'] = [
        [T_named('c')]
    ]
    g.start_symbol = SNT('S')
    g.eoi_symbol = T_named('EOI')
    g.generate_LR0_automaton()

# vim: sw=4 ts=4 expandtab
