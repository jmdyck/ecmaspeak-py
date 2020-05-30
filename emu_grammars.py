#!/usr/bin/python3

# ecmaspeak-py/emu_grammars.py:
# Analyze <emu-grammar> elements.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import atexit, subprocess, re, time, sys, pdb
from collections import namedtuple, defaultdict, OrderedDict

import DFA
import shared
from shared import stderr, header, msg_at_node, msg_at_posn, spec, SpecNode

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
        t = emu_grammar.attrs.get('type', 'reference')
        emu_grammars_of_type_[t].append(emu_grammar)

    stderr('<emu-grammar> counts:')
    for (t, emu_grammars) in sorted(emu_grammars_of_type_.items()):
        stderr('    ', len(emu_grammars), t)

    process_defining_emu_grammars(emu_grammars_of_type_['definition'])
    check_reachability() # not that useful?

    check_non_defining_prodns(emu_grammars_of_type_['reference'])

    check_emu_prodrefs(spec.doc_node)
    approximate_annex_A(spec.doc_node)

    check_nonterminal_refs(spec.doc_node)

    make_grammars()
    do_grammar_left_right_stuff()
    # return #XXX
    generate_es_parsers()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_grammar(emu_grammar):
    assert emu_grammar.element_name == 'emu-grammar'

    if '\n' in emu_grammar.source_text():
        # one or more productions, indented wrt the <emu-grammar> tag, separated by blank line.
        goal = 'EMU_GRAMMAR_CONTENT_2'
        line_start_posn = 1 + shared.spec_text.rfind('\n', 0, emu_grammar.start_posn)
        emu_grammar_indent = emu_grammar.start_posn - line_start_posn
        assert emu_grammar_indent in [2, 4, 6, 8]

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

        production_n._rhss = rhss

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

    'MULTILINE_PRODUCTION' : ('_', 'n', 'NLAI', 'GNT', ' ', 'COLONS', 'MULTILINE_R'),
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
    'LAC_SET'              : ('_', 'n', r'\[lookahead &lt;! ', 'LAC_SET_OPERAND', r'\]'),
    'LAC_SET_OPERAND'      : ('|', '^', 'NT', 'SET_OF_TERMINAL_SEQ'),
    'SET_OF_TERMINAL_SEQ'  : ('+', 'n', 'TERMINAL_SEQ', ', ', '{', '}'),
    'TERMINAL_SEQ'         : ('+', 'n', 'TERMINAL_ITEM', ' '),
    'TERMINAL_ITEM'        : ('|', '^', 'BACKTICKED_THING', 'NAMED_CHAR', 'NLTH_BAR'),

    'BUT_ONLY'             : ('/', 'n', r'\[> but only if ([^][]+)\]'),

    'INDENT'           : ('/', ' ', ''),
    'OUTDENT'          : ('/', ' ', ''),
    'EOI'              : ('/', ' ', ''),
    'NLAI'             : ('/', ' ', r'\n +'),

    'COLONS'           : ('/', 'n', r':+'),
    'PARAM'            : ('/', 'n', r'([~+?]?)([A-Z][a-z]*)'),
    'NT'               : ('/', 'n', r'[A-Z]\w*|uri\w*|@'),
    'LABEL'            : ('/', 'n', r'#\w+'),
    'EMPTY'            : ('/', 'n', r'\[empty\]'),
    'NLTH'             : ('/', 'n', r'\[no LineTerminator here\]'),
    'NLTH_BAR'         : ('/', 'n', r'\[no \|LineTerminator\| here\]'),
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
                    # optional thing has been omitted
                    if rkind == 'n':
                        result = GNode(at_start_posn, at_start_posn, goal, [])
                    elif rkind == '^':
                        result = GNode(at_start_posn, at_start_posn, 'OMITTED_OPTIONAL', [])
                    else:
                        assert 0, rkind
                    return (posn, indent, result)
                (posn, indent, child) = r
                if child: children.append(child)
            # optional thing is there
            if rkind == 'n':
                result = GNode(at_start_posn, posn, goal, children)
            elif rkind == '^':
                assert len(children) == 1
                [result] = children
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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

info_for_nt_ = None

def process_defining_emu_grammars(emu_grammars):
    stderr('process_defining_emu_grammars...')
    header("checking grammar (i.e., defining prodns)...")

    global info_for_nt_
    grammar_f = shared.open_for_output('def_prodns')
    info_for_nt_ = defaultdict(NonterminalInfo)

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

# ------------------------------------------------------------------------------

def check_non_defining_prodns(emu_grammars):
    stderr("check_non_defining_prodns...")
    header("checking non-defining productions...")

    for emu_grammar in emu_grammars:
        emu_grammar.summary = []

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
                    elif u_rhs_item_n.kind in ['LAC_SINGLE', 'LAC_SET', 'NLTH']:
                        annotations.append(u_rhs_item_n)
                    else:
                        assert 0, u_rhs_item_n.kind

                for annotation_n in annotations:
                    if cc_section.section_title == 'Rules of Automatic Semicolon Insertion' and annotation_n.kind == 'NLTH':
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

                    emu_grammar.summary.append((lhs_nt, d_i, notes['optional-GNT']))

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
                elif L == 1:
                    # good
                    pass
                else:
                    msg_at_node(u_rhs,
                        f"WARNING: This RHS matches {L} defining RHSs for {lhs_nt} [but probably resolved by guards]"
                    )

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
                    f"ERROR: 'use' RHSs are out-of-order wrt corresponding def RHSs: {[i+1 for i in all_def_i_s]}"
                )

            # Each 'def' RHS should match at most one 'use' RHS.
            # (Actually, it's conceivable that this could happen without being a mistake.
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

        if emu_grammar.summary == []:
            stderr(f"    no summary for {emu_grammar.source_text()}")

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
            assert not u_item_n._is_optional
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

#    if (
#        t == A_but_only_if
#        and
#        d_item_n.c == "the integer value of DecimalEscape is 0"
#        and
#        u_item_n.c == "&hellip;"
#    ):
#        return 'ellipsify condition in but_only_if'
#
#    if (
#        t == A_but_only_if
#        and
#        d_item_n.c == "the integer value of |DecimalEscape| is 0"
#        and
#        u_item_n.c == "&hellip;"
#    ):
#        return 'ellipsify condition in but_only_if'

def d_item_doesnt_require_a_matching_u_item(d_item_n):
    if d_item_n.kind in ['PARAMS', 'LABEL', 'BUT_ONLY', 'LAC_SINGLE', 'LAC_SET', 'NLTH']:
        return {'annotations suppressed': d_item_n, 'L-900': 1}

    if d_item_n.kind == 'GNT' and d_item_n._is_optional:
        return {'optional-GNT': (d_item_n._nt_name, 'omitted'), 'L-903': 1}

    return None

# ------------------------------------------------------------------------------

def check_emu_prodrefs(doc_node):
    stderr("check_emu_prodrefs...")
    header("checking emu-prodref elements...")

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
            msg_at_posn(emu_prodref.start_posn, f"WARNING: duplicate emu-prodref for '{name}'")

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

        header("comparing Annex A order to main-body order:")
        import difflib
        for line in difflib.context_diff(referenced_names, arena_A_names, lineterm=''):
            print(line, file=shared.g_errors_f)

# ------------------------------------------------------------------------------

def approximate_annex_A(doc_node):

    lines = []
    def put(line=''):
        lines.append(line)

    # sections in the main body of the text that correspond to sections in Annex A:
    grouping_sections = []
    for section in doc_node.each_descendant_that_is_a_section():
        # caast = corresponding_annex_a_section_title
        mo = re.fullmatch(r'ECMAScript Language: (.+)', section.section_title)
        if mo:
            caast = mo.group(1)

            if caast == 'Source Code':
                # Annex A doesn't have a separate section corresponding to 10 "Source Code".
                # Instead, it slips its single production into "Lexical Grammar"
                caast = None
                source_code_section = section

            elif caast == 'Statements and Declarations':
                caast = 'Statements'

        elif section.section_title == 'ToNumber Applied to the String Type':
            caast = 'Number Conversions'

        elif section.section_title == 'URI Syntax and Semantics':
            caast = 'Universal Resource Identifier Character Classes'

        elif section.section_title in ['Patterns', 'Syntax for Patterns']:
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
    stderr("check_nonterminal_refs...")
    header("checking references to nonterminals (outside of emu-grammar)...")

    # kludge:
    B_start = shared.spec_text.find('namespace="annexB"')

    for mo in re.finditer('\|(\w+?)(?:\[(.*?)\])?(_opt)?\|', shared.spec_text):
        (nt, args, maybe_opt) = mo.groups()
        posn = mo.start()
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

        # XXX: Should check that _opt is compatible with nt's use.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

grammar_ = None

def make_grammars():
    global grammar_
    grammar_ = {}
    for level in ['lexical', 'syntactic']:
        for arena in ['A', 'B']:
            grammar_[(level,arena)] = Grammar(level, arena)

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

            grammar_[(grammar_level, arena)].add_prodn(production_n)

def do_grammar_left_right_stuff():
    grammar_lr_f = shared.open_for_output('grammar_lr')
    def put(*args):
        print(*args, file=grammar_lr_f)

    for (_, g) in sorted(grammar_.items()):
        g.do_left_right_stuff(put)

# ------------------------------------------------------------------------------

def generate_es_parsers():
    stderr("generate_es_parsers...")

    for (_, g) in sorted(grammar_.items()):
        # stderr()
        # stderr('---------------------------')
        stderr(f"    {g.name}")

        g.generate_parser()

    stderr()
    stderr('---------------------------')

# ------------------------------------------------------------------------------

# from emu_grammar_tokens import *  # e.g. T_lit, LAX, A_guard
# terminal_types = [T_lit, T_nc, T_u_p, T_named ]

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

    # ==========================================================================

    def generate_parser(this_grammar):
        if this_grammar.level == 'lexical':
            this_grammar.explode_multichar_literals()
            # this_grammar.distinguish_Token_from_NonToken()

        this_grammar.save_as_json()

        if 0:
            # An LR approach, which bogged down
            # when I tried to handle lookahead-restrictions:
            this_grammar.expand_abbreviations()
            this_grammar.print_exp_prodns()
            this_grammar.calc_min_length()
            this_grammar.compute_firstk()

            # Have to exclude lexicalB because it's incomplete.
            # (It doesn't 'duplicate' all prodns that must have 'N' added as grammatical param.)
            if this_grammar.name != 'lexicalB':
                this_grammar.generate_LR0_automaton()

    def explode_multichar_literals(this_grammar):
        # mcl = "multicharacter literal",
        #
        #" A <em>lexical grammar</em> for ECMAScript ...
        #" has as its terminal symbols Unicode code points ...
        #
        # So, in the lexical grammar, we explode multicharacter literals.

        def is_mcl(rhs_item_n):
            return rhs_item_n.kind == 'BACKTICKED_THING' and len(rhs_item_n._chars)>1

        for (lhs_symbol, production_n) in sorted(this_grammar.prodn_for_lhs_.items()):
            for rhs_n in production_n._rhss:
                if any(is_mcl(rhs_item_n) for rhs_item_n in rhs_n._rhs_items):
                    # stderr(f"exploding things in {rhs_n}")
                    new_rhs_items = []
                    for rhs_item_n in rhs_n._rhs_items:
                        if is_mcl(rhs_item_n):
                            for char in rhs_item_n._chars:
                                #XXX kludgey
                                new_node = GNode(0, 0, 'BACKTICKED_THING', [])
                                new_node._chars = char
                                new_rhs_items.append(new_node)
                        else:
                            new_rhs_items.append(rhs_item_n)
                    rhs_n._rhs_items = new_rhs_items

    # ==========================================================================

    def distinguish_Token_from_NonToken(this_grammar):
        assert this_grammar.level == 'lexical'

        non_token_names = ['WhiteSpace','LineTerminator', 'Comment']
        non_token_rhss = [
            [GNT(non_token_name, (), False)]
            for non_token_name in non_token_names
        ]

        for (lhs_symbol, production_n) in sorted(this_grammar.prodn_for_lhs_.items()):
            if lhs_symbol.startswith('InputElement'):
                ie_rest = lhs_symbol.replace('InputElement', '')
                # print(lhs_symbol)
                # print(production_n._param_names)
                # print(production_n._rhss)
                assert len(production_n._rhss) == 6
                assert production_n._rhss[0:3] == non_token_rhss
                # del production_n._rhss[0:3]

                this_grammar.prodn_for_lhs_['_Token' + ie_rest] = (
                    production_n._param_names, production_n._rhss[3:]) #!
                del this_grammar.prodn_for_lhs_[lhs_symbol] 

        this_grammar.prodn_for_lhs_['_NonToken'] = (0, [], non_token_rhss) #!

    # ==========================================================================

    def save_as_json(this_grammar):
        filename = '%s_cfps.json' % this_grammar.name
        f = shared.open_for_output(filename)
        def put(*args): print(*args, file=f)

        def to_json(x):
            if x is None:
                return 'null'
            elif type(x) == bool:
                return 'true' if x else 'false'
            elif type(x) == str:
                return (
                    '"'
                    + x.replace('\\', '\\\\').replace('"', '\\"')
                    + '"'
                )
            elif type(x) in [list,tuple]:
                return '[' + ', '.join(to_json(e) for e in x) + ']'
            elif hasattr(x, 'items'):
                return (
                '{'
                + ', '.join(
                    '"%s": %s' % (name, to_json(value))
                    for (name, value) in x.items()
                    )
                + '}'
                )
            else:
                assert 0, x

        def convert_lac(lac_n):
            if lac_n.kind == 'LAC_SINGLE':
                [lac_single_op, terminal_seq_n] = lac_n.children
                T = {
                    '==': 'LAI',
                    '!=': 'LAX',
                }[lac_single_op.source_text()]
                return {'T': T, 'ts': [convert_terminal_seq_n(terminal_seq_n)]}

            elif lac_n.kind == 'LAC_SET':
                [lac_set_operand_n] = lac_n.children
                if lac_set_operand_n.kind == 'NT':
                    ts = [{'T': 'GNT', 'n': lac_set_operand_n.source_text(), 'a': [], 'o': False}]
                elif lac_set_operand_n.kind == 'SET_OF_TERMINAL_SEQ':
                    ts = []
                    for terminal_seq_n in lac_set_operand_n.children:
                        ts.append(convert_terminal_seq_n(terminal_seq_n))
                else:
                    assert 0
                return {'T': 'LAX', 'ts': ts}
            else:
                assert 0

        def convert_terminal_seq_n(terminal_seq_n):
            ts = []
            for terminal_item_n in terminal_seq_n.children:
                if terminal_item_n.kind == 'BACKTICKED_THING':
                    t = {'T': 'T_lit', 'c': terminal_item_n._chars}
                elif terminal_item_n.kind == 'NAMED_CHAR':
                    t = {'T': 'T_nc', 'n': terminal_item_n.source_text()[4:-4]}
                elif terminal_item_n.kind == 'NLTH_BAR':
                    t = {'T': 'A_no_LT'}
                else:
                    t = str(terminal_item_n)
                ts.append(t)
            return ts

        # These are symbols that appear in both the syntactic and lexical grammars.
        # In the lexical, they're nonterminals, but in the syntactic, they're terminals.
        # (So the 'nt' in 'bilevel_nt_names' is a misnomer,
        # but the metagrammar identifies them as non-terminals anyway...)
        # XXX This should be deduced rather than hardcoded.
        bilevel_nt_names = [
            'IdentifierName',
            'NumericLiteral',
            'StringLiteral',
            'RegularExpressionLiteral',
            'TemplateHead',
            'NoSubstitutionTemplate',
            'TemplateMiddle',
            'TemplateTail'
        ]

        def convert_nt(nt_n):
            nt_name = nt_n._nt_name
            if nt_n.kind == 'GNT':
                args = nt_n._params
                is_optional = nt_n._is_optional
            elif nt_n.kind == 'NT':
                args = []
                is_optional = False
            else:
                assert 0
            #
            if this_grammar.level == 'syntactic' and nt_name in bilevel_nt_names:
                assert args == []
                assert is_optional == False
                return {'T': 'T_named', 'n': nt_name}
            else:
                a = [
                    {'T': 'Arg', 's': sign, 'n': name}
                    for (sign, name) in args
                ]
                return {'T': 'GNT', 'n': nt_name, 'a': a, 'o': is_optional}

        #XXX This code is just an interim mess that mostly reproduces what the former code did.

        # all_params = set()
        # all_types = set()
        put('[')
        n_rhss = 0
        for (lhs_symbol, production_n) in sorted(this_grammar.prodn_for_lhs_.items()):

            # for param in production_n._param_names: all_params.add(param)

            for rhs_n in production_n._rhss:
                n_rhss += 1
                if n_rhss > 1: put(',')
                put('{')
                put('  "n": %d,' % n_rhss)
                put('  "lhs": "%s",' % lhs_symbol)
                put('  "params": [%s],' % ','.join('"%s"' % param for param in production_n._param_names))
                if rhs_n._rhs_items and rhs_n._rhs_items[0].kind == 'PARAMS':
                    p0 = rhs_n._rhs_items[0].children[0]
                    put('  "guard": {"s":"%s", "n":"%s"},' % p0.groups)
                else:
                    put('  "guard": null,')

                saved_pre = None
                runit = None
                runits = []
                for (r,rhs_item_n) in enumerate(rhs_n._rhs_items):
                    K = rhs_item_n.kind
                    # all_types.add(rhs_item_n.T)

                    if K == 'PARAMS':
                        assert r == 0
                        # already handled above
                    elif K == 'LABEL':
                        assert r == len(rhs_n._rhs_items) - 1
                        # doesn't contribute to parser

                    # Things that attach to the following symbol:
                    elif (
                        (K.startswith('LAC_') and r < len(rhs_n._rhs_items) - 1)
                    ):
                        assert saved_pre is None
                        saved_pre = convert_lac(rhs_item_n)

                    # Things that attach to the preceding symbol:
                    elif (
                        K in ['BUT_ONLY', 'NLTH']
                        or
                        (K.startswith('LAC_') and r == len(rhs_n._rhs_items) - 1)
                    ):
                        if K == 'NLTH':
                            post = {'T': 'A_no_LT'}
                        elif K == 'BUT_ONLY':
                            post = {'T': 'A_but_only_if', 'c': decode_entities(rhs_item_n.groups[0])}
                        elif K.startswith('LAC_'):
                            post = convert_lac(rhs_item_n)
                        else:
                            post = str(rhs_item_n)

                        assert runit is not None
                        assert runit['post'] is None
                        runit['post'] = post

                    elif K == 'NT_BUT_NOT':
                        (nt_n, exclusion_n) = rhs_item_n.children

                        b = []
                        for excludable_n in exclusion_n._excludables:
                            if excludable_n.kind == 'NT':
                                ex_symbol = convert_nt(excludable_n)
                            elif excludable_n.kind == 'BACKTICKED_THING':
                                ex_symbol = {'T': 'T_lit', 'c': excludable_n._chars}
                            else:
                                assert 0
                            b.append(ex_symbol)
                        post = {'T': 'A_but_not', 'b': b}

                        runit = OrderedDict(
                            [('pre', None), ('rsymbol', convert_nt(nt_n)), ('post', post)]
                        )
                        runits.append(runit)

                    else:
                        if K == 'GNT':
                            rsymbol = convert_nt(rhs_item_n)
                        elif K == 'BACKTICKED_THING':
                            rsymbol = {'T': 'T_lit', 'c': rhs_item_n._chars}
                        elif K == 'NAMED_CHAR':
                            rsymbol = {'T': 'T_nc', 'n': rhs_item_n.source_text()[4:-4]}
                        elif K == 'U_ANY':
                            rsymbol = {'T': 'T_u_p', 'p': None}
                        elif K == 'U_PROP':
                            rsymbol = {'T': 'T_u_p', 'p': rhs_item_n.groups[0]}
                        elif K == 'U_RANGE':
                            rsymbol = {'T': 'T_u_r', 'rlo': rhs_item_n.groups[0], 'rhi': rhs_item_n.groups[1]}
                        else:
                            assert 0, K

                        runit = OrderedDict(
                            [('pre', saved_pre), ('rsymbol', rsymbol), ('post', None)]
                        )
                        runits.append(runit)
                        saved_pre = None

                if saved_pre:
                    runits.append(saved_pre)

                put('  "rhs": [')
                prefix = '      '
                for runit in runits:
                    put(prefix + to_json(runit))
                    prefix = '    , '
                put('  ]')

                put('}')
        put(']')

        # print('params:', sorted(list(all_params)))
        # print('types:', sorted(list(all_types)))

    # ==========================================================================

    #XXX From here down, the code has not been updated to the new GNode representation.

    def expand_abbreviations(this_grammar):
        # Expand productions with respect to optionals and parameters.
        # (Expanding wrt parameters eliminates A_guard items.
        # Also eliminate A_id items, as they don't contribute.)
        # Generally, convert the grammar to something closer to a CFG.

        stderr('    expand_abbreviations ...')

        # Put the expanded set of productions here:
        this_grammar.exp_prodns = OrderedDict()

        this_grammar.start_symbol = SNT('START')
        this_grammar.eoi_symbol = T_named('EOI')
        for goal_symbol in this_grammar.goal_symbols:
            # kludge:
            if goal_symbol == 'Pattern':
                goal_symbols = ['Pattern~U~N', 'Pattern~U+N', 'Pattern+U+N']

            elif goal_symbol in [
                'ArrowFormalParameters',
                'AssignmentPattern',
                'ParenthesizedExpression',
                'CallMemberExpression',
            ]:
                goal_symbols = [
                    goal_symbol + '~Yield~Await',
                    goal_symbol + '~Yield+Await',
                    goal_symbol + '+Yield~Await',
                    goal_symbol + '+Yield+Await',
                ]

            else:
                goal_symbols = [goal_symbol]

            # When there are multiple possible goal symbols,
            # we could generate a separate parser for each,
            # but that would be inefficient in time+space+attention,
            # because they'd be largely identical.
            # So instead, for each goal_symbol G,
            # we augment the grammar with a production of the form:
            #     START -> prep_for_G  G  EOI
            # where prep_for_G is an ad hoc terminal that we'll feed to the parser
            # to indicate which goal_symbol we're interested in.
            for goal_symbol in goal_symbols:
                prep_symbol = T_named('prep_for_' + goal_symbol)
                this_grammar.add_exp_prod1(
                    this_grammar.start_symbol.n,
                    [prep_symbol, SNT(goal_symbol), this_grammar.eoi_symbol]
                )

        for (lhs_symbol, production_n) in sorted(this_grammar.prodn_for_lhs_.items()):
            if 0:
                print()
                print('    ', lhs_symbol, production_n._param_names)
                for rhs_n in production_n._rhss:
                    print('        ', rhs_n)

            for params_setting in each_params_setting(production_n._param_names):
                exp_lhs_symbol = lhs_symbol + ''.join(params_setting)
                for rhs_n in production_n._rhss:

                    if rhs_n:
                        rthing0 = rhs_n[0]
                        if type(rthing0) == A_guard:
                            if (rthing0.s + rthing0.n) in params_setting:
                                # The guard succeeds (in the current `params_setting`).
                                pass
                            else:
                                # The guard fails.
                                continue # to next rhs_n

                    # count the number of optionals in this rhs_n
                    n_optionals = len([
                        rhs_item_n
                        for rhs_item_n in rhs_n._rhs_items
                        if type(rhs_item_n) == GNT and rhs_item_n._is_optional
                    ])

                    # Generate a different rhs_n for each combo of optionals
                    for include_optional_ in each_boolean_vector_of_length(n_optionals):

                        opt_i = 0
                        exp_rhs = []

                        for (i,rhs_item_n) in enumerate(rhs_n._rhs_items):
                            if type(rhs_item_n) == A_guard:
                                assert i == 0
                                # We've already determined that this guard succeeds.
                                continue # to next rhs_item_n
                            elif type(rhs_item_n) == A_id:
                                assert i == len(rhs_n)-1
                                continue

                            elif type(rhs_item_n) in [A_but_only_if, A_but_not, A_no_LT]:
                                exp_rthing = rhs_item_n

                            elif type(rhs_item_n) in [LAX, LAI]:
                                if type(rhs_item_n.ts) in [tuple, list]:
                                    ts = rhs_item_n.ts
                                else:
                                    ts = [rhs_item_n.ts]

                                terminal_sequences = []
                                for t in ts:
                                    if type(t) == T_lit:
                                        terminal_sequences.append(map(c_to_terminal, t.c.split(' ')))
                                    elif type(t) == GNT:
                                        terminal_sequences.extend([]) # XXX
                                    elif type(t) == T_nc:
                                        pass # XXX
                                    else:
                                        assert 0, t
                                exp_rthing = rhs_item_n # XXX something(terminal_sequences)

                            elif type(rhs_item_n) in terminal_types:
                                exp_rthing = rhs_item_n

                            elif type(rhs_item_n) == GNT:
                                exp_rthing = SNT(expand_nt_wrt_params_setting(rhs_item_n, params_setting))
                                if rhs_item_n._is_optional:
                                    include_this_optional = include_optional_[opt_i]
                                    opt_i += 1
                                    if include_this_optional:
                                        pass
                                    else:
                                        # omit the optional
                                        continue # to next rhs_item_n

                            else:
                                assert 0, rhs_item_n

                            exp_rhs.append(exp_rthing)

                        this_grammar.add_exp_prod1( exp_lhs_symbol, exp_rhs )

                        assert opt_i == n_optionals

    def add_exp_prod1(this_grammar, exp_lhs, exp_rhs):
        if exp_lhs not in this_grammar.exp_prodns:
            this_grammar.exp_prodns[exp_lhs] = []
        this_grammar.exp_prodns[exp_lhs].append( exp_rhs )

    # --------------------------------------------------------------------------

    def print_exp_prodns(this_grammar):
        stderr('    print_exp_prodns ...')
        filename = '%s_expanded_grammar' % this_grammar.name
        f = shared.open_for_output(filename)

        i = 0
        for (exp_lhs, exp_rhss) in this_grammar.exp_prodns.items():
            for exp_rhs in exp_rhss:
                # print("%3d: " % i, end=None)
                print("%61s -> %s" % (
                        exp_lhs,
                        stringify_rthings(exp_rhs)
                    ),
                    file=f
                )
                i += 1
        f.close()

    # --------------------------------------------------------------------------

    def calc_min_length(this_grammar):
        # XXX UNUSED?
        stderr('    calc_min_length ...')

        this_grammar.min_length_for_nt_named_ = defaultdict(int)

        def min_len(rhs_item_n):
            if type(rhs_item_n) == SNT:
                return this_grammar.min_length_for_nt_named_[rhs_item_n.n]
            elif type(rhs_item_n) in terminal_types:
                return 1
            elif type(rhs_item_n) in [LAI, LAX, A_but_not, A_but_only_if, A_no_LT]:
                return 0
            else:
                assert 0, rhs_item_n

        while True:
            something_changed = False
            for (exp_lhs, exp_rhss) in this_grammar.exp_prodns.items():
                new_min_len = min(
                    sum(
                        min_len(rhs_item_n)
                        for rhs_item_n in exp_rhs
                    )
                    for exp_rhs in exp_rhss
                )
                assert new_min_len >= this_grammar.min_length_for_nt_named_[exp_lhs]
                if new_min_len > this_grammar.min_length_for_nt_named_[exp_lhs]:
                    this_grammar.min_length_for_nt_named_[exp_lhs] = new_min_len
                    something_changed = True
            if not something_changed:
                break

        filename = '%s_min_len' % this_grammar.name
        f = shared.open_for_output(filename)
        for (exp_lhs, min_len) in sorted(this_grammar.min_length_for_nt_named_.items()):
            print(min_len, exp_lhs, file=f)
        f.close()

    # --------------------------------------------------------------------------

    def compute_firstk(this_grammar):
        stderr('    compute_firstk ...')

        this_grammar.firstk_for_nt_named_ = defaultdict(lambda: defaultdict(set))

        def firstk_for_symbols(symbols, k):
            assert k >= 0
            if symbols == [] or k == 0:
                yield tuple()
            else:
                (s0, rest) = (symbols[0], symbols[1:])
                if type(s0) == SNT:
                    x = this_grammar.firstk_for_nt_named_[s0.n][k]
                    if rest and type(rest[0]) == A_but_not:
                        # stderr('>>  ', symbols)
                        pass # XXX?
                elif type(s0) in terminal_types:
                    f00 = tuple([s0])
                    x = set([f00])
                elif type(s0) in [A_no_LT, A_but_not, LAX]:
                    f00 = tuple([])
                    x = set([f00])
                else:
                    assert 0, s0
                for f0 in x:
                    assert isinstance(f0, tuple)
                    for fr in firstk_for_symbols(rest, k - len(f0)):
                        assert isinstance(fr, tuple)
                        yield f0 + fr

        # kludge
        max_k = 2 if this_grammar.name == 'syntactic' else 1

        n_passes = 0
        while True:
            something_changed = False
            n_passes += 1

            for (exp_lhs, exp_rhss) in this_grammar.exp_prodns.items():
                trace = (exp_lhs == 'ArgumentList+Yield')

                for k in range(1, max_k+1):

                    old_firstk = this_grammar.firstk_for_nt_named_[exp_lhs][k]

                    new_firstk = set()
                    for exp_rhs in exp_rhss:
                        new_firstk.update( firstk_for_symbols(exp_rhs, k) )

                    if False and trace:
                        stderr()
                        stderr('pass %d' % n_passes)
                        stderr('  old_firstk:', old_firstk)
                        stderr('  new_firstk:', new_firstk)

                    if new_firstk != old_firstk:
                        if 0:
                            print("first %d for %s has changed\n  from %r\n    to %r" %
                                (k, exp_lhs, old_firstk, new_firstk)
                            )
                        assert new_firstk > old_firstk
                        this_grammar.firstk_for_nt_named_[exp_lhs][k] = new_firstk
                        something_changed = True


            if not something_changed:
                break

        stderr(f'        {n_passes} passes')

        filename = '%s_firstk' % this_grammar.name
        f = shared.open_for_output(filename)
        for (exp_lhs, k_firstk) in sorted(this_grammar.firstk_for_nt_named_.items()):
            print(file=f)
            print(exp_lhs, file=f)
            for (k, firstk) in sorted(k_firstk.items()):
                print('  ', k, file=f)
                for fk in sorted(list(firstk)):
                    print('    [' + ' '.join(map(str, fk)) + ']', file=f)
        f.close()

    # --------------------------------------------------------------------------

    def generate_LR0_automaton(this_grammar):
        stderr('    generate_LR0_automaton ...')

        n_conflicts = 0
        max_stacklet_len = 0

        # ------------------------------------------------------------

        def generate_LR0_main():
            t_start = time.time()

            item0 = LR0_Item(None, (this_grammar.start_symbol,), 0)
            lr0 = DFA.Automaton(item0, LR0_State)

            t_end = time.time()
            t_elapsed = t_end - t_start
            stderr(
                "    LR0 machine constructed (in %d sec) with %d states and %d conflicts" %
                (t_elapsed, len(lr0.state_for_kernel_), n_conflicts)
            )

            stderr("    printing automaton...")
            filename = '%s_automaton' % this_grammar.name
            f = shared.open_for_output(filename)
            lr0.print(f, stringify_rthing)
            stderr("    done")

            return # XXX for now

            for state in lr0.state_for_kernel_.values():
                state.resolve_any_conflicts()

        # ------------------------------------------------------------

        class LR0_Item(namedtuple('_Item', 'lhs rhs dot_posn')):

            def __str__(this_item):
                return (
                    stringify_rthing(this_item.lhs)
                    +
                    ' -> '
                    +
                    stringify_rthings(this_item.rhs[0:this_item.dot_posn])
                    +
                    ' ## '
                    +
                    stringify_rthings(this_item.rhs[this_item.dot_posn:])
                )

            def each_transition(this_item):
                assert this_item.dot_posn >= 0
                assert this_item.dot_posn <= len(this_item.rhs)

                current_lax = None
                for (rposn, rhs_item_n) in enumerate(this_item.rhs):
                    if rposn < this_item.dot_posn: continue

                    t = type(rhs_item_n)
                    if t in [A_but_only_if, A_but_not, A_no_LT]:
                        pass

                    elif t in [LAX,LAI]:
                        assert current_lax is None
                        current_lax = rhs_item_n

                    elif t in terminal_types:
                        if current_lax is not None:
                            assert this_item.lax_is_satisfied_by_terminal(current_lax, rhs_item_n)
                            current_lax = None

                        next_item = LR0_Item(this_item.lhs, this_item.rhs, rposn+1)
                        yield (rhs_item_n, next_item)
                        break # don't look at any further things in the rhs

                    elif t == SNT:
                        nt = rhs_item_n
                        for derived_rhs in this_grammar.exp_prodns[nt.n]:
                            if current_lax is None:
                                new_item_rhs = derived_rhs
                            else:
                                # new_item_rhs = this_item.lax_plus_rhs(current_lax, derived_rhs)
                                new_item_rhs = derived_rhs

                            if new_item_rhs is not None:
                                new_item = LR0_Item(nt, tuple(new_item_rhs), 0)
                                yield (None, new_item)

                        next_item = LR0_Item(this_item.lhs, this_item.rhs, rposn+1)
                        yield (rhs_item_n, next_item)
                        break # don't look at any further things in the rhs

                    else:
                        assert 0, rhs_item_n

            def lax_is_satisfied_by_terminal(this_item, lax, terminal):
                return True
                # --------------------
                if lax.ts == (T_lit('let ['),) and terminal == T_lit(';'):
                    return True
                assert 0, (lax, terminal)

            def lax_plus_rhs(this_item, lax, rhs):
                rhs_item_n = rhs[0]
                if type(rhs_item_n) in terminal_types:
                    for lax_thing in lax.ts:
                        assert type(lax_thing) == T_lit
                        if type(lax_thing) != type(rhs_item_n):
                            pass
                        elif lax_thing == rhs_item_n:
                            # The LAX prohibits the first symbol of the rhs
                            return None
                        elif ' ' in lax_thing.c:
                            pieces = lax_thing.c.split()
                            assert pieces[0] != rhs_item_n.c

                    # The LAX does not prohibit the first symbol of the rhs.
                    # Therefore, it is redundant.
                    return rhs
                elif type(rhs_item_n) == SNT:
                    # Should we determine how lax compares to rhing's language?
                    return [lax] + rhs
                else:
                    assert 0, rhs_item_n
                    return [lax] + rhs
                    # --------------------

        class LR0_State(DFA.State):
            def __repr__(this_state):
                return "<State #%d>" % this_state.number

            def __lt__(this_state, other_state):
                return (this_state.number < other_state.number)

            def post_close(this_state):
                for next_state in this_state.transitions.values():
                    if not hasattr(next_state, 'prev_states'):
                        next_state.prev_states = []
                    next_state.prev_states.append(this_state)

                this_state.has_conflict = (
                    len(this_state.final_items) > 1
                    or
                    len(this_state.final_items) > 0 and len([
                            X
                            for (X, _) in this_state.transitions.items()
                            if type(X) != SNT
                        ]) > 0
                )
                if this_state.has_conflict:
                    nonlocal n_conflicts
                    n_conflicts += 1

#                this_state.actions_ = {
#                    'terminal': defaultdict(list),
#                    'nonterminal': defaultdict(list)
#                }
#
#                for (X, next_state) in sorted(this_state.transitions.items()):
#                    if X == this_grammar.eoi_symbol:
#                        action = ('accept',)
#                        which = 'terminal'
#                    else:
#                        action = ('shift_and_go_to', next_state)
#                        if type(X) in terminal_types:
#                            which = 'terminal'
#                        elif type(X) == SNT:
#                            which = 'nonterminal'
#                        else:
#                            assert 0, X
#                    this_state.actions_[which][X].append(action)

            def post_print(this_state, put):
                if this_state.has_conflict:
                    put()
                    put('  CONFLICT!')
                put()
#                put('  actions:')
#                for which in ['terminal', 'nonterminal']:
#                    put('    ', which)
#                    for (X, actions) in sorted(this_state.actions_[which].items()):
#                        put('      ', stringify_rthing(X))
#                        for action in actions:
#                            if action[0] == 'accept':
#                                action_str = 'ACCEPT'
#                            elif action[0] == 'shift_and_go_to':
#                                action_str = '%s #%d' % (action[0], action[1].number)
#                            else:
#                                assert 0
#                            put('        ', action_str)

            def resolve_any_conflicts(this_lr0_state):
                if not this_lr0_state.has_conflict: return

                # Generate a lookahead automaton to allow us
                # to decide between conflicting actions.

                stderr("    state #%d has a conflict" % this_lr0_state.number)

                stacklet = (this_lr0_state,)
                la_item0 = LA_Item(None, stacklet)
                this_lr0_state.la_automaton = DFA.Automaton(la_item0, LA_State)
                stderr("    LA automaton has %d states" %
                    len(this_lr0_state.la_automaton.state_for_kernel_)
                )

        # ------------------------------------------------------------

        class LA_Item(namedtuple('_LA_Item', 'choice stacklet')):

            def each_transition(this_la_item):

                def each_transition_main():
                    (choice, stacklet) = this_la_item
                    top_lr0_state = stacklet[-1]
                    assert isinstance(top_lr0_state, LR0_State)

                    # reductions
                    for lr0_item in top_lr0_state.final_items:
                        next_choice = ('r',lr0_item) if choice is None else choice
                        for next_stacklet in simulate_reduction(stacklet, lr0_item):
                            next_item = LA_Item(next_choice, next_stacklet)
                            yield (None, next_item)

                    # shifts
                    for (X, next_lr0_state) in sorted(top_lr0_state.transitions.items()):
                        if type(X) == SNT: continue
                        assert type(X) in terminal_types
                        next_choice = ('s',X) if choice is None else choice
                        next_stacklet = simulate_shift(stacklet, X, next_lr0_state)
                        next_item = LA_Item(next_choice, next_stacklet)
                        yield (X, next_item)

                def simulate_reduction(stacklet, lr0_item):
                    if 0:
                        print()
                        print('simulate_reduction...')
                        print('    ', stacklet)
                        print('    ', lr0_item)

                    # assert lr0_item.dot_posn == len(lr0_item.rhs)
                    # Thats usually true, but not if the last rhs_item_n
                    # in the rhs is an annotation.

                    n_symbols_in_rhs = sum(
                        1
                        for rhs_item_n in lr0_item.rhs
                        if type(rhs_item_n) == SNT or type(rhs_item_n) in terminal_types
                    )
                    if 0: print('    ', n_symbols_in_rhs)

                    for st in backtrack(stacklet, n_symbols_in_rhs):
                        back_lr0_state = st[-1]
                        next_lr0_state = back_lr0_state.transitions[lr0_item.lhs]
                        rst = simulate_shift(st, lr0_item.lhs, next_lr0_state)
                        if 0: print('        ', rst)
                        yield rst

                def backtrack(stacklet, n_to_pop):
                    assert len(stacklet) > 0
                    if n_to_pop == 0:
                        yield stacklet
                    else:
                        # backtrack by 1:
                        if len(stacklet) > 1:
                            back_st = stacklet[0:-1]
                            for st in backtrack(back_st, n_to_pop-1):
                                yield st
                        elif len(stacklet) == 1:
                            [remaining_state] = stacklet
                            for back_lr0_state in remaining_state.prev_states:
                                back_st = (back_lr0_state,)
                                for st in backtrack(back_st, n_to_pop-1):
                                    yield st
                        else:
                            assert 0

                def simulate_shift(stacklet, symbol, lr0_state):
                    new_stacklet = stacklet + (lr0_state,)
                    m = 3
                    if len(new_stacklet) > m:
                        # print('    truncating stacklet of length', len(new_stacklet))
                        new_stacklet = new_stacklet[-m:]

                    nonlocal max_stacklet_len
                    max_stacklet_len = max(max_stacklet_len, len(new_stacklet))
                    return new_stacklet
                    # XXX: also stack the symbol?

                # ----------------------------

                yield from each_transition_main()

        class LA_State(DFA.State):
            def should_be_closed(this_state):
                if this_state.number == 0:
                    return True

                if this_state.number > 100:
                    f = open('/tmp/la_au', 'w')
                    this_state.automaton.print(f, str)
                    f.close()
                    assert 0
                    return False

                # An LA_State needs to be closed if the items in its kernel
                # reflect more than one distinct choice.
                distinct_choices = set(
                    la_item.choice
                    for la_item in this_state.kernel
                )
                assert len(distinct_choices) >= 1
                return (len(distinct_choices) > 1)

            def post_close(this_state):
                # this_state.print(sys.stdout, str)
                pass

        # ------------------------------------------------------------

        generate_LR0_main()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def each_params_setting(params):
    # `params` is a list of grammatical parameters (i.e., just names).
    # Each of them can take on a '+' or '~' setting.
    # Yield every possible combination of settings for these parameters.
    for bools in each_boolean_vector_of_length(len(params)):
        yield [
            ('+' if b else '~') + p
            for (b, p) in zip(bools, params)
        ]

def c_to_terminal(c):
    if c == "'":
        return '"' + c + '"'
    else:
        return "'" + c + "'"

def expand_nt_wrt_params_setting(nt, params_setting):
    assert type(nt) == GNT
    result = nt.n
    for arg in nt.a:
        if arg.s == '?':
            for p in params_setting:
                if p[1:] == arg.n:
                    result += p
                    break
            else:
                # There is no param by that name in params_setting.
                assert 0, nt
        elif arg.s in ['+','~']:
            result += arg.s + arg.n
        else:
            assert 0, arg
    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

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

def decode_entities(text):
    assert '<' not in text, text
    # assert '>' not in text 
    # comment it out due to "[>" in grammars?
    return ( text
        .replace(r'&lt;', '<')
        .replace(r'&gt;', '>')
        .replace(r'&ldquo;', '\u201C')
        .replace(r'&rdquo;', '\u201D')
        .replace(r'&amp;', '&')
    )

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
