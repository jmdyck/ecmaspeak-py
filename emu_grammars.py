#!/usr/bin/python3

# ecmaspeak-py/emu_grammars.py:
# Analyze <emu-grammar> elements.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import atexit, subprocess, re, time, sys, pdb
from collections import namedtuple, defaultdict, OrderedDict

import DFA
from Tokenizer import Tokenizer, TokenizationError
import shared
from shared import stderr, header, msg_at_posn, spec
from emu_grammar_tokens import * 

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_stuff_with_grammars():
    stderr('do_stuff_with_grammars...')

    emu_grammars_of_type_ = {
        'definition': [],
        'example'   : [],
        'reference' : [],
    }
    for emu_grammar in spec.doc_node.each_descendant_named('emu-grammar'):
        t = emu_grammar.attrs.get('type', 'reference')
        emu_grammars_of_type_[t].append(emu_grammar)

    stderr('<emu-grammar> counts:')
    for (t, emu_grammars) in sorted(emu_grammars_of_type_.items()):
        stderr('    ', len(emu_grammars), t)

    process_defining_emu_grammars(emu_grammars_of_type_['definition'])
    # check_reachability() not that useful?
    check_params_within_def_prodns()

    check_non_defining_prodns(emu_grammars_of_type_['reference'])

    check_emu_prodrefs(spec.doc_node)

    check_nonterminal_refs(spec.doc_node)

    # XXX should also check that emu_grammars_of_type_['example'] at least parse.

    do_grammar_left_right_stuff()
    # return
    generate_es_parsers()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

info_for_nt_ = None
grammar_named_ = None

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

        cc_section = emu_grammar.nearest_ancestor_satisfying(lambda node: node.is_a_section())

        arena = get_grammar_arena_for_section(cc_section)

        if arena == 'B':
            # Some are replacements, and some are augments. Need to know which.
            # Could detect it based on whether the preceding para says
            #   "The following augments the <Foo> production in <section-num>:"
            # but easier to hard-code it:
            augments = (cc_section.section_title in [
                'FunctionDeclarations in IfStatement Statement Clauses',
                'Initializers in ForIn Statement Heads',
            ])
        else:
            augments = False

        print(file=grammar_f)
        print('#', cc_section.section_num, cc_section.section_title, file=grammar_f)
        print(file=grammar_f)

        for (prodn_posn, lhs_symbol, prodn_params, colons, rhss) in parse_emu_grammar(emu_grammar, grammar_f):

            if cc_section.section_title == 'URI Syntax and Semantics':
                lhs_nt_pattern = r'^uri([A-Z][a-z]+)?$'
            else:
                lhs_nt_pattern = r'^[A-Z][a-zA-Z0-9]+$'
            assert re.match(lhs_nt_pattern, lhs_symbol), lhs_symbol

            info_for_nt_[lhs_symbol].supply(
                lhs_symbol, arena, prodn_posn, prodn_params, colons, augments, rhss )

    global grammar_named_
    grammar_named_ = keydefaultdict(Grammar)
    for (lhs_symbol, nt_info) in sorted(info_for_nt_.items()):

        # From a parsing point of view, there's really just two grammars,
        # each with multiple goal symbols.
        grammar_name = 'syntactic' if nt_info.colons == ':' else 'lexical'

        # See Bug 4088: https://tc39.github.io/archives/bugzilla/4088/
        if grammar_name == 'lexical' and lhs_symbol in [
            'ReservedWord',
            'Keyword',
            'FutureReservedWord',
            'NullLiteral',
            'BooleanLiteral',
        ]:
            stderr('Changing from lexical to syntactic:', lhs_symbol)
            grammar_name = 'syntactic'

        for arena in ['A', 'B']:
            r = nt_info.get_appropriate_def_occ(arena)
            if r is None: continue
            (prodn_posn, params, rhss) = r

            grammar_named_[grammar_name + arena].add_prodn(
                prodn_posn, lhs_symbol, params, rhss)

# ------------------------------------------------------------------------------

def parse_emu_grammar(emu_grammar, output_f):
    assert emu_grammar.element_name == 'emu-grammar'

    raw_prodns_text = emu_grammar.inner_source_text()
    prodn_offsets = [0] + [mo.end() for mo in re.finditer(r'\n{2,}', raw_prodns_text)]

    prodns_text = decode_entities(trim_newlines(raw_prodns_text))

    if output_f: print(prodns_text, file=output_f)

    for (prodn_offset, prodn_text) in zip(prodn_offsets, re.split(r'\n{2,}', prodns_text)):

        prodn_posn = emu_grammar.inner_start_posn + prodn_offset

        split_lines = [
            split_indentation(line)
            for line in prodn_text.split('\n')
        ]

        (first_ind, first_line) = split_lines[0]
        mo = re.match(r'^(\w+)(?:\[(.+)\])? (:+)(.*)', first_line)
        assert mo, first_line
        (lhs_symbol, prodn_params_str, colons, first_line_rem) = mo.groups()

        if prodn_params_str is None:
            prodn_params = []
        else:
            # assert re.match(r'^[A-Z][a-z]*(, [A-Z][a-z]*)*$', prodn_params_str), prodn_text
            prodn_params = prodn_params_str.split(', ')
            for prodn_param in prodn_params:
                if not re.match(r'^[A-Z][a-z]*$', prodn_param):
                    msg_at_posn(prodn_posn, "gp-ERROR-159: ill-formed lhs-param: '%s'" % prodn_param)

        assert colons in [':', '::', ':::']
        # print(colons, section.section_num, section.section_title)

        def each_rhs():
            if len(split_lines) == 1:
                # one-line production
                if first_line_rem.startswith(' one of '):
                    # normalize 'one of' production into one with multiple
                    # right-hand-sides, each of which is only a single symbol:
                    for rthing in rhs_tokenizer.tokenize(first_line_rem[8:]):
                        assert type(rthing) == T_lit
                        yield [rthing]
                else:
                    try:
                        rthings = rhs_tokenizer.tokenize(first_line_rem)
                        yield rthings
                    except TokenizationError:
                        msg_at_posn(prodn_posn, "ERROR: tokenization")
            else:
                # multi-line production
                if first_line_rem not in ['', ' one of']:
                    msg_at_posn(prodn_posn, "ERROR: Multi-line production's first line ends oddly")
                else:
                    for (r_ind, r_line) in split_lines[1:]:
                        assert r_ind == first_ind + 2, prodn_text
                        try:
                            rthings = rhs_tokenizer.tokenize(r_line)
                        except TokenizationError:
                            msg_at_posn(prodn_posn, "ERROR: tokenization")
                            rthings = []
                        if first_line_rem == '':
                            yield rthings
                        elif first_line_rem == ' one of':
                            # normalize 'one of' production
                            for rthing in rthings:
                                assert type(rthing) == T_lit
                                yield [rthing]
                        else:
                            assert 0, first_line_rem

        rhss = []
        for rhs in each_rhs():

            # Eliminate A_empty, it's just a placeholder.
            if any(type(rthing) == A_empty for rthing in rhs):
                assert len(rhs) == 1
                rhs = []

            # Merge adjacent LAX (in NotEscapeSequence RHS #5 + #11)
            for r in range(len(rhs)-1, 0, -1):
                if type(rhs[r]) == LAX and r > 0 and type(rhs[r-1]) == LAX:
                    rhs[r-1] = LAX(ts= (rhs[r-1].ts + rhs[r].ts))
                    del rhs[r]

            rhss.append(rhs)

        yield (prodn_posn, lhs_symbol, prodn_params, colons, rhss)

# ------------------------------------------------------------------------------

terminal_types = [T_lit, T_nc, T_u_p, T_u_r, T_named ]

def stringify_rthings(rthings):
    return ' '.join(map(stringify_rthing, rthings))

def stringify_rthing(rthing):
    if isinstance(rthing, SNT) or isinstance(rthing, T_named):
        return rthing.n
    elif isinstance(rthing, T_lit) and rthing.c != '"':
        return '"' + rthing.c + '"'
    else:
        return str(rthing)

rhs_tokenizer = Tokenizer([
    ('(\w+|@)',                              lambda g: GNT(n=g(1), a=(), o=False)),
    ('(\w+)\?',                              lambda g: GNT(n=g(1), a=(), o=True)),
    ('(\w+)\[([+~?]\w+(?:, [+~?]\w+)*)\]',   lambda g: GNT(n=g(1), a=parse_args(g(2)), o=False)),
    ('(\w+)\[([+~?]\w+(?:, [+~?]\w+)*)\]\?', lambda g: GNT(n=g(1), a=parse_args(g(2)), o=True)),

    ('`(\S+)`',                              lambda g: T_lit(c=g(1))),
    ('<([A-Z]+)>',                           lambda g: T_nc(n=g(1))),
    ('> any Unicode code point',             lambda g: T_u_p(p=None)),
    ('> any Unicode code point with the Unicode property \u201C(\w+)\u201D', lambda g: T_u_p(p=g(1))),

    (' ',                             None),
    ('\[([+~])([A-Z][a-z]*)\]',       lambda g: A_guard(s=g(1), n=g(2))),
    ('#(\w+)',                        lambda g: A_id(i=g(1))),
    ('but not (.+)',                  lambda g: A_but_not(b=parse_buts(g(1)))),
    ('\[> but only if (.+?)\]',       lambda g: A_but_only_if(c=g(1))),
    ('\[empty\]',                     lambda g: A_empty()),
    ('\[no LineTerminator here\]',    lambda g: A_no_LT()),
    ('\[lookahead == `([^` ]+)`\]',   lambda g: LAI(ts=(T_lit(c=g(1)),))),
    ('\[lookahead != `([^` ]+)` ?\]', lambda g: LAX(ts=(T_lit(c=g(1)),))),
    ('\[lookahead != `(let` `\[)`\]', lambda g: LAX(ts=(T_lit(c=g(1)),))), # kludge
    ('\[lookahead != <([A-Z]+)> \]',  lambda g: LAX(ts=(T_nc(n=g(1)),))),
    ('\[lookahead <! (\w+)\]',        lambda g: LAX(ts=(GNT(n=g(1), a=(), o=False),))),
    ('\[lookahead <! {([^}]+)}\]',    lambda g: LAX(ts=parse_terminals(g(1)))),
])
atexit.register(rhs_tokenizer.print_unused_paterns)

def parse_args(args_str):
    args = []
    for arg_str in args_str.split(', '):
        if arg_str[0] in ['+', '~', '?']:
            arg = Arg(s=arg_str[0], n=arg_str[1:])
        else:
            arg = Arg(s='', n=arg_str) # '+' ?
        args.append(arg)
    return tuple(args)

def parse_buts(buts_str):
    mo2 = re.match(r'^one of (.+)', buts_str)
    if mo2:
        if ' or ' in buts_str:
            but_strs = mo2.group(1).split(' or ')
        else:
            but_strs = mo2.group(1).split(' ')
    else:
        but_strs = [buts_str]
    buts = []
    for but_str in but_strs:
        if re.match(r'^\w+$', but_str):
            but = GNT(but_str, (), False)
        elif re.match(r'^`(\S+)`$', but_str):
            but = T_lit(but_str[1:-1])
        elif but_str == 'U+0000 through U+001F':
            but = T_u_r('U+0000', 'U+001F')
        else:
            assert 0, but_str
        buts.append(but)
    return tuple(buts)

def parse_terminals(list_str):
    ts = []
    for item in list_str.split(', '):
        assert item.startswith('`'), list_str
        assert item.endswith('`')
        chars = item[1:-1]
        if chars == 'async` [no |LineTerminator| here] `function':
            chars = 'async nLTh function'
        ts.append(T_lit(c=chars))
    return tuple(ts) # XXX sorted???

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class NonterminalInfo:
    def __init__(self):
        self.def_occs = defaultdict()

    def supply(self, symbol, arena, prodn_posn, params, colons, augments, rhss):
        if not hasattr(self, 'symbol'):
            self.symbol = symbol
            self.colons = colons
        else:
            assert symbol == self.symbol
            if colons != self.colons:
                msg_at_posn(prodn_posn, 'ERROR: colons mismatch for %s: was %s, here %s' %
                    (self.symbol, self.colons, colons))

        if arena in self.def_occs:
            msg_at_posn(prodn_posn, 'Additional defining production for: ' + symbol)
            return

        if augments:
            assert arena != 'A'
            (_, params_from_arena_a, rhss_from_arena_a) = self.def_occs['A']
            assert params == params_from_arena_a
            rhss = rhss_from_arena_a + rhss

        self.def_occs[arena] = (prodn_posn, params, rhss)

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
        (_, _, rhss) = nt_info.def_occs['A']
        for rhs in rhss:
            for rthing in rhs:
                rthing_kind = type(rthing)
                if rthing_kind == GNT:
                    reach(rthing.n)
                elif rthing_kind == A_but_not:
                    for but in rthing.b:
                        if type(but) == GNT:
                            reach(but.n)

    for (nt, nt_info) in sorted(info_for_nt_.items()):
        if 'A' in nt_info.def_occs and nt_info.colons != ':' and nt not in lexical_symbols:
            print('lexical symbol not reached:', nt)

# ------------------------------------------------------------------------------

# g_current_branch_name = subprocess.check_output('git rev-parse --abbrev-ref HEAD'.split(' ')).rstrip()

def check_params_within_def_prodns():
    stderr("check_params_within_def_prodns...")
    header("checking grammatical parameters in defining prodns...")

    for (nt, nt_info) in sorted(info_for_nt_.items()):
        # Look at all 'defining occurrences' of nt.
        # (Usually just 1, might be 2 (Annex B).)

        for (arena, (prodn_posn, nt_param_names, rhss)) in sorted(nt_info.def_occs.items()):
            for (rhs_i, rhs) in enumerate(rhss):
                rhs_guard_sign = None
                rhs_guard_param_name = None
                for rthing in rhs:
                    rthing_kind = type(rthing)
                    if rthing_kind == A_guard:
                        (rhs_guard_sign, rhs_guard_param_name) = (rthing.s, rthing.n)
                        continue
                    elif rthing_kind != GNT:
                        continue

                    for r_arg in rthing.a:
                        if r_arg.s not in ['+', '~', '?']:
                            msg_at_posn(prodn_posn,
                                "gp-ERROR-447: In rhs #%d, arg is missing +~?: %s" %
                                    (rhs_i + 1, r_arg.n)
                            )

                    if rthing.n not in info_for_nt_:
                        msg_at_posn(prodn_posn,
                            "ERROR: In rhs #%d, refers to undefined nonterminal '%s'" %
                                (rhs_i + 1, rthing.n)
                        )
                        continue

                    r_param_names = [ r_arg.n for r_arg in rthing.a ]
                    (_, d_param_names, _) = info_for_nt_[rthing.n].get_appropriate_def_occ(arena)

                    if len(r_param_names) == len(d_param_names):
                        if r_param_names != d_param_names:
                            msg_at_posn(prodn_posn,
                                "gp-ERROR-454: In rhs #%d, args are ordered %s but should be %s" %
                                (rhs_i, r_param_names, d_param_names)
                            )
                    else:
                        msg_at_posn(prodn_posn,
                            "gp-ERROR-459: %s takes %s but is invoked with %s" %
                            (rthing.n, d_param_names, r_param_names)
                        )

                    # Look for valid-but-anomalous args...
                    for r_arg in rthing.a:
                        if r_arg.n in nt_param_names:
                            # This arg refers to a parameter that appears on the prodn's LHS.
                            if r_arg.s == '?': 
                                # Simply 'pass down' the value of that param.
                                pass
                            elif r_arg.n == rhs_guard_param_name and r_arg.s == rhs_guard_sign:
                                pass
                            else:
                                msg_at_posn(prodn_posn,
                                    "gp-WARNING-474: %s has %s param, so you'd normally expect [?%s] in its rhss, but rhs #%d has %s[%s%s]" % (
                                        nt,
                                        r_arg.n,
                                        r_arg.n,
                                        rhs_i + 1,
                                        rthing.n, r_arg.s, r_arg.n
                                    )
                                )
                        else:
                            # This arg refers to parameter
                            # that does not appear on the prodn's LHS.
                            # assert r_arg.s != '?', rhs
                            if r_arg.s == '?':
                                msg_at_posn(prodn_posn,
                                    "gp-ERROR-488: %s does not appear on the prodn's LHS, so cannot be referenced with '?'" %
                                    r_arg.n 
                                )
                            # because you can only use '?' on the RHS
                            # when the parameter is 'declared' on the LHS


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

        # closest-containing section
        cc_section = emu_grammar.nearest_ancestor_satisfying(lambda node: node.is_a_section())
        arena = get_grammar_arena_for_section(cc_section)

        for (u_posn, lhs_nt, u_prodn_params, u_colons, u_rhss) in parse_emu_grammar(emu_grammar, None):
            if lhs_nt not in info_for_nt_:
                msg_at_posn(u_posn,
                    "ERROR: lhs symbol in 'use' production does not match any defined nonterminal: " + lhs_nt
                )
                continue

            nt_info = info_for_nt_[lhs_nt]

            if u_colons != nt_info.colons:
                msg_at_posn(u_posn,
                    "ERROR: #colons in use (%d) does not match #colons in defn (%d)" %
                    (len(u_colons), len(nt_info.colons))
                )

            (def_prodn_posn, def_prodn_params, def_rhss) = nt_info.get_appropriate_def_occ(arena)

            if def_prodn_params:
                # The 'def' production has parameters.
                if u_prodn_params:
                    # This is an uncommon case (~20 occurrences),
                    # where the 'def' production has parameters
                    # and the 'use' production repeats them
                    # (because accompanying prose needs to refer to them).
                    u_lhs_args_are_suppressed = False

                    if u_prodn_params != def_prodn_params:
                        msg_at_posn(u_posn,
                            "ERROR: params in use (%s) does not match params in defn (%s)" %
                            (u_prodn_params, def_prodn_params)
                        )
                    # print(lhs_nt, def_prodn_params)

                else:
                    # This is a typical case (~958 occurrences),
                    # where a 'use' production elides the parameters
                    # specified in the 'def' production.
                    u_lhs_args_are_suppressed = True
            else:
                # The 'def' production doesn't have parameters.
                # (~430 occurrences)
                u_lhs_args_are_suppressed = None
                assert not u_prodn_params

            # In the use-prodn, we expect rhs-args iff there are lhs-params.
            # u_expect_rhs_args = len(u_prodn_params) > 0

            # --------------------------
            # In 'use' productions, we don't usually have annotations

            for (u_i, u_rhs) in enumerate(u_rhss):
                annotations = [
                    item
                    for item in u_rhs
                    if item.T not in ['GNT', 'T_lit', 'T_nc']
                ]

                # For certain productions, allow one annotation:
                if len(annotations) == 1:
                    [anno] = annotations
                    if (
                        cc_section.section_title == 'Rules of Automatic Semicolon Insertion' and anno.T == 'A_no_LT'
                        or lhs_nt in [
                            'DoubleStringCharacter',
                            'SingleStringCharacter',
                            'NonEscapeCharacter',
                            'TemplateCharacter',
                            'Identifier',
                            'ClassAtomNoDash',
                            ]
                            and anno.T == 'A_but_not'
                        or lhs_nt == 'NotEscapeSequence' and anno.T == 'LAX'
                        or lhs_nt == 'CharacterEscape' and anno.T == 'LAX'
                        or lhs_nt == 'ClassAtomNoDash' and anno.T == 'LAI'
                        or lhs_nt == 'ExtendedAtom' and anno.T == 'LAI'
                    ):
                        continue

                if annotations:
                    msg_at_posn(u_posn,
                        f"WARNING: {lhs_nt} RHS#{u_i+1} has {len(annotations)} annotations: {annotations}"
                    )

            # --------------------------

            rmc = RhsMatchesChecker(lhs_nt, u_posn, len(u_rhss))

            for (u_i, u_rhs) in enumerate(u_rhss):
                for (def_i, def_rhs) in enumerate(def_rhss):
                    # Does u_rhs match def_rhs?

                    notes = u_rhs_matches_d_rhs_(u_rhs, def_rhs)
                    if notes == False:
                        # Nope, doesn't match. Try the next def_rhs.
                        continue

                    # Yes, it does match...

                    rmc.u_matches_d(u_i, def_i)

                    # ------------------

                    if u_lhs_args_are_suppressed is None:
                        pass
                    elif u_lhs_args_are_suppressed:
                        notes['nt-args suppressed'].insert(0, lhs_nt)
                    else:
                        notes['nt-args intact'].insert(0, lhs_nt)

                    if notes['nt-args suppressed'] and notes['nt-args intact']:
                        msg_at_posn(u_posn, "gp-ERROR-624?: RHS suppresses args for %s but not for %s" %
                            (notes['nt-args suppressed'], notes['nt-args intact'])
                        )

                    # ------------------

                    if notes['annotations suppressed'] and notes['annotations intact']:
                        msg_at_posn(u_posn,
                            f"WARNING: RHS suppresses some annotations ({notes['annotations suppressed']}) but leaves some intact ({notes['annotations intact']})"
                        )

                    # ------------------

                    if 0 and notes['optional-GNT']:
                        print(lhs_nt, def_i, notes['optional-GNT'])

                    # ------------------

                    if 0:
                        for (k,v) in notes.items():
                            if k.startswith('L-'):
                                for one in v:
                                    assert one == 1
                                    print(k)

                    # ------------------

                    emu_grammar.summary.append((lhs_nt, def_i, notes['optional-GNT']))

            rmc.report()

def u_rhs_matches_d_rhs_(u_rhs, d_rhs):
    notes = defaultdict(list)
    u_offset = 0
    for d_item in d_rhs:
        if u_offset < len(u_rhs):
            u_item = u_rhs[u_offset]
            note = u_item_matches_d_item(u_item, d_item)
            if note is not None:
                # good so far
                u_offset += 1
                for (key, val) in note.items(): notes[key].append(val)
                continue

        note = d_item_doesnt_require_a_matching_u_item(d_item)
        if note is not None:
            # Assume that the item was omitted from the u_rhs,
            # and see if we can get a match that way.
            for (key, val) in note.items(): notes[key].append(val)
            continue

        return False

    # We've exhausted the d_rhs.
    # In order to match, we need to have exhausted the u_rhs too.
    if u_offset != len(u_rhs):
        return False

    return notes

def u_item_matches_d_item(u_item, d_item):
    # Returns None if they do not match.
    # Otherwise, returns a dict containing notes about the comparison.

    if u_item.T != d_item.T:
        # 3058 occurrences
        return None

    # Now we know they have the same type.

    t = u_item.T

    note = {}

    if t == 'GNT':
        if u_item.n != d_item.n:
            # They can't possibly match.
            return None

        note['L-670'] = 1
        # 2505 occurrences

        if d_item.o:
            # In the definition, this GNT is optional.
            if u_item.o:
                note['optional-GNT'] = (u_item.n, 'either')
                note['L-678'] = 1
                # 149 occurrences
            else:
                note['optional-GNT'] = (u_item.n, 'required')
                note['L-682'] = 1
                # 71 occurrences
        else:
            # In the definition, this GNT is not optional.
            assert not u_item.o
            note['L-687'] = 1
            # 2285 occurrences

        if d_item.a:
            # In the definition, this GNT has args.
            if u_item.a:
                assert u_item.a == d_item.a
                note['nt-args intact'] = u_item.n
                note['L-695'] = 1
                # 23 occurrences
            else:
                note['nt-args suppressed'] = u_item.n
                note['L-699'] = 1
                # 1884 occurrences
        else:
            # In the definition, this GNT has no args.
            assert not u_item.a
            note['L-703'] = 1
            # 598 occurrences

    else:

        if u_item != d_item:
            return None

        note['L-711'] = 1
        # 2523 occurrences

        if t.startswith('A_') or t in ['LAX', 'LAI']:
            note['annotations intact'] = u_item

    return note

#    if (
#        t == A_but_only_if
#        and
#        d_item.c == "the integer value of DecimalEscape is 0"
#        and
#        u_item.c == "&hellip;"
#    ):
#        return 'ellipsify condition in but_only_if'
#
#    if (
#        t == A_but_only_if
#        and
#        d_item.c == "the integer value of |DecimalEscape| is 0"
#        and
#        u_item.c == "&hellip;"
#    ):
#        return 'ellipsify condition in but_only_if'

def d_item_doesnt_require_a_matching_u_item(d_item):
    if type(d_item) in [A_guard, A_id, A_but_only_if, A_but_not, A_no_LT, LAX]:
        return {'annotations suppressed': d_item}

    if type(d_item) == GNT and d_item.o:
        return {'optional-GNT': (d_item.n, 'omitted')}

    return None

# ------------------------------------------------------------------------------

class RhsMatchesChecker:
    def __init__(self, lhs_nt, u_posn, n_u_rhs):
        self.lhs_nt = lhs_nt
        self.u_posn = u_posn
        self.n_u_rhs = n_u_rhs
        self.def_i_s_for_u_i_ = [
            [] for i in range(n_u_rhs)
        ]

    def u_matches_d(self, u_i, def_i):
        self.def_i_s_for_u_i_[u_i].append(def_i)

    def report(self):

        # Each 'use' RHS should match exactly one 'def' RHS.
        for (u_i, def_i_s) in enumerate(self.def_i_s_for_u_i_):
            L = len(def_i_s)
            if L == 0:

                msg_at_posn(self.u_posn,
                    f"ERROR: RHS#{u_i+1} does not match any defining RHS for {self.lhs_nt}"
                )
            elif L == 1:
                # good
                pass
            else:
                # This would indicate an obvious ambiguity in the grammar,
                # so is very unlikely. (I haven't seen it yet.)
                assert 0

        # As you walk through the 'use' RHSs in order,
        # the corresponding 'def' RHSs should also be in order
        # (though with possible 'holes' of course).
        all_def_i_s = []
        for def_i_s in self.def_i_s_for_u_i_:
            all_def_i_s.extend(def_i_s)
        if all_def_i_s == sorted(all_def_i_s):
            # good
            pass
        else:
            msg_at_posn(self.u_posn,
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
        u_i_s_for_def_i_ = defaultdict(list)
        for (u_i, def_i_s) in enumerate(self.def_i_s_for_u_i_):
            for def_i in def_i_s:
                u_i_s_for_def_i_[def_i].append(u_i)
        for (def_i, u_i_s) in sorted(u_i_s_for_def_i_.items()):
            L = len(u_i_s)
            if L == 0:
                # can't happen
                assert 0
            elif L == 1:
                # good
                pass
            else:
                # Likely a 'use' RHS has been pasted twice?
                u_j_s = [u_i+1 for u_i in u_i_s]
                msg_at_posn(self.u_posn,
                    f"ERROR: RHS#{','.join(u_j_s)} all match def RHS#{def_i+1}"
                )


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
            (prodn_posn, _, _) = nt_info.def_occs['A']
            arena_A_names_with_posn.append((prodn_posn, nt_name))

    arena_A_names_with_posn.sort()
    for (prodn_posn, nt_name) in arena_A_names_with_posn:
        if nt_name not in referenced_names:
            msg_at_posn(prodn_posn, f"ERROR: Production is not referenced in Annex A: '{nt_name}'")

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

def check_nonterminal_refs(doc_node):
    stderr("check_nonterminal_refs...")
    header("checking references to nonterminals (outside of emu-grammar)...")

    # kludge:
    B_start = shared.spec_text.find('namespace=annexB')

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
                        "gp-WARNING-753: nonterminal-ref has arg '%s', with no ?+~ prefix" % arg
                    )
                    # Actually, this is okay if it's referring to
                    # an occurrence in the LHS of a use production.
                    # But it's worth calling out for checking.
                    param_name = arg
                else:
                    param_name = arg[1:]
                param_names_in_args.append(param_name)

            arena = 'A' if posn < B_start else 'B' # kludge
            (_, def_prodn_params, _) = nt_info.get_appropriate_def_occ(arena)

            if param_names_in_args != def_prodn_params:
                msg_at_posn(posn,
                    "gp-ERROR-770: nonterminal-ref has args '%s', but nonterminal's definition has params '%s'" %
                    (args, ', '.join(def_prodn_params))
                )

        # XXX: Should check that _opt is compatible with nt's use.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_grammar_left_right_stuff():
    grammar_lr_f = shared.open_for_output('grammar_lr')
    def put(*args):
        print(*args, file=grammar_lr_f)

    for (grammar_name, g) in sorted(grammar_named_.items()):
        g.do_left_right_stuff(put)

# ------------------------------------------------------------------------------

def generate_es_parsers():
    stderr("generate_es_parsers...")

    for (grammar_name, g) in sorted(grammar_named_.items()):
        # stderr()
        # stderr('---------------------------')
        stderr(grammar_name)

        if grammar_name.startswith('lexical'):
            g.explode_multichar_literals()
            g.distinguish_Token_from_NonToken()

        g.save_as_json()

        if 0:
            # An LR approach, which bogged down
            # when I tried to handle lookahead-restrictions:
            g.expand_abbreviations()
            g.calc_min_length()
            g.compute_firstk()
            # g.propagate_LAX()
            g.print_exp_prodns()

            # Have to exclude lexicalB because it's incomplete.
            # (It doesn't 'duplicate' all prodns that must have 'N' added as grammatical param.)
            if grammar_name != 'lexicalB':
                g.generate_LR0_automaton()

    stderr()
    stderr('---------------------------')

# ------------------------------------------------------------------------------

class Grammar:
    def __init__(this_grammar, name):
        this_grammar.name = name
        this_grammar.prodn_for_lhs_ = {}

    # --------------------------------------------------------------------------

    def add_prodn(this_grammar, prodn_posn, lhs_symbol, prodn_params, rhss):
        assert lhs_symbol not in this_grammar.prodn_for_lhs_, lhs_symbol
        this_grammar.prodn_for_lhs_[lhs_symbol] = (prodn_posn, prodn_params, rhss)

    # --------------------------------------------------------------------------

    def do_left_right_stuff(this_grammar, put):
        put()
        put(this_grammar.name)
        lhs_symbols = set()
        rhs_symbols = set()
        for (lhs_symbol, (prodn_posn, prodn_params, rhss)) in sorted(this_grammar.prodn_for_lhs_.items()):
            lhs_symbols.add(lhs_symbol)
            for rhs in rhss:
                for rthing in rhs:
                    rthing_kind = type(rthing)
                    if rthing_kind == GNT:
                        rhs_symbols.add(rthing.n)
                    elif rthing_kind == A_but_not:
                        for but in rthing.b:
                            if type(but) == GNT:
                                rhs_symbols.add(but.n)
                    else:
                        pass

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

        for (lhs_symbol, (prodn_posn, prodn_params, rhss)) in sorted(this_grammar.prodn_for_lhs_.items()):
            for rhs in rhss:
                for (r, rthing) in enumerate(rhs):
                    rthing_kind = type(rthing)
                    if rthing_kind == GNT and rthing.n in this_grammar.named_terminals:
                        rhs[r] = T_named(rthing.n)

    # ==========================================================================

    def explode_multichar_literals(this_grammar):
        # mcl = "multicharacter literal",
        #       i.e., a T_lit whose 'c' has more than 1 character.
        #
        #" A <em>lexical grammar</em> for ECMAScript ...
        #" has as its terminal symbols Unicode code points ...
        #
        # So, in the lexical grammar, we explode multicharacter literals.

        def is_mcl(rthing):
            return type(rthing) == T_lit and len(rthing.c)>1

        for (lhs_symbol, (prodn_posn, prodn_params, rhss)) in sorted(this_grammar.prodn_for_lhs_.items()):
            for rhs in rhss:
                mcl_posns = [
                    r
                    for (r,rthing) in enumerate(rhs)
                    if is_mcl(rthing)
                ]

                # Explode them in reverse order
                for mcl_posn in reversed(mcl_posns):
                    mcl = rhs[mcl_posn]
                    assert is_mcl(mcl)

                    rhs[mcl_posn:mcl_posn+1] = [
                        T_lit(c=char)
                        for char in mcl.c
                    ]

    # ==========================================================================

    def distinguish_Token_from_NonToken(this_grammar):
        assert this_grammar.name.startswith('lexical')

        non_token_names = ['WhiteSpace','LineTerminator', 'Comment']
        non_token_rhss = [
            [GNT(non_token_name, (), False)]
            for non_token_name in non_token_names
        ]

        for (lhs_symbol, (prodn_posn, prodn_params, rhss)) in sorted(this_grammar.prodn_for_lhs_.items()):
            if lhs_symbol.startswith('InputElement'):
                ie_rest = lhs_symbol.replace('InputElement', '')
                # print(lhs_symbol)
                # print(prodn_params)
                # print(rhss)
                assert len(rhss) == 6
                assert rhss[0:3] == non_token_rhss
                # del rhss[0:3]

                this_grammar.prodn_for_lhs_['_Token' + ie_rest] = (
                    prodn_posn, prodn_params, rhss[3:])
                del this_grammar.prodn_for_lhs_[lhs_symbol]

        this_grammar.prodn_for_lhs_['_NonToken'] = (0, [], non_token_rhss)

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

        all_params = set()
        all_types = set()
        put('[')
        n_rhss = 0
        for (lhs_symbol, (prodn_posn, prodn_params, rhss)) in sorted(this_grammar.prodn_for_lhs_.items()):

            for param in prodn_params:
                all_params.add(param)
            for rhs in rhss:
                n_rhss += 1
                if n_rhss > 1: put(',')
                put('{')
                put('  "n": %d,' % n_rhss)
                put('  "lhs": "%s",' % lhs_symbol)
                put('  "params": [%s],' % ','.join('"%s"' % param for param in prodn_params))
                if rhs and type(rhs[0]) == A_guard:
                    put('  "guard": {"s":"%s", "n":"%s"},' % (rhs[0].s, rhs[0].n))
                else:
                    put('  "guard": null,')

                saved_pre = None
                runit = None
                runits = []
                for (r,rthing) in enumerate(rhs):
                    all_types.add(rthing.T)
                    if type(rthing) == A_guard:
                        assert r == 0
                        # already handled above
                    elif type(rthing) == A_id:
                        assert r == len(rhs) - 1
                        # doesn't contribute to parser

                    # Things that attach to the following symbol:
                    elif (
                        (type(rthing) in [LAX,LAI] and r < len(rhs) - 1)
                    ):
                        assert saved_pre is None
                        saved_pre = rthing

                    # Things that attach to the preceding symbol:
                    elif (
                        type(rthing) in [A_but_not, A_but_only_if, A_no_LT]
                        or
                        (type(rthing) in [LAX,LAI] and r == len(rhs) - 1)
                    ):
                        assert runit is not None
                        assert runit['post'] is None
                        runit['post'] = rthing

                    else:
                        assert type(rthing) == GNT or type(rthing) in terminal_types
                        runit = OrderedDict(
                            [('pre', saved_pre), ('rsymbol', rthing), ('post', None)]
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

    def expand_abbreviations(this_grammar):
        # Expand productions with respect to optionals and parameters.
        # (Expanding wrt parameters eliminates A_guard items.
        # Also eliminate A_id items, as they don't contribute.)
        # Generally, convert the grammar to something closer to a CFG.

        stderr('expand_abbreviations ...')

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

            for goal_symbol in goal_symbols:
                prep_symbol = T_named('prep_for_' + goal_symbol)
                this_grammar.add_exp_prod1(
                    this_grammar.start_symbol.n,
                    [prep_symbol, SNT(goal_symbol), this_grammar.eoi_symbol]
                )

        for (lhs_symbol, (prodn_posn, prodn_params, rhss)) in sorted(this_grammar.prodn_for_lhs_.items()):
            if 0:
                print()
                print('    ', lhs_symbol, prodn_params)
                for rhs in rhss:
                    print('        ', rhs)

            for params_setting in each_params_setting(prodn_params):
                exp_lhs_symbol = lhs_symbol + ''.join(params_setting)
                for rhs in rhss:

                    if rhs:
                        rthing0 = rhs[0]
                        if type(rthing0) == A_guard:
                            if (rthing0.s + rthing0.n) in params_setting:
                                # The guard succeeds.
                                pass
                            else:
                                # The guard fails.
                                continue # to next rhs

                    # count the number of optionals in this rhs
                    n_optionals = len([
                        rthing
                        for rthing in rhs
                        if type(rthing) == GNT and rthing.o
                    ])

                    # Generate a different rhs for each combo of optionals
                    for include_optional_ in each_boolean_vector_of_length(n_optionals):

                        opt_i = 0
                        exp_rhs = []

                        for (i,rthing) in enumerate(rhs):
                            if type(rthing) == A_guard:
                                assert i == 0
                                # We've already determined that this guard succeeds.
                                continue # to next rthing
                            elif type(rthing) == A_id:
                                assert i == len(rhs)-1
                                continue

                            elif type(rthing) in [A_but_only_if, A_but_not, A_no_LT]:
                                exp_rthing = rthing

                            elif type(rthing) in [LAX, LAI]:
                                if type(rthing.ts) in [tuple, list]:
                                    ts = rthing.ts
                                else:
                                    ts = [rthing.ts]

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
                                exp_rthing = rthing # XXX something(terminal_sequences)

                            elif type(rthing) in terminal_types:
                                exp_rthing = rthing

                            elif type(rthing) == GNT:
                                exp_rthing = SNT(expand_nt_wrt_params_setting(rthing, params_setting))
                                if rthing.o:
                                    include_this_optional = include_optional_[opt_i]
                                    opt_i += 1
                                    if include_this_optional:
                                        pass
                                    else:
                                        # omit the optional
                                        continue # to next rthing

                            else:
                                assert 0, rthing

                            exp_rhs.append(exp_rthing)

                        this_grammar.add_exp_prod1( exp_lhs_symbol, exp_rhs )

                        assert opt_i == n_optionals

    def add_exp_prod1(this_grammar, exp_lhs, exp_rhs):
        if exp_lhs not in this_grammar.exp_prodns:
            this_grammar.exp_prodns[exp_lhs] = []
        this_grammar.exp_prodns[exp_lhs].append( exp_rhs )

    # --------------------------------------------------------------------------

    def calc_min_length(this_grammar):
        # XXX UNUSED?
        stderr('calc_min_length ...')

        this_grammar.min_length_for_nt_named_ = defaultdict(int)

        def min_len(rthing):
            if type(rthing) == SNT:
                return this_grammar.min_length_for_nt_named_[rthing.n]
            elif type(rthing) in terminal_types:
                return 1
            elif type(rthing) in [LAI, LAX, A_but_not, A_but_only_if, A_no_LT]:
                return 0
            else:
                assert 0, rthing

        while True:
            something_changed = False
            for (exp_lhs, exp_rhss) in this_grammar.exp_prodns.items():
                new_min_len = min(
                    sum(
                        min_len(rthing)
                        for rthing in exp_rhs
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
        stderr('compute_firstk ...')

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

        stderr('   ', n_passes, 'passes')

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

#    def propagate_LAX(this_grammar):
#        stderr('propagate_LAX ...')
#
#        this_grammar.replacement_for_lax_case_ = {}
#
#        for (exp_lhs, exp_rhss) in this_grammar.exp_prodns.items():
#            for exp_rhs in exp_rhss:
#                lax_indexes = [
#                    i
#                    for (i,rthing) in enumerate(exp_rhs)
#                    if type(rthing) == LAX
#                ]
#                # Each RHS has at most one LAX:
#                assert len(lax_indexes) in [0,1]
#                if lax_indexes == []: continue
#
#                [i] = lax_indexes
#                assert i < len(exp_rhs)
#                if i == len(exp_rhs)-1:
#                    # LAX is the last thing in the RHS.
#                    continue
#                    # XXX but do something later??
#
#                lax = exp_rhs[i]
#                s = exp_rhs[i+1]
#                assert type(lax) == LAX
#                assert type(s) in [SNT, T_lit]
#
#                s_exp = this_grammar.replacement_for_lax_before_symbol(lax, s)
#                exp_rhs[i:i+2] = [s_exp]
#
#    # ----------------------------------------
#
#    def replacement_for_lax_before_symbol(this_grammar, lax, s):
#        if type(s) == T_lit:
#
#            # Normally, it wouldn't make sense to put a lookahead-restriction
#            # immediately before a T_lit.
#            # The only place where this happens is in the 3rd RHS for
#            # IterationStatement:
#            # in the unexpanded grammar, we have:
#            #   `for` `(` [lookahead <! {`let [`}] Expression[~In, ?Yield]? `;` ...
#            # which, due to expansion of '?', gives rise to:
#            #   `for` `(` [lookahead <! {`let [`}]                          `;` ...
#
#            assert s == T_lit(c=';')
#            assert lax == LAX(ts=(T_lit(c='let ['),))
#
#            # Here, the LAX is trivially satisfied,
#            # so we can replace lax-before-symbol with just the symbol.
#            return s
#
#        elif type(s) == SNT:
#            return this_grammar.symbol_variant_that_doesnt_start_with(s, lax.ts, 0)
#
#        else:
#            assert 0, s
#
#    def symbol_variant_that_doesnt_start_with(this_grammar, s, lats, level):
#        if lats == []:
#            return s
#
#        if type(lats) != tuple:
#            lats.sort() # already sorted?
#            lats = tuple(lats)
#
#        stderr('>>' * (level+1), s, lats)
#        key = (s, lats)
#        if key in this_grammar.replacement_for_lax_case_:
#            return this_grammar.replacement_for_lax_case_[key]
#
#        # Each disallowed lookahead in the lookahead-restriction
#        # is in the firstk of s.
#        for lat in lats:
#            assert this_grammar.symbol_can_start_with(s, lat)
#
#        # NSW = "not starting with"
#        nsw_name = s.n + '-NSW:(' + ','.join(lat.c for lat in lats) + ')'
#        nsw_s = SNT(n=nsw_name)
#
#        # important to do this before any recursive call,
#        # otherwise infinite recursion:
#        this_grammar.replacement_for_lax_case_[key] = nsw_s
#
#        s_exp_rhss = []
#        s_rhss = this_grammar.exp_prodns[s.n]
#        for s_rhs in s_rhss:
#            # How much (if any) of the LHS's NSW restriction
#            # is transferred to this RHS?
#
#            if s_rhs == []:
#                # In ES, the only time this happens is due to the first RHS for CharacterClass:
#                #     `[` [lookahead <! {`^`}] ClassRanges[?U] `]`
#                # because one of the rhs for ClassRanges is [empty].
#
#                assert lats == (T_lit(c='^'),)
#                assert s in [SNT(n='ClassRanges+U'), SNT(n='ClassRanges~U')]
#
#                # But that alternative for ClassRanges
#                # can't lead to a violation of the lookahead-restriction,
#                # because the symbol after ClassRanges is `]`.
#                # So the lookahead-restriction has no effect here.
#                s_exp_rhs = s_rhs
#
#            else:
#                (s0, rest) = (s_rhs[0], s_rhs[1:])
#
#                if type(s0) == SNT and s0.n == 'SourceCharacter':
#                    assert len(rest) == 1
#                    [but_not] = rest
#                    assert type(but_not) == A_but_not
#
#                    assert lats == (T_lit(c='^'),)
#
#                    # Just add the lookahead-restriction to the but-not.
#                    s_exp_rhs = [s0, A_but_not(but_not.b + lats)]
#
#                elif this_grammar.symbol_can_only_start_with(s0, lats):
#                    # This RHS is prevented by the NSW/LAX.
#                    # Don't add to s_exp_rhss
#                    continue
#
#                else:
#                    sub_lats = [
#                        lat
#                        for lat in lats
#                        if this_grammar.symbol_can_start_with(s0, lat)
#                    ]
#                    s0m = this_grammar.symbol_variant_that_doesnt_start_with(s0, sub_lats, level+1)
#                    s_exp_rhs = [s0m] + rest
#            s_exp_rhss.append(s_exp_rhs)
#
#        this_grammar.exp_prodns[nsw_s.n] = s_exp_rhss
#
#        return nsw_s
#
#    # --------------------------------------------
#
#    def symbol_can_only_start_with(this_grammar, s, lats):
#        # Return a boolean indicating whether EVERY phrase derivable from the symbol s
#        # begins with some lat in lats. (Not necessarily the same lat for all phrases.)
#
#        def fkt_matches_some_lat(fkt):
#            for lat in lats:
#                assert type(lat) == T_lit
#                lac = lat.c
#                if ' ' in lac:
#                    if lac == 'async nLTh function':
#                        if this_grammar.fkt_matches_lac(fkt, 'async'):
#                            assert 0
#                        else:
#                            # not this lat
#                            pass
#                    else:
#                        assert 0, lac
#                elif this_grammar.fkt_matches_lac(fkt, lac):
#                    return True
#                else:
#                    # not this lat, but maybe another
#                    pass
#            # No lat
#            return False
#
#        if type(s) in [T_lit, T_named]:
#            print('--', s, lats)
#            return fkt_matches_some_lat(s)
#
#        assert type(s) == SNT
#        first1_of_s = this_grammar.firstk_for_nt_named_[s.n][1]
#        first2_of_s = this_grammar.firstk_for_nt_named_[s.n][2]
#
#        for fk in first1_of_s:
#            assert isinstance(fk, tuple)
#            assert len(fk) == 1
#            (fkt,) = fk
#            if fkt_matches_some_lat(fkt):
#                # good so far
#                pass
#            else:
#                # Some phrase (beginning with fkt) does not start with any lat in lats.
#                return False
#
#        return True
#
#    def symbol_can_start_with(this_grammar, s, lat):
#        # Return a boolean indicating whether SOME phrase derivable from the symbol s
#        # begins with the lookahead-terminal lat.
#        #
#        # A general solution to this question would be fairly involved.
#        # Luckily, we don't need a general solution,
#        # we only need one that works for EcmaScript.
#
#        # -------------------------
#
#        # ES-specific assertions:
#        assert type(lat) == T_lit
#        assert lat.c in ['^', '{', 'class', 'function', 'let', 'let [', 'async nLTh function']
#
#        if ' ' in lat.c:
#            assert type(s) == SNT
#            if lat.c == 'let [':
#                first2_of_s = this_grammar.firstk_for_nt_named_[s.n][2]
#                assert (T_named(n='IdentifierName'), T_lit(c='[')) in first2_of_s
#                return True
#            elif lat.c == 'async nLTh function':
#                # print()
#                # print(s)
#                first2_of_s = this_grammar.firstk_for_nt_named_[s.n][2]
#                for f2 in first2_of_s:
#                    if len(f2) < 2: continue
#                    (a,b) = f2
#                    if this_grammar.fkt_matches_lac(a, 'async') and this_grammar.fkt_matches_lac(b, 'function'):
#                        return True
#                return False
#            else:
#                assert 0
#        else:
#            if type(s) in [T_lit, T_u_p, T_named]:
#                return this_grammar.fkt_matches_lac(s, lat.c)
#                
#            elif type(s) == SNT:
#                first1_of_s = this_grammar.firstk_for_nt_named_[s.n][1]
#                for fk in first1_of_s:
#                    assert isinstance(fk, tuple)
#                    assert len(fk) == 1
#                    (fk,) = fk
#                    if this_grammar.fkt_matches_lac(fk, lat.c):
#                        return True
#                    else:
#                        # lat doesn't match *this* fk, but it might match another
#                        pass
#                # lat doesn't match any fk in first1_of_s
#                return False
#
#            else:
#                assert 0, s
#
#
#    def fkt_matches_lac(this_grammar, fkt, lac):
#        # Return True iff firstk-terminal fkt matches lookahead-chars lac.
#        assert ' ' not in lac
#
#        if type(fkt) == T_lit:
#            return (fkt.c == lac)
#
#        elif type(fkt) == T_u_p:
#            assert fkt.p is None
#            assert lac == '^'
#            return True
#
#        elif type(fkt) == T_named:
#            if fkt.n == 'IdentifierName':
#                if lac in ['async', 'class', 'function', 'let']:
#                    return True
#                elif lac == '{':
#                    return False
#                else:
#                    assert 0, lac
#
#            elif fkt.n in [
#                'NumericLiteral', 'StringLiteral', 'RegularExpressionLiteral',
#                'NoSubstitutionTemplate', 'TemplateHead',
#            ]:
#                assert lac in ['{', 'async', 'class', 'function', 'let'], lac
#                return False
#
#            else:
#                assert 0, fkt
#
#        else:
#            assert 0, fkt

#    # XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#
#    def lax_replacement(this_grammar, lax, s):
#        # Looking at the language derivable from symbol s,
#        # and looking at the lookahead-constraint mandated by lax,
#        # distinguish cases:
#        # -- every phrase in the language satisfies the constraint
#        #    (i.e., the constraint is redundant here, can be discarded).
#        # -- no phrase in the language satisfies the constraint
#        #    (i.e., this alternative must be pruned).
#        # -- some do, some don't.
#        #    (i.e., use a restricted variant of the symbol)
#        #    subcase: 
#        # (Assumes that every phrase in the language is long enough
#        # to make this determination.)
#
#        if type(s) == SNT:
#            # if s.n == 'SourceCharacter': assert 0
#
#            s_rhss = this_grammar.exp_prodns[s.n]
#            for s_rhs in s_rhss:
#                if len(s_rhs) == 0:
#                    if s.n == 'ClassRanges~U' and lax.ts == (T_lit(c='^'),) and exp_lhs == 'CharacterClass~U':
#                        this_rhs_says = 'every'
#                    elif s.n == 'ClassRanges+U' and lax.ts == (T_lit(c='^'),) and exp_lhs == 'CharacterClass+U':
#                        this_rhs_says = 'every'
#                    else:
#                        assert 0, s
#                else:
#                    rthing = s_rhs[0]
#                    if type(rthing) == SNT:
#                        lax_replacement(lax, rthing)
#                    elif type(rthing) == T_named:
#                        if lax.ts == (T_lit(c='{'),) and rthing.n in [
#                            'IdentifierName',
#                            'NumericLiteral',
#                            'StringLiteral',
#                            'RegularExpressionLiteral', # starts with /
#                            'NoSubstitutionTemplate',   # starts with `
#                            'TemplateHead',             # starts with `
#                        ]:
#                            this_rhs_says = 'every'
#                        else:
#                            assert 0, rthing
#                    elif type(rthing) == T_lit:
#                        # make the determination
#                        if any(
#                            t == rthing
#                            for t in lax.ts
#                        ):
#                            this_rhs_says = 'none'
#                        elif all(
#                            type(t) == T_lit and t.c != rthing.c
#                            for t in lax.ts
#                        ):
#                            this_rhs_says = 'every'
#                        else:
#                            assert 0, rthing
#                    elif type(rthing) == T_u_p:
#                        assert lax.ts == (T_lit(c='^'),)
#                        this_rhs_says = 'some'
#                    else:
#                        assert 0, rthing
#        else:
#            assert 0, s
#
#        return [lax, s]
#        return [s]

    # --------------------------------------------------------------------------

    def print_exp_prodns(this_grammar):
        stderr('print_exp_prodns ...')
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

    def generate_LR0_automaton(this_grammar):
        stderr('generate_LR0_automaton ...')

        n_conflicts = 0

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
                for (rposn, rthing) in enumerate(this_item.rhs):
                    if rposn < this_item.dot_posn: continue

                    t = type(rthing)
                    if t in [A_but_only_if, A_but_not, A_no_LT]:
                        pass

                    elif t in [LAX,LAI]:
                        assert current_lax is None
                        current_lax = rthing

                    elif t in terminal_types:
                        if current_lax is not None:
                            assert this_item.lax_is_satisfied_by_terminal(current_lax, rthing)
                            current_lax = None

                        next_item = LR0_Item(this_item.lhs, this_item.rhs, rposn+1)
                        yield (rthing, next_item)
                        break # don't look at any further things in the rhs

                    elif t == SNT:
                        nt = rthing
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
                        yield (rthing, next_item)
                        break # don't look at any further things in the rhs

                    else:
                        assert 0, rthing

            def lax_is_satisfied_by_terminal(this_item, lax, terminal):
                return True
                # --------------------
                if lax.ts == (T_lit('let ['),) and terminal == T_lit(';'):
                    return True
                assert 0, (lax, terminal)

            def lax_plus_rhs(this_item, lax, rhs):
                rthing = rhs[0]
                if type(rthing) in terminal_types:
                    for lax_thing in lax.ts:
                        assert type(lax_thing) == T_lit
                        if type(lax_thing) != type(rthing):
                            pass
                        elif lax_thing == rthing:
                            # The LAX prohibits the first symbol of the rhs
                            return None
                        elif ' ' in lax_thing.c:
                            pieces = lax_thing.c.split()
                            assert pieces[0] != rthing.c

                    # The LAX does not prohibit the first symbol of the rhs.
                    # Therefore, it is redundant.
                    return rhs
                elif type(rthing) == SNT:
                    # Should we determine how lax compares to rhing's language?
                    return [lax] + rhs
                else:
                    assert 0, rthing
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
                    len(this_state.final_items) > 0 and len(this_state.transitions) > 0
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

        # ------------------------------------------------------------

        t_start = time.time()

        item0 = LR0_Item(None, (this_grammar.start_symbol,), 0)
        lr0 = DFA.Automaton(item0, LR0_State)

        t_end = time.time()
        t_elapsed = t_end - t_start
        stderr(
            "LR0 machine constructed (in %d sec) with %d states and %d conflicts" %
            (t_elapsed, len(lr0.state_for_kernel_), n_conflicts)
        )

        stderr("printing automaton...")
        filename = '%s_automaton' % this_grammar.name
        f = shared.open_for_output(filename)
        lr0.print(f, stringify_rthing)
        stderr("done")

        # ------------------------------------------------------------

        class LA_Item(namedtuple('_LA_Item', 'choice stacklet')):
            def each_transition(this_item):

                def simulate_reduction(stacklet, lr0_item):
                    if 0:
                        print()
                        print('simulate_reduction...')
                        print('    ', stacklet)
                        print('    ', lr0_item)

                    # assert lr0_item.dot_posn == len(lr0_item.rhs)
                    # Thats usually true, but not if the last rthing
                    # in the rhs is an annotation.

                    n_symbols_in_rhs = sum(
                        1
                        for rthing in lr0_item.rhs
                        if type(rthing) == SNT or type(rthing) in terminal_types
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

                (choice, stacklet) = this_item
                top_lr0_state = stacklet[-1]
                assert isinstance(top_lr0_state, LR0_State)
                for lr0_item in top_lr0_state.final_items:
                    next_choice = ('r',lr0_item) if choice is None else choice
                    for next_stacklet in simulate_reduction(stacklet, lr0_item):
                        next_item = LA_Item(next_choice, next_stacklet)
                        yield (None, next_item)

                for (X, next_lr0_state) in sorted(top_lr0_state.transitions.items()):
                    if type(X) == SNT: continue
                    assert type(X) in terminal_types
                    next_choice = ('s',X) if choice is None else choice
                    next_stacklet = simulate_shift(stacklet, X, next_lr0_state)
                    next_item = LA_Item(next_choice, next_stacklet)
                    yield (X, next_item)

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

        return

        # go to conflicted states and generate a lookahead automaton
        # (to allow you to decide between conflicting states)
        for state in lr0.state_for_kernel_.values():
            if not state.has_conflict: continue
            stderr("state #%d has a conflict" % state.number)

            max_stacklet_len = 0
            stacklet = (state,)
            la_item0 = LA_Item(None, stacklet)
            state.la_automaton = DFA.Automaton(la_item0, LA_State)
            stderr("    LA automaton has %d states" %
                len(state.la_automaton.state_for_kernel_)
            )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def each_params_setting(params):
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

class keydefaultdict(defaultdict):
    # http://stackoverflow.com/questions/2912231/
    def __missing__(self, key):
        if self.default_factory is None:
            raise KeyError( key )
        else:
            ret = self[key] = self.default_factory(key)
            return ret

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

# vim: sw=4 ts=4 expandtab columns=85
