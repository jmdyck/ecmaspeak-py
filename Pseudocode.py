#!/usr/bin/python3

# ecmaspeak-py/Pseudocode.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, time, math
from collections import defaultdict

from HTML import HNode
from Pseudocode_Parser import Pseudocode_Parser, ANode
import emu_grammars
import shared
from shared import spec, stderr

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_stuff_with_pseudocode():
    create_all_parsers()
    analyze_sections()
    check_emu_alg_coverage()
    check_emu_eqn_coverage()
    report_all_parsers()

    check_sdo_coverage()

def create_all_parsers():

    global emu_eqn_parser
    emu_eqn_parser = Pseudocode_Parser('emu_eqn')

    global inline_sdo_parser
    inline_sdo_parser = Pseudocode_Parser('inline_SDO')

    global ee_parser
    ee_parser = Pseudocode_Parser('early_error')

    global emu_alg_parser
    emu_alg_parser = Pseudocode_Parser('emu_alg')

def report_all_parsers():
    emu_eqn_parser.report()
    inline_sdo_parser.report()
    ee_parser.report()
    emu_alg_parser.report()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_emu_eqn_coverage():
    # Check that every <emu-eqn> that should have been parsed was parsed.
    stderr("check_emu_eqn_coverage...")

    for emu_eqn in spec.doc_node.each_descendant_named('emu-eqn'):
        st = emu_eqn.inner_source_text()
        if '=' not in st:
            # The content is at best a formula or expression;
            # it doesn't define anything.
            # I suppose I could parse it for conformance to {EXPR},
            # but to what end?
            # Skip it.
            continue

        if 'aoid' not in emu_eqn.attrs:
            # There are a few of these:
            #     abs(_k_) &lt; abs(_y_) and _x_-_k_ = _q_ &times; _y_
            #     floor(_x_) = _x_-(_x_ modulo 1)
            #     MonthFromTime(0) = 0
            #     WeekDay(0) = 4
            #     _t_<sub>local</sub> = _t_
            #     _a_ =<sub>CF</sub> _b_
            #     _comparefn_(_a_, _b_) = 0
            # They aren't definitions.
            # Skip it.
            continue

        assert emu_eqn.parent.element_name == 'emu-clause'
        assert emu_eqn.parent.section_kind == 'catchall'

        assert hasattr(emu_eqn, '_syntax_tree')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_emu_alg_coverage():
    stderr("check_emu_alg_coverage...")

    for emu_alg in spec.doc_node.each_descendant_named('emu-alg'):

        assert emu_alg.parent.element_name in ['emu-clause', 'emu-annex', 'emu-note', 'td', 'li']
        # print(emu_alg.parent.element_name)
        # 1758 emu-clause
        #   56 emu-annex
        #    4 emu-note
        #    3 td
        #    1 li

        assert hasattr(emu_alg, '_syntax_tree')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_sections():
    stderr('analyze_sections...')

    spec.info_for_op_named_ = {}

    for section in spec.doc_node.each_descendant_that_is_a_section():

        if section.section_kind == 'early_errors':
            analyze_early_errors_section(section)

        elif section.section_kind == 'syntax_directed_operation':
            analyze_sdo_section(section)
        else:
            analyze_other_section(section)

        # ------------------------------------------------------------

        # Ensure that we've parsed every <emu-alg>
        # for which this is the closet-containing section.
        # (Eventually, these should be reached by 'normal' means.)
        for bc in section.block_children:
            for emu_alg in bc.each_descendant_named('emu-alg'):

                if hasattr(emu_alg, '_syntax_tree'):
                    # already done
                    continue

                if spec.text.startswith(
                    (
                        '\n      1. Top-level step',
                        # 5.2 Algorithm Conventions
                        # This is just showing the format of algorithms,
                        # so it's not meant to be parsable.

                        '\n            5. Otherwise, let ',
                        '\n              5. Otherwise, let ', # PR 1515 BigInt
                        # 7.1.12.1 NumberToString
                        # The is unparsable because the grammar doesn't
                        # allow an "Otherwise" without a preceding "If",
                        # and I don't want to warp the grammar to allow it.
                    ),
                    emu_alg.inner_start_posn,
                    emu_alg.inner_end_posn
                ):
                    # unparsable, so don't try
                    emu_alg._syntax_tree = None
                    continue

                parse_emu_alg(emu_alg)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_early_errors_section(section):

    # XXX prose 'superstructure' outside early error rules:
    #
    # 12.2.6.1
    # sec-object-initializer-static-semantics-early-errors:
    # extra paragraph that constrains application of subsequent emu-grammar + ul
    #
    # 13.7.5.1
    # sec-for-in-and-for-of-statements-static-semantics-early-errors:
    # extra paragraph that is logically scoped to two bullets of three,
    #
    # See old bug 4378: https://tc39.github.io/archives/bugzilla/4378/

    assert not section.inline_child_element_names

    for child in section.block_children:
        if child.element_name == 'emu-grammar':
            curr_emu_grammar = child
        elif child.element_name == 'ul':
            for li in child.children:
                if li.element_name == 'li':
                    tree = ee_parser.parse_and_handle_errors(li.start_posn, li.end_posn)
                    li._syntax_tree = tree
            # XXX connect production with child

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_sdo_section(section):

    assert section.section_kind == 'syntax_directed_operation'

    # XXX: See define_ops_from_sdo_section() in static_type_analysis.py
    # Merge them somehow?

    if section.section_num.startswith('B.'):
        # Taking Annex B into account is difficult,
        # because it modifies the main-body grammar,
        # so RHS-indexes aren't always the same.
        # XXX For now, just skip it.
        #! (STA has it)
        return

    if section.section_title == 'Static Semantics: HasCallInTailPosition':
        assert len(section.block_children) == 2
        assert section.block_children[0].element_name == 'p'
        assert section.block_children[1].element_name == 'emu-note'
        assert len(section.section_children) == 2
        return

    sdo_name = section.ste['op_name']

    # ------------------------------------------------------------------------------

    if section.section_title == 'Static Semantics: NumberValueNotEverReferenced':
        # In the BigInt proposal, it has a <ul> defining "significant digit" and then <p> instead of <emu-alg>.
        assert section.bcen_list == ['p', 'ul', 'emu-grammar', 'p', 'emu-grammar', 'p']
        return
    elif section.section_title == 'Static Semantics: BigIntValueNotEverReferenced':
        # In the BigInt proposal, it has <ul> instead of <emu-alg>
        assert section.bcen_list == ['emu-grammar', 'ul', 'emu-grammar', 'ul']
        return

    if 'emu-grammar' in section.bcen_set:
        if section.section_title == 'Static Semantics: NumericValue':
            # In the BigInt proposal, it has a <ul> defining "significant digit"
            assert section.bcen_set == {'emu-grammar', 'emu-alg', 'ul', 'p'}
        else:
            assert section.bcen_set <= set(['emu-grammar', 'emu-alg', 'emu-note', 'emu-see-also-para', 'emu-table', 'p'])
        # Each <emu-grammar> + <emu-alg> pair in an SDO unit.

        for (i,c) in enumerate(section.block_children):
            if c.element_name == 'emu-grammar':
                next_c = section.block_children[i+1]
                handle_composite_sdo(sdo_name, c, next_c)

    elif 'ul' in section.bcen_set:
        assert section.bcen_set <= set(['ul', 'p', 'emu-table', 'emu-note'])
        # Each <li> in the <ul> is an "inline SDO".

        for ul in section.block_children:
            if ul.element_name != 'ul': continue

            if re.match(r'^<li>\n +it is not `0`; or\n +</li>$', ul.children[1].source_text()):
                # This is the <ul> for 'significant digit' at the end of 
                # 7.1.3.1.1 Runtime Semantics: MV
                # and
                # 11.8.3.1 Static Semantics: MV
                # We're not interested in it.
                assert section.section_title in ['Runtime Semantics: MV', 'Static Semantics: MV']
                continue

            for child in ul.children:
                if child.element_name == '#LITERAL':
                    assert child.is_whitespace()
                elif child.element_name == 'li':
                    handle_inline_sdo(child, sdo_name)
                else:
                    assert 0, child.element_name

    elif 'emu-alg' in section.bcen_set:
        assert section.bcen_set <= set(['emu-alg', 'p', 'emu-note'])
        # Each <p> + <emu-alg> pair is an SDO unit.
        assert sdo_name in ['Evaluation', 'regexp-Evaluate']

        # print(section.bcen_str)
        for (i,c) in enumerate(section.block_children):
            if c.element_name == 'p':
                if c.inner_source_text() == 'With parameter _direction_.':
                    continue

                emu_alg = section.block_children[i+1]
                assert emu_alg.element_name == 'emu-alg'
                handle_composite_sdo(sdo_name, c, emu_alg)

    else:
        print(section.section_num, section.section_title, section.section_id)
        print(section.bcen_str)
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_other_section(section):

    for child in section.block_children:
        if child.element_name == 'emu-eqn':
            handle_emu_eqn(child)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_composite_sdo(sdo_name, grammar_arg, algo_arg):

    # ---------------------------
    # grammar_arg -> emu_grammar:

    if grammar_arg.element_name == 'emu-grammar':
        emu_grammar = grammar_arg

    elif grammar_arg.element_name == 'p':
        (emu_grammars, text) = extract_grammars(grammar_arg)
        assert len(emu_grammars) == 1
        [emu_grammar] = emu_grammars

        if text == 'The production <G>, where @ is one of the bitwise operators in the productions above, is evaluated as follows:':
            assert emu_grammar.attrs.get('type', 'reference') == 'example'
            assert emu_grammar.inner_source_text() == 'A : A @ B'
            # It isn't really an example, and yet it isn't a proper production.
            # Because it's marked as an 'example', it didn't get a 'summary' property
            # over in check_non_defining_prodns().
            # Hard-code the summary.
            emu_grammar.summary = [
                ('BitwiseANDExpression', 1, []),
                ('BitwiseXORExpression', 1, []),
                ('BitwiseORExpression',  1, []),
            ]

        elif text == 'The production <G> evaluates as follows:':
            pass

        else:
            assert 0, text

    else:
        assert 0, grammar_arg.element_name

    # -----------------
    # algo_arg

    if algo_arg.element_name == 'emu-alg':
        parse_emu_alg(algo_arg)
    elif algo_arg.element_name == 'p':
        assert algo_arg.inner_source_text().startswith('Is evaluated in exactly the same manner as')
    else:
        assert 0, algo_arg.element_name

    # ----------

    op_add_defn('SDO', sdo_name, emu_grammar, algo_arg)

# ------------------------------------------------------------------------------

def extract_grammars(x):
    emu_grammars = []
    text = ''
    for c in x.children:
        if c.element_name == 'emu-grammar':
            emu_grammars.append(c)
            text += '<G>'
        else:
            text += c.source_text()
    return (emu_grammars, text.strip())

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_inline_sdo(li, section_sdo_name):
    assert li.element_name == 'li'

    li._syntax_tree = inline_sdo_parser.parse_and_handle_errors(li.start_posn, li.end_posn)

    LI = li._syntax_tree
    assert LI.prod.lhs_s == '{LI}'
    [ISDO_RULE] = LI.children
    assert ISDO_RULE.prod.lhs_s == '{ISDO_RULE}'

    emu_grammar_hnodes = [* li.each_child_named('emu-grammar')]
    emu_grammar_anodes = [
        child
        for child in ISDO_RULE.children
        if child.prod.lhs_s == '{h_emu_grammar}'
    ]
    assert len(emu_grammar_hnodes) == len(emu_grammar_anodes)
    for (emu_grammar_hnode, emu_grammar_anode) in zip(emu_grammar_hnodes, emu_grammar_anodes):
        emu_grammar_anode._hnode = emu_grammar_hnode

    rule_sdo_names = []
    rule_grammars = []
    rule_expr = None

    for child in ISDO_RULE.children:
        cl = child.prod.lhs_s
        if cl == '{ISDO_NAME}':
            [cap_word] = child.children
            [rule_sdo_name] = cap_word.children
            if section_sdo_name == 'TV and TRV':
                assert rule_sdo_name in ['TV', 'TRV']
            else:
                assert rule_sdo_name == section_sdo_name
            rule_sdo_names.append(rule_sdo_name)
        elif cl == '{h_emu_grammar}':
            rule_grammars.append(child._hnode)
        elif cl == '{nonterminal}':
            rule_grammars.append(child)
        elif cl == '{EXPR}':
            assert rule_expr is None
            rule_expr = child
        elif cl == '{NAMED_OPERATION_INVOCATION}':
            if 'Note that if {NAMED_OPERATION_INVOCATION}' in ISDO_RULE.prod.rhs_s:
                # skip it
                pass
            else:
                assert rule_expr is None
                rule_expr = child
        else:
            assert 0, cl

    assert 0 < len(rule_sdo_names) <= 2
    assert 0 < len(rule_grammars) <= 5
    for rule_sdo_name in rule_sdo_names:
        for rule_grammar in rule_grammars:
            op_add_defn('SDO', rule_sdo_name, rule_grammar, rule_expr)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_emu_eqn(emu_eqn):
    assert emu_eqn.element_name == 'emu-eqn'

    aoid = emu_eqn.attrs['aoid']
    if aoid in ['DateFromTime', 'WeekDay']:
        assert 'id' not in emu_eqn.attrs
    else:
        id = emu_eqn.attrs['id']
        if aoid == 'DayFromYear':
            assert id == 'eqn-DaysFromYear' # "Day" vs "Days"
        else:
            assert id == 'eqn-' + aoid

    tree = emu_eqn_parser.parse_and_handle_errors(emu_eqn.inner_start_posn, emu_eqn.inner_end_posn)
    emu_eqn._syntax_tree = tree

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_alg(emu_alg):
    assert emu_alg.element_name == 'emu-alg'
    assert not hasattr(emu_alg, '_syntax_tree')
    tree = emu_alg_parser.parse_and_handle_errors(
        emu_alg.inner_start_posn,
        emu_alg.inner_end_posn
    )
    emu_alg._syntax_tree = tree

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Operation:
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind
        self.definitions = []

def op_add_defn(op_kind, op_name, discriminator, algo):
    assert type(op_name) == str
    assert (
        isinstance(discriminator, HNode) and discriminator.element_name == 'emu-grammar'
        or
        isinstance(discriminator, ANode) and discriminator.prod.lhs_s == '{nonterminal}'
    )

    if op_name in spec.info_for_op_named_:
        op_info = spec.info_for_op_named_[op_name]
        assert op_info.kind == op_kind
    else:
        op_info = Operation(op_name, op_kind)
        spec.info_for_op_named_[op_name] = op_info

    assert (
        isinstance(algo, ANode) and algo.prod.lhs_s in ['{EXPR}', '{NAMED_OPERATION_INVOCATION}']
        or
        isinstance(algo, HNode) and algo.element_name in ['emu-alg', 'p']
    )

    op_info.definitions.append( (discriminator, algo) )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_sdo_coverage():
    stderr('check_sdo_coverage...')
    spec.sdo_coverage_map = {}

    # collect sdo_coverage_info:
    for (op_name, op_info) in spec.info_for_op_named_.items():
        if op_info.kind == 'SDO':

            if op_name not in spec.sdo_coverage_map:
                spec.sdo_coverage_map[op_name] = {}

            for (discriminator, emu_alg) in op_info.definitions:
                if isinstance(discriminator, ANode):
                    assert discriminator.prod.lhs_s == '{nonterminal}'
                    assert discriminator.source_text() == '|HexDigit|'
                    discriminator.summary = [] # XXX?

                for (lhs_nt, def_i, optionals) in discriminator.summary:
                    if lhs_nt not in spec.sdo_coverage_map[op_name]:
                        spec.sdo_coverage_map[op_name][lhs_nt] = {}
                    if def_i not in spec.sdo_coverage_map[op_name][lhs_nt]:
                        spec.sdo_coverage_map[op_name][lhs_nt][def_i] = []
                    spec.sdo_coverage_map[op_name][lhs_nt][def_i].append(optionals)

    analyze_sdo_coverage_info()

# ------------------------------------------------------------------------------

def analyze_sdo_coverage_info():
    coverage_f = shared.open_for_output('sdo_coverage')
    def put(*args): print(*args, file=coverage_f)

    for (sdo_name, coverage_info_for_this_sdo) in sorted(spec.sdo_coverage_map.items()):

        if sdo_name == 'Contains':
            # XXX can we do anything useful here?
            # we could check for conflicting defs
            continue

        nt_queue = sorted(coverage_info_for_this_sdo.keys())
        def queue_ensure(nt):
            if nt not in nt_queue: nt_queue.append(nt)

        for lhs_nt in nt_queue:
            # print('    ', lhs_nt)

            nt_info = emu_grammars.info_for_nt_[lhs_nt]
            assert 'A' in nt_info.def_occs
            (_, _, def_rhss) = nt_info.def_occs['A']

            for (def_i, def_rhs) in enumerate(def_rhss):
                GNTs = [r for r in def_rhs if r.T == 'GNT']
                oGNTs = [gnt for gnt in GNTs if gnt.o]
                nGNTs = [gnt for gnt in GNTs if not gnt.o]

                for opt_combo in each_opt_combo(oGNTs):
                    opt_combo_str = ''.join(omreq[0] for (nt, omreq) in opt_combo)
                    rules = sdo_rules_that_handle(sdo_name, lhs_nt, def_i, opt_combo)
                    if len(rules) == 1:
                        # great
                        pass
                    elif len(rules) > 1:
                        put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} {opt_combo_str} is handled by {len(rules)} rules!")
                    elif is_sdo_coverage_exception(sdo_name, lhs_nt, def_i):
                        # okay
                        pass
                    else:
                        nts = [gnt.n for gnt in nGNTs] + required_nts_in(opt_combo)
                        if len(nts) == 1:
                            # The rule for chain productions applies.
                            # So recurse on the rhs non-terminal.
                            [nt] = nts

                            # DEBUG:
                            # put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} chains to {nt}")
                            # That creates a lot of output, but it's really useful
                            # when you're trying to figure out why "needs a rule" messages appear.

                            queue_ensure(nt)
                        else:
                            put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} {opt_combo_str} needs a rule")

    coverage_f.close()

def each_opt_combo(oGNTs):
    N = len(oGNTs)
    if N == 0:
        yield []
    elif N == 1:
        [a] = oGNTs
        yield [(a.n, 'omitted' )]
        yield [(a.n, 'required')]
    elif N == 2:
        [a, b] = oGNTs
        yield [(a.n, 'omitted' ), (b.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'required')]
    elif N == 3:
        [a, b, c] = oGNTs
        yield [(a.n, 'omitted' ), (b.n, 'omitted' ), (c.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'omitted' ), (c.n, 'required')]
        yield [(a.n, 'omitted' ), (b.n, 'required'), (c.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'required'), (c.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'omitted' ), (c.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'omitted' ), (c.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'required'), (c.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'required'), (c.n, 'required')]
    else:
        assert 0

def required_nts_in(opt_combo):
    return [nt for (nt, omreq) in opt_combo if omreq == 'required']

def sdo_rules_that_handle(sdo_name, lhs_nt, def_i, opt_combo):
    coverage_info_for_this_sdo = spec.sdo_coverage_map[sdo_name]
    coverage_info_for_this_nt = coverage_info_for_this_sdo.get(lhs_nt, {})
    if def_i not in coverage_info_for_this_nt: return []
    list_of_opt_covers = coverage_info_for_this_nt[def_i]
    covers = []
    for opt_cover in list_of_opt_covers:
        # print(opt_cover, covers_opt_combo(opt_cover, opt_combo))
        if covers_opt_combo(opt_cover, opt_combo):
            covers.append(opt_cover)
    return covers

def covers_opt_combo(opt_cover, opt_combo):
    assert len(opt_cover) == len(opt_combo)
    for (cover_item, combo_item) in zip(opt_cover, opt_combo):
        assert cover_item[0] == combo_item[0]
        assert cover_item[1] in ['omitted', 'required', 'either']
        assert combo_item[1] in ['omitted', 'required']
        if cover_item[1] == combo_item[1]:
            # easy
            pass
        elif cover_item[1] == 'either':
            # covers either
            pass
        else:
            # incompatible
            return False
    return True

def is_sdo_coverage_exception(sdo_name, lhs_nt, def_i):
    # Looking at the productions that share a LHS
    # (or equivalently, the RHSs of a multi-production),
    # it's typically the case that if an SDO can be invoked on one,
    # then it can be invoked on all.
    # And thus, if you see an SDO defined on one,
    # you should expect to see it defined on all,
    # either explicitly, or implicitly via chain productions.
    #
    # This function identifies exceptions to that rule of thumb.

    if sdo_name == 'CharacterValue' and lhs_nt == 'ClassEscape' and def_i == 2:
        # Invocations of this SDO on ClassAtom and ClassAtomNoDash
        # are guarded by `IsCharacterClass ... is *false*`.
        # This excludes the `ClassEscape :: CharacterClassEscape` production.
        return True

    if (
        sdo_name == 'CoveredParenthesizedExpression'
        and
        lhs_nt == 'CoverParenthesizedExpressionAndArrowParameterList'
        and
        def_i != 0
    ):
        # For this SDO, we're guaranteed (by early error) that rhs must be def_i == 0,
        # so the SDO doesn't need to be defined for def_i != 0.
        return True

    if sdo_name == 'DefineMethod' and lhs_nt == 'MethodDefinition' and def_i != 0:
        # "Early Error rules ensure that there is only one method definition named `"constructor"`
        # and that it is not an accessor property or generator definition."
        # (or AsyncMethod)
        # See SpecialMethod.
        return True

    if sdo_name == 'Evaluation' and lhs_nt == 'ClassDeclaration' and def_i == 1:
        # "ClassDeclaration : `class` ClassTail</emu-grammar>
        # only occurs as part of an |ExportDeclaration| and is never directly evaluated."
        return True

    if sdo_name == 'HasName':
        # Invocations of this SDO are guarded by `IsFunctionDefinition of _expr_ is *true*`,
        # so the SDO doesn't need to be defined for most kinds of expr.
        # Assume that it's defined for all that need it.
        return True

    if sdo_name == 'NamedEvaluation':
        # NamedEvaluation is invoked on |Initializer| and |AssignmentExpression|,
        # which are fairly general, except that it's only invoked on nodes
        # for which IsAnonymousFunctionDefinition() is true,
        # which implies that IsFunctionDefition is true and HasName is false.
        # return lhs_nt not in [
        #     'ArrowFunction',
        #     'AsyncArrowFunction',
        #     'FunctionExpression',
        #     'GeneratorExpression',
        #     'AsyncGeneratorExpression',
        #     'ClassExpression',
        #     'AsyncFunctionExpression',
        # ]
        # As above, assume it's defined for all that need it.
        return True

    if sdo_name == 'IsConstantDeclaration' and lhs_nt == 'ExportDeclaration' and def_i in [0,1,2,3]:
        # LexicallyScopedDeclarations skips these, so IsConstantDeclaration won't be invoked on them.
        return True

    if (
        sdo_name in ['PropName', 'PropertyDefinitionEvaluation']
        and 
        lhs_nt == 'PropertyDefinition'
        and
        def_i == 1
    ):
        # "Use of |CoverInitializedName| results in an early Syntax Error in normal contexts..."
        return True

    # ----------

    if (
        sdo_name == 'Evaluation'
        and
        lhs_nt in [
            'BitwiseANDExpression',
            'BitwiseXORExpression',
            'BitwiseORExpression',
        ]
        and
        def_i == 1
    ):
        # This is handled by the stupid "A : A @ B" rule.
        return True

    return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# import cProfile
# cProfile.run('main()', '_prof')

# vim: sw=4 ts=4 expandtab
