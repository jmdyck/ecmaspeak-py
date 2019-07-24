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
    parse_all_pseudocode()
    collect_operation_info()
    check_sdo_coverage()

def parse_all_pseudocode():
    parse_emu_eqns()
    parse_early_errors()
    parse_inline_sdo()
    parse_emu_algs()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_eqns():
    stderr()
    stderr("parse_emu_eqns...")

    emu_eqn_parser = Pseudocode_Parser('emu_eqn')

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

        aoid = emu_eqn.attrs['aoid']
        # id = emu_eqn.attrs['id']
        # assert (id == 'eqn-' + aoid) or (id == 'eqn-DaysFromYear' and aoid == 'DayFromYear')
        # 'id' not defined for 'DateFromTime'

        tree = emu_eqn_parser.parse_and_handle_errors(emu_eqn.inner_start_posn, emu_eqn.inner_end_posn)
        emu_eqn._syntax_tree = tree

    emu_eqn_parser.report()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_early_errors():
    stderr()
    stderr("parse_early_errors...")

    ee_parser = Pseudocode_Parser('early_error')

    # XXX prose 'superstructure' outside early error rules:
    #
    # sec-object-initializer-static-semantics-early-errors:
    # extra paragraph that constrains application of subsequent emu-grammar + ul
    #
    # sec-for-in-and-for-of-statements-static-semantics-early-errors:
    # extra paragraph that is logically scoped to two bullets of three,
    # but 
    # See old bug 4378: https://tc39.github.io/archives/bugzilla/4378/

    spec.early_error_map = defaultdict(list)

    for s in spec.doc_node.each_descendant_that_is_a_section():
        if s.section_kind == 'early_errors':
            assert not s.inline_child_element_names

            if 0:
                x = re.sub(r'\bemu-grammar ul\b', 'X X',
                        ' '.join(child.element_name for child in s.block_children)
                    )
                x = x.split()
                assert len(x) == len(s.block_children)
                for (block, x) in zip(s.block_children, x):
                    if x == 'X': continue
                    if block.element_name == 'emu-note': continue
                    print('--------------------------')
                    print(s.section_id)
                    print()
                    print(block.source_text())

            for block in s.block_children:
                if block.element_name == 'emu-grammar':
                    curr_emu_grammar = block
                elif block.element_name == 'ul':
                    for li in block.children:
                        if li.element_name == 'li':
                            tree = ee_parser.parse_and_handle_errors(li.start_posn, li.end_posn)
                            li._syntax_tree = tree
                    # XXX connect production with block
                    # spec.early_error_map[?] = block

    ee_parser.report()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_inline_sdo():
    stderr()
    stderr("parse_inline_sdo...")

    inline_sdo_parser = Pseudocode_Parser('inline_SDO')

    for s in spec.doc_node.each_descendant_that_is_a_section():
        if s.section_kind == 'syntax_directed_operation':
            for ul in s.block_children:
                if ul.element_name == 'ul':
                    if re.match(r'^<li>\n +it is not `0`; or\n +</li>$', ul.children[1].source_text()):
                        # "A digit is significant if ..." in "Runtime Semantics: MV" and "Static Semantics: MV"
                        continue
                    for child in ul.children:
                        if child.element_name == '#LITERAL':
                            assert child.is_whitespace()
                            continue

                        assert child.element_name == 'li'
                        tree = inline_sdo_parser.parse_and_handle_errors(child.start_posn, child.end_posn)
                        child._syntax_tree = tree

    inline_sdo_parser.report()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_algs():
    stderr()
    stderr("parse_emu_algs...")

    emu_alg_parser = Pseudocode_Parser('emu_alg')

    t_start = time.time()

    parse_count = 0

    def try_to_parse(start_posn, end_posn):
        nonlocal parse_count
        parse_count += 1
        if parse_count % 20 == 0:
            print('.', file=sys.stderr, end='')
            sys.stderr.flush()
        tree = emu_alg_parser.parse_and_handle_errors(start_posn, end_posn)
        return tree

    for emu_alg in spec.doc_node.each_descendant_named('emu-alg'):
        cc_section = emu_alg.closest_containing_section()
        if cc_section.section_title == 'Algorithm Conventions':
            # stderr("skipping Algorithm Conventions")
            continue
            # because some of the <emu-alg>s in that section aren't really parseable

        x = '\n            5. Otherwise, let '
        if spec.text[emu_alg.inner_start_posn:emu_alg.inner_start_posn+len(x)] == x:
            # stderr("skipping 5. Otherwise!")
            continue
            # because I can't parse an "Otherwise" without a preceding "If"
            # (NumberToString)

        if 1:
            tree = try_to_parse(emu_alg.inner_start_posn, emu_alg.inner_end_posn)
            emu_alg._syntax_tree = tree
        else:
            # used this when I was parsing individual lines:
            for mo in re.compile(r'(?m)^ +\d+\. .+\n').finditer(
                spec.text,
                emu_alg.inner_start_posn,
                emu_alg.inner_end_posn
            ):
                (line_start, line_end) = mo.span(0)
                try_to_parse(line_start, line_end)

    print(file=sys.stderr)

    t_end = time.time()
    stderr("parsing %d emu-algs took %d seconds" % (parse_count, t_end-t_start))

    emu_alg_parser.report()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def collect_operation_info():
    stderr('collect_operation_info...')

    spec.info_for_op_named_ = {}

    for section in spec.doc_node.each_descendant_that_is_a_section():

        if section.section_kind == 'syntax_directed_operation':
            collect_op_info_from_sdo_section(section)
        else:
            pass # XXX for now

# ------------------------------------------------------------------------------

def collect_op_info_from_sdo_section(section):

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
                assert next_c.element_name in ['emu-alg', 'p']
                if next_c.element_name == 'p':
                    assert next_c.inner_source_text().startswith('Is evaluated in exactly the same manner as')
                op_add_defn('SDO', sdo_name, c, next_c)

    elif 'ul' in section.bcen_set:
        assert section.bcen_set <= set(['ul', 'p', 'emu-table', 'emu-note'])
        # Each <li> in the <ul> is an "inline SDO".

        for ul in section.block_children:
            if ul.element_name != 'ul': continue
            for li in ul.children:
                if li.element_name != 'li': continue

                li_ist = li.inner_source_text().strip()
                if re.match(r'it is not `0`|there is a nonzero digit', li_ist):
                    # This is the <ul> for 'significant digit' at the end of 
                    # 7.1.3.1.1 Runtime Semantics: MV
                    # and
                    # 11.8.3.1 Static Semantics: MV
                    # We're not interested in it.
                    # print(section.section_num, section.section_title, section.section_id)
                    continue

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
                        if sdo_name == 'TV and TRV':
                            assert rule_sdo_name in ['TV', 'TRV']
                        else:
                            assert rule_sdo_name == sdo_name
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

    elif 'emu-alg' in section.bcen_set:
        assert section.bcen_set <= set(['emu-alg', 'p', 'emu-note'])
        # Each <p> + <emu-alg> pair is an SDO unit.
        assert sdo_name in ['Evaluation', 'regexp-Evaluate']

        # print(section.bcen_str)
        for (i,c) in enumerate(section.block_children):
            if c.element_name == 'p':
                (emu_grammars, text) = extract_grammars(c)

                if len(emu_grammars) == 0:
                    assert text == 'With parameter _direction_.'
                    # ignore it
                    continue

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

                    emu_alg = section.block_children[i+1]
                    assert emu_alg.element_name == 'emu-alg'
                    op_add_defn('SDO', sdo_name, emu_grammar, emu_alg)

                elif text in [
                    'The production <G> evaluates by returning the CharSet containing all Unicode code points included in the CharSet returned by |UnicodePropertyValueExpression|.',
                    'The production <G> evaluates by returning the CharSet containing all Unicode code points not included in the CharSet returned by |UnicodePropertyValueExpression|.',
                ]:
                    op_add_defn('SDO', sdo_name, emu_grammar, None)

                elif text == 'The production <G> evaluates as follows:':
                    emu_alg = section.block_children[i+1]
                    assert emu_alg.element_name == 'emu-alg'
                    op_add_defn('SDO', sdo_name, emu_grammar, emu_alg)

                else:
                    assert 0, text

    else:
        print(section.section_num, section.section_title, section.section_id)
        print(section.bcen_str)
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

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

class Operation:
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind
        self.definitions = []

def op_add_defn(op_kind, op_name, discriminator, emu_alg):
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
        isinstance(emu_alg, ANode) and emu_alg.prod.lhs_s in ['{EXPR}', '{NAMED_OPERATION_INVOCATION}']
        or
        isinstance(emu_alg, HNode) and emu_alg.element_name in ['emu-alg', 'p']
    )

    op_info.definitions.append( (discriminator, emu_alg) )

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
