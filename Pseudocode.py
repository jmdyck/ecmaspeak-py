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

    analyze_static_dependencies()
    check_sdo_coverage()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def create_all_parsers():
    global samex_parser
    samex_parser = Pseudocode_Parser('samex')

    global one_line_alg_parser
    one_line_alg_parser = Pseudocode_Parser('one_line_alg')

    global emu_eqn_parser
    emu_eqn_parser = Pseudocode_Parser('emu_eqn')

    global inline_sdo_parser
    inline_sdo_parser = Pseudocode_Parser('inline_SDO')

    global ee_parser
    ee_parser = Pseudocode_Parser('early_error')

    global emu_alg_parser
    emu_alg_parser = Pseudocode_Parser('emu_alg')

def report_all_parsers():
    samex_parser.report()
    one_line_alg_parser.report()
    emu_eqn_parser.report()
    inline_sdo_parser.report()
    ee_parser.report()
    emu_alg_parser.report()

def parse(hnode, what=None):
    assert isinstance(hnode, HNode)
    assert not hasattr(hnode, '_syntax_tree')

    # In most case, we parse the element's inner text.
    start_posn = hnode.inner_start_posn
    end_posn   = hnode.inner_end_posn

    if hnode.element_name == 'emu-alg':
        assert what is None
        parser = emu_alg_parser

    elif hnode.element_name == 'emu-eqn':
        assert what is None
        parser = emu_eqn_parser

    elif hnode.element_name == 'td':
        assert what is None
        parser = one_line_alg_parser

    elif hnode.element_name == 'p':
        assert what is None
        parser = samex_parser

    elif hnode.element_name == 'li':
        if what == 'early_error':
            parser = ee_parser
        elif what == 'inline_sdo':
            parser = inline_sdo_parser
        else:
            assert 0, what
        start_posn = hnode.start_posn
        end_posn = hnode.end_posn

    else:
        assert 0, hnode.element_name

    tree = parser.parse_and_handle_errors(start_posn, end_posn)
    hnode._syntax_tree = tree

    if tree is None:
        # cc_section = hnode.closest_containing_section()
        # stderr(f"Failed to parse <{hnode.element_name}> in {cc_section.section_num} {cc_section.section_title}")
        # (Messes up the "progress bar")
        pass

    return tree

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_emu_eqn_coverage():
    # Check that every <emu-eqn> that should have been parsed was parsed.
    stderr("check_emu_eqn_coverage...")

    for emu_eqn in spec.doc_node.each_descendant_named('emu-eqn'):
        st = emu_eqn.inner_source_text()
        if '=' not in st:
            # 67 of these.
            # The content is at best a formula or expression;
            # it doesn't define anything.
            # I suppose I could parse it for conformance to {EXPR},
            # but to what end?
            # Skip it.
            assert not hasattr(emu_eqn, '_syntax_tree')
            continue

        if 'aoid' not in emu_eqn.attrs:
            # There are a few of these:
            #     abs(_k_) &lt; abs(_y_) and _x_-_k_ = _q_ &times; _y_
            #     floor(_x_) = _x_-(_x_ modulo 1)
            #     60 &times; 60 &times; 24 &times; 1000 = 86,400,000
            #     MonthFromTime(0) = 0
            #     WeekDay(0) = 4
            #     _t_<sub>local</sub> = _t_
            #     _a_ =<sub>CF</sub> _b_
            #     _comparefn_(_a_, _b_) = 0
            # They aren't definitions.
            # Skip it.
            assert not hasattr(emu_eqn, '_syntax_tree')
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

    t_start = time.time()
    prev_top_level_num = ''

    for section in spec.doc_node.each_descendant_that_is_a_section():
        assert hasattr(section, 'ste')

        top_level_num = section.section_num.split('.')[0]
        if top_level_num != prev_top_level_num:
            stderr(f" {top_level_num}", end='', flush=True)
            prev_top_level_num = top_level_num

        global in_annex_b
        in_annex_b = (top_level_num == 'B')
        # This is kludgey, but it works.

        # ------------------------------------------------

        if section.section_kind == 'early_errors':
            analyze_early_errors_section(section)

        elif section.section_kind == 'syntax_directed_operation':
            analyze_sdo_section(section)

        elif section.section_kind in [
            'abstract_operation',
            'env_rec_method',
            'internal_method',
            'module_rec_method',
        ]:
            analyze_other_op_section(section)

        elif section.section_kind in [
            'CallConstruct',
            'CallConstruct_overload',
            'accessor_property',
            'anonymous_built_in_function',
            'function_property',
            'function_property_overload',
            'function_property_xref',
        ]:
            analyze_built_in_section(section)

        elif section.section_kind == 'changes':
            analyze_changes_section(section)

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

                parse(emu_alg)

    stderr()

    t_end = time.time()
    stderr(f"analyze_sections took {t_end-t_start:.2f} seconds")

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
            handle_early_error(curr_emu_grammar, child)
        elif child.element_name in ['p', 'emu-note']:
            pass
        else:
            assert 0, child.element_name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_sdo_section(section):

    assert section.section_kind == 'syntax_directed_operation'

    # XXX: See define_ops_from_sdo_section() in static_type_analysis.py
    # Merge them somehow?

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
                p_text = c.inner_source_text()
                if p_text == 'With parameter _direction_.':
                    continue

                if 'evaluates by returning' in p_text:
                    # branch is based before the merge of PR #1596.
                    continue

                if (
                    p_text.startswith('The production <emu-grammar')
                    and
                    (
                        p_text.endswith('</emu-grammar> evaluates as follows:')
                        or
                        p_text.endswith('is evaluated as follows:')
                    )
                ):
                    emu_alg = section.block_children[i+1]
                    assert emu_alg.element_name == 'emu-alg'
                    handle_composite_sdo(sdo_name, c, emu_alg)

                else:
                    # assert 0, p_text
                    # print('>', p_text)
                    pass
                    # skip it for now

    else:
        print(section.section_num, section.section_title, section.section_id)
        print(section.bcen_str)
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_other_op_section(section):
    assert 'op_name' in section.ste
    op_name = section.ste['op_name']

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        # 13 cases

        if op_name in ['ToBoolean', 'ToNumber', 'ToString', 'ToObject', 'RequireObjectCoercible']:
            assert section.bcen_str in ['p emu-table', 'emu-operation-header emu-table']
            # The op is defined by a table that splits on argument type.
            # The second cell in each row is a little algorithm,
            # but it's generally not marked as an emu-alg.
            emu_table = section.block_children[1]
            assert emu_table.element_name == 'emu-table'
            (_, table, _) = emu_table.children
            assert table.element_name == 'table'
            (_, tbody, _) = table.children
            for tr in tbody.each_child_named('tr'):
                (_, a, _, b, _) = tr.children 

                if a.element_name == 'th' and b.element_name == 'th':
                    assert a.inner_source_text().strip() == 'Argument Type'
                    assert b.inner_source_text().strip() == 'Result'
                    continue

                handle_tabular_op_defn(op_name, a, b)

        elif op_name == 'CreateImmutableBinding':
            # This is a bit odd.
            # The clause exists just to say that this definition doesn't exist.
            # discriminator = None # XXX get the discriminator!
            # emu_alg = None ?
            # handle_type_discriminated_op(op_name, section.section_kind, discriminator, emu_alg)
            pass

        elif op_name.startswith('Host') or op_name == 'LocalTZA':
            # These are host-defined ops, so we expect no alg.
            ensure_foo('abstract_operation', op_name)
            pass

        # PR 1515 BigInt:
        elif op_name.startswith('::'):
            # A mathematical operation that we merely constrain, via a bullet-list.
            ensure_foo('abstract_operation', op_name)
            pass

        # PR 1515 BigInt:
        elif op_name == 'StringToBigInt':
            # Apply other alg with changes, ick.
            ensure_foo('abstract_operation', op_name)

        else:
            assert 0, (section.section_num, section.section_title)

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        assert emu_alg.element_name == 'emu-alg'

        # The emu-alg is the 'body' of
        # (this definition of) the operation named by the section_title.

        if section.section_kind == 'abstract_operation':
            handle_solo_op(op_name, emu_alg)

        elif section.section_kind in [
            'env_rec_method',
            'module_rec_method',
            'internal_method',
        ]:
            # type-discriminated operation
            discriminator = None # XXX get the discriminator!
            handle_type_discriminated_op(op_name, section.section_kind, discriminator, emu_alg)

        else:
            assert 0, section.section_kind


    else:
        assert op_name in ['MakeArgGetter', 'MakeArgSetter'], op_name
        assert n_emu_algs == 2
        assert section.bcen_str in [
            'p emu-alg p emu-alg emu-note',
            'emu-operation-header emu-alg emu-operation-header emu-alg emu-note'
        ]

        # The first emu-alg defines the operation.
        handle_solo_op(op_name, section.block_children[1])

        # The second emu-alg is the [[Call]] alg for an anonymous built-in function.
        handle_function('anonymous_built_in_function', op_name.replace('Make',''), section.block_children[3])

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_built_in_section(section):
    assert 'prop_path' in section.ste
    prop_path = section.ste['prop_path']

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        # Various possibilities:
        # - A Math function that we merely constrain, via a bullet-list.
        # - "This function is like that function" (except different, maybe).
        # - Other functions that we only define in prose.
        # - A cross-reference to actual definition
        # XXX handle_function(...) ?
        pass

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        handle_function(section.section_kind, prop_path, emu_alg)

    else:
        assert prop_path in ['Array.prototype.sort', '%TypedArray%.prototype.sort']
        # It's an odd combination of the emu-algs in the clause.
        # XXX SortCompare
        # XXX handle_function(...)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_changes_section(section):

    mo = re.fullmatch(r'Changes to (\w+|Abstract Equality Comparison)', section.section_title)
    if mo:
        op_name = mo.group(1)
        assert section.bcen_str in ['p emu-alg', 'p emu-alg p emu-alg']
        for i in range(0, len(section.block_children), 2):
            p = section.block_children[i]
            assert p.element_name == 'p'
            p_ist = p.inner_source_text()
            assert any(
                re.fullmatch(pattern, p_ist)
                for pattern in [
                    f"During {op_name} the following steps are performed in place of step [\w.]+:",
                    f"The following steps are inserted after step 3 of the .+{op_name}.+ algorithm:",
                    f"The result column in .+ for an argument type of Object is replaced with the following algorithm:",
                ]
            ), p_ist

            emu_alg = section.block_children[i+1]
            assert emu_alg.element_name == 'emu-alg'
            handle_solo_op(op_name, emu_alg)
            # XXX debateable, since it's not a full algorithm

    else:
        emu_xref_re = r'<emu-xref href="[^"<>]+"></emu-xref>'
        emu_grammar_re = r'<emu-grammar>[^<>]+</emu-grammar>'
        nont_re = r'\|\w+\|'
        i = 0
        while i < len(section.block_children):
            p = section.block_children[i]; i += 1

            if p.element_name == 'emu-note':
                continue

            assert p.element_name == 'p'
            p_ist = p.inner_source_text()

            if (
                p_ist == 'For web browser compatibility, that rule is modified with the addition of the <ins>highlighted</ins> text:'
                or
                re.fullmatch(fr'The following Early Error rule is added to those in {emu_xref_re}\. .+', p_ist)
                or
                re.fullmatch(fr'The content of subclause {emu_xref_re} is replaced with the following:', p_ist)
            ):
                emu_grammar = section.block_children[i]; i += 1
                ul = section.block_children[i]; i += 1
                handle_early_error(emu_grammar, ul)

            elif re.fullmatch(fr'The semantics of {emu_xref_re} is extended as follows:', p_ist):
                p2 = section.block_children[i]; i += 1
                assert p2.element_name == 'p'
                p2_ist = p2.inner_source_text()
                assert re.fullmatch(fr'Within {emu_xref_re} reference to &ldquo;{emu_grammar_re} &rdquo; are to be interpreted as meaning &ldquo;{emu_grammar_re} &rdquo; or &ldquo;{emu_grammar_re} &rdquo;\.', p2_ist)

            elif (
                re.fullmatch(r'.+ includes the following additional evaluation rules?:', p_ist)
                or 
                re.fullmatch(r'.+ The following evaluation rules are also added:', p_ist)
                or
                re.fullmatch(r'.+ modifies the following evaluation rule:', p_ist)
            ):
                while True:
                    p2 = section.block_children[i]; i += 1
                    if p2.element_name == 'emu-note':
                        break
                    assert p2.element_name == 'p'
                    p2_ist = p2.inner_source_text()
                    if re.fullmatch(fr'The production {emu_grammar_re} evaluates the same as the production {emu_grammar_re} but with {nont_re} substituted for {nont_re}\.', p2_ist):
                        pass
                    elif re.fullmatch(fr'The production {emu_grammar_re} evaluates as follows:', p2_ist):
                        [emu_grammar] = [*p2.each_child_named('emu-grammar')]
                        emu_alg = section.block_children[i]; i += 1
                        assert emu_alg.element_name == 'emu-alg'
                        handle_composite_sdo('regexp-Evaluate', emu_grammar, emu_alg)
                    else:
                        i -= 1
                        break

            elif re.fullmatch(fr'Assertion \({emu_xref_re}\) evaluation rules for the {emu_grammar_re} and {emu_grammar_re} productions are also used for the {nont_re} productions, but with {nont_re} substituted for {nont_re}\.', p_ist):
                pass

            elif re.fullmatch(fr'.+ This change is accomplished by modifying the algorithm of {emu_xref_re} as follows:', p_ist):
                while i < len(section.block_children):
                    p2 = section.block_children[i]; i += 1
                    assert p2.element_name == 'p'
                    p2_ist = p2.inner_source_text()
                    assert re.fullmatch(r'Step [\w.]+ is replaced by:', p2_ist)

                    emu_alg = section.block_children[i]; i += 1
                    assert emu_alg.element_name == 'emu-alg'
                    handle_solo_op('EvalDeclarationInstantiation', emu_alg)

            elif re.fullmatch(fr'The following augments the \|IterationStatement\| production in {emu_xref_re}:', p_ist):
                emu_grammar = section.block_children[i]; i += 1
                assert emu_grammar.element_name == 'emu-grammar'
                p2 = section.block_children[i]; i += 1
                assert p2.element_name == 'p'
                p2_ist = p2.inner_source_text()
                assert p2_ist == 'This production only applies when parsing non-strict code.'

            elif re.fullmatch(fr'The following table entry is inserted into {emu_xref_re} .+', p_ist):
                emu_table = section.block_children[i]; i += 1
                assert emu_table.element_name == 'emu-table'

            else:
                mo = (
                    re.fullmatch(fr'In {emu_xref_re} the (PropertyDefinitionEvaluation) algorithm (.|\n)+ is replaced with the following definition:', p_ist)
                    or
                    re.fullmatch(fr'The (?:static|runtime) semantics of (\w+) in {emu_xref_re} are augmented with the following:', p_ist)
                )
                if mo:
                    op_name = mo.group(1)
                    emu_grammar = section.block_children[i]; i += 1
                    emu_alg = section.block_children[i]; i += 1
                    assert emu_grammar.element_name == 'emu-grammar'
                    assert emu_alg.element_name == 'emu-alg'
                    handle_composite_sdo(op_name, emu_grammar, emu_alg)

                else:
                    print()
                    print('--------------------------------------')
                    print(section.section_num, section.section_title)
                    print(section.bcen_str)
                    print()
                    print(p_ist)
                    print(section.block_children[i].source_text())
                    assert 0
                    break

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_other_section(section):
    # The section_title doesn't declare an operation or a function-property,
    # so we don't expect an algorithm.
    # But sometimes there are some anyway.

    for child in section.block_children:
        if child.element_name == 'emu-eqn':
            handle_emu_eqn(child)

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        if section.section_title == 'Mathematical Operations':
            ensure_foo('abstract_operation', 'abs')
            ensure_foo('abstract_operation', 'min')
            ensure_foo('abstract_operation', 'max')
            ensure_foo('abstract_operation', 'floor')

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]

        if section.section_title == 'Algorithm Conventions':
            assert n_emu_algs == 1
            # It's just the example of algorithm layout.
            # Skip it.
            pass

        elif section.section_title == 'Static Semantics' and section.section_num == '5.2.4':
            assert n_emu_algs == 1
            # It's the default definition of Contains
            preamble_text = section.block_children[emu_alg_posn-1].source_text()
            assert preamble_text.endswith('The default definition of Contains is:</p>')
            handle_composite_sdo('Contains', None, emu_alg)

        elif section.section_title == 'Array.prototype [ @@unscopables ]':
            assert n_emu_algs == 1
            # The section_title identifies a data property,
            # and the algorithm results in its initial value.
            # So CreateIntrinsics invokes this alg, implicitly and indirectly.
            handle_solo_op('initialize_unscopables', emu_alg)

        elif section.section_kind == 'properties_of_an_intrinsic_object':
            assert n_emu_algs == 1
            # In addition to telling you about the intrinsic object,
            # it also defines an abstract operation that is used
            # by the object's function properties.
            mo = re.fullmatch(r'Properties of the (\w+) Prototype Object', section.section_title)
            which = mo.group(1)
            op_name = f"this{'Time' if which == 'Date' else which}Value"

            preamble = section.block_children[emu_alg_posn-1]
            assert (
                preamble.element_name == 'emu-operation-header'
                or
                preamble.source_text() == f'<p>The abstract operation <dfn id="sec-{op_name.lower()}" aoid="{op_name}">{op_name}</dfn>(_value_) performs the following steps:</p>'
            )

            handle_solo_op(op_name, emu_alg)

        else:
            assert 0, section.section_title

    else:

        if section.section_kind == 'shorthand':
            if section.section_title == 'Implicit Completion Values':
                ensure_foo('shorthand', 'Completion')
            elif section.section_title in [
                'ReturnIfAbrupt',
                'Await',
                'NormalCompletion',
                'ThrowCompletion',
            ]:
                ensure_foo('shorthand', section.section_title)
            elif section.section_title == 'IfAbruptRejectPromise ( _value_, _capability_ )':
                ensure_foo('shorthand', 'IfAbruptRejectPromise')
            else:
                pass
                # print('>', section.section_num, section.section_title)
            pass
        elif section.section_title == 'Syntax-Directed Operations':
            # just examples
            pass
        else:
            assert 0, (section.section_num, section.section_title)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_solo_op(op_name, emu_alg):
    # "solo" in the sense of having a single definition,
    # in contrast to multiple definitions discriminated by type or syntax

    foo_add_defn('abstract_operation', op_name, None, parse(emu_alg))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_tabular_op_defn(op_name, tda, tdb):
    assert tda.element_name == 'td'
    assert tdb.element_name == 'td'

    at = tda.inner_source_text().strip()
    bt = tdb.inner_source_text().strip()

    discriminator = at

    x = ' '.join(c.element_name for c in tdb.children)

    if x in ['#LITERAL', '#LITERAL emu-xref #LITERAL']:
        foo_add_defn('abstract_operation', op_name, discriminator, parse(tdb))

    elif x == '#LITERAL p #LITERAL p #LITERAL':
        (_, p1, _, p2, _) = tdb.children
        # XXX:
        # print(p1.inner_source_text())
        # print(p2.inner_source_text())
        pass

    elif x == '#LITERAL p #LITERAL emu-alg #LITERAL':
        (_, p, _, emu_alg, _) = tdb.children
        assert p.source_text() == '<p>Apply the following steps:</p>'
        foo_add_defn('abstract_operation', op_name, discriminator, parse(emu_alg))

    else:
        assert 0, x

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_type_discriminated_op(op_name, section_kind, discriminator, emu_alg):
    foo_add_defn(section_kind, op_name, discriminator, parse(emu_alg))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_early_error(emu_grammar, ul):
    assert emu_grammar.element_name == 'emu-grammar'
    assert ul.element_name == 'ul'

    for li in ul.children:
        if li.element_name == '#LITERAL':
            assert li.source_text().isspace()
        elif li.element_name == 'li':
            tree = parse(li, 'early_error')
            if tree is None: continue
            [ee_rule] = tree.children
            assert ee_rule.prod.lhs_s == '{EE_RULE}'
            foo_add_defn('early_error', 'Early Errors', emu_grammar, ee_rule)
        else:
            assert 0, li.element_name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_composite_sdo(sdo_name, grammar_arg, algo_arg):

    # ---------------------------
    # grammar_arg -> emu_grammar:

    if grammar_arg is None:
        assert sdo_name == 'Contains'
        # This is the default definition,
        # which isn't associated with a particular production.
        emu_grammar = None
    
    elif grammar_arg.element_name == 'emu-grammar':
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
    # algo_arg -> algo:

    if algo_arg.element_name == 'emu-alg':
        algo = parse(algo_arg)
    elif algo_arg.element_name == 'p':
        algo = parse(algo_arg)
    else:
        assert 0, algo_arg.element_name

    # ----------

    foo_add_defn('SDO', sdo_name, emu_grammar, algo)

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

    LI = parse(li, 'inline_sdo')
    if LI is None: return

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
            foo_add_defn('SDO', rule_sdo_name, rule_grammar, rule_expr)

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

    tree = parse(emu_eqn)
    if tree is None: return

    assert tree.prod.lhs_s == '{EMU_EQN_BODY}'
    [child] = tree.children
    if child.prod.lhs_s == '{CONSTANT_DEF}':
        [constant_name, dec_int_lit] = child.children[0:2]
        assert constant_name.source_text() == aoid
        # XXX foo_add_defn('constant', aoid, None, dec_int_lit)
    elif child.prod.lhs_s == '{OPERATION_DEF}':
        [op_name, parameter, body] = child.children
        assert op_name.source_text() == aoid
        parameter_name = parameter.source_text()
        foo_add_defn('abstract_operation', aoid, None, body)
    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_function(section_kind, locater, emu_alg):
    # XXX not using section_kind
    foo_add_defn('built-in function', locater, None, parse(emu_alg))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

spec.info_for_op_named_ = {}
spec.info_for_bif_named_ = {}
# These need to be separate because Set() is both
# an abstract operation and a built-in function.

class Foo:
    # "Foo" = "Function or Operation"
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind
        self.definitions = []

def ensure_foo(foo_kind, foo_name):
    if foo_kind == 'built-in function':
        iffn = spec.info_for_bif_named_
    else:
        iffn = spec.info_for_op_named_

    if foo_name in iffn:
        foo_info = iffn[foo_name]
        assert foo_info.name == foo_name
        assert foo_info.kind == foo_kind
    else:
        foo_info = Foo(foo_name, foo_kind)
        iffn[foo_name] = foo_info

    return foo_info

# ------------------------------------------------

def foo_add_defn(foo_kind, foo_name, discriminator, algo):
    assert type(foo_name) == str

    assert (
        discriminator is None
        or
        isinstance(discriminator, HNode) and discriminator.element_name == 'emu-grammar'
        or
        isinstance(discriminator, ANode) and discriminator.prod.lhs_s == '{nonterminal}'
        or
        isinstance(discriminator, str) # type name
    )

    foo_info = ensure_foo(foo_kind, foo_name)

    if algo is None: return

    assert isinstance(algo, ANode)
    assert algo.prod.lhs_s in [
        '{EXPR}',
        '{NAMED_OPERATION_INVOCATION}',
        '{EMU_ALG_BODY}',
        '{SAMEX}',
        '{EE_RULE}',
        '{RHSS}',
        '{ONE_LINE_ALG}',
    ]

    foo_info.definitions.append( (discriminator, algo, in_annex_b) )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_static_dependencies():

    f_deps = shared.open_for_output('static_deps')
    def put(*args):
        print(*args, file=f_deps)

    # ----------------------------------------------------

    # Find and print all the static dependencies:

    for (foo_name, foo_info) in (
        sorted(spec.info_for_op_named_.items())
        +
        sorted(spec.info_for_bif_named_.items())
    ):
        foo_info.callees = set()
        for (_, algo, _) in foo_info.definitions:
            for callee_name in each_callee_name_in_algo(algo):
                foo_info.callees.add(callee_name)

        put()
        put(foo_name)
        put(f"[{foo_info.kind}, {len(foo_info.definitions)} definitions]")
        for callee in sorted(foo_info.callees):
            put('  ', callee)

    # ----------------------------------------------------

    # Starting at known "top-level" points,
    # do a depth-first search of the dependency graph,
    # marking which operations are "reached".

    op_names_with_no_info = set()

    def reach_op(op_name, level):
        if op_name in op_names_with_no_info:
            # No point in continuing.
            return
        # put('  '*level, op_name)
        if op_name not in spec.info_for_op_named_:
            op_names_with_no_info.add(op_name)
            return
        op_info = spec.info_for_op_named_[op_name]
        if hasattr(op_info, '_reached'): return
        op_info._reached = True
        for callee_name in sorted(list(op_info.callees)):
            reach_op(callee_name, level+1)

    reach_op('Early Errors', 0)
    if shared.g_outdir == '_1597_ed':
        reach_op('InitializeHostDefinedRealm', 1)
        # ScriptEvaluationJob, 1
        reach_op('ParseScript', 2)
        reach_op('ScriptEvaluation', 2)
        # TopLevelModuleEvaluationJob, 1
        reach_op('ParseModule', 2)
        reach_op('Link', 2)
        reach_op('Evaluate', 2)
    else:
        reach_op('RunJobs', 0)

    # put('PromiseJobs queue')
    reach_op('PromiseResolveThenableJob', 1)
    reach_op('PromiseReactionJob', 1)

    # The spec doesn't invoke, but the host can:
    reach_op('FinishDynamicImport', 0)
    reach_op('DetachArrayBuffer', 0)

    # Memory Model
    # put('Valid Executions')
    # references things via bullet point prose
    # put('  '*1, 'host-synchronizes-with')
    reach_op('HostEventSet', 2)
    reach_op('Valid Chosen Reads', 1)
    reach_op('Coherent Reads', 1)
    reach_op('Tear Free Reads', 1)
    #
    reach_op('Data Races', 0)

    for (bif_name, bif_info) in sorted(spec.info_for_bif_named_.items()):
        # put(bif_name)
        for callee in sorted(bif_info.callees):
            reach_op(callee, 1)

    # --------------

    # Print out dependency anomalies.

    put()
    put('X' * 40)

    put()
    put('operations referenced but not declared:')
    for op_name in sorted(op_names_with_no_info):
        put(f"    {op_name}")

    put()
    put('operations declared but not reached:')
    for (op_name, op_info) in sorted(spec.info_for_op_named_.items()):
        if not hasattr(op_info, '_reached'):
            put(f"    {op_name}")

    # ===================================================================

    # Static Semantics

    put()
    put('X' * 40)

    op_names_labelled_ss = set()
    for section in spec.doc_node.each_descendant_that_is_a_section():
        if section.section_title.startswith('Static Semantics:'):
            op_name = section.ste['op_name']
            if op_name == 'TV and TRV':
                op_names_labelled_ss.add('TV')
                op_names_labelled_ss.add('TRV')
            else:
                op_names_labelled_ss.add(op_name)

    # ------

    if 1:
        op_names_reached_from_ss_starting_points = set()

        def ss_reach_op(op_name, level):
            if op_name in op_names_with_no_info:
                # No point in continuing.
                return
            if op_name in op_names_reached_from_ss_starting_points:
                return
            op_names_reached_from_ss_starting_points.add(op_name)
            op_info = spec.info_for_op_named_[op_name]
            for callee_name in sorted(list(op_info.callees)):
                if op_name == 'ToString' and callee_name in ['ToPrimitive', 'ToString']:
                    # These calls only happen for an Object argument,
                    # which we'll assume doesn't occur during Static Semantics.
                    # (ToPrimitive leads to lots of Runtime stuff.)
                    continue

                # put(f"{'  '*level}{level}. {op_name} -> {callee_name}")
                ss_reach_op(callee_name, level+1)

        ss_reach_op('Early Errors', 0)
        ss_reach_op('ParseModule', 0)

        # ----

        put()
        put("ops labelled 'Static Semantics' but not reachable from SS starting points:")
        for op_name in sorted(op_names_labelled_ss - op_names_reached_from_ss_starting_points):
            put(f"    {op_name}")

        put()
        put("ops reachable from SS starting points but not labelled 'Static Semantics':")
        for op_name in sorted(op_names_reached_from_ss_starting_points - op_names_labelled_ss):
            put(f"    {op_name}")

    # ------

    ss_calls_non = []
    non_calls_ss = []

    for (op_name, op_info) in sorted(spec.info_for_op_named_.items()):
        caller_is_ss = op_name in op_names_labelled_ss
        for callee_name in sorted(op_info.callees):
            callee_is_ss = callee_name in op_names_labelled_ss
            if caller_is_ss and not callee_is_ss:
                ss_calls_non.append((op_name, callee_name))
            elif not caller_is_ss and callee_is_ss:
                non_calls_ss.append((op_name, callee_name))
    
    put()
    put("op labelled 'Static Semantics' calls one that isn't:")
    for (caller, callee) in ss_calls_non:
        put(f"    {caller} -> {callee}")

    put()
    put("op not labelled 'Static Semantics' calls one that is:")
    for (caller, callee) in non_calls_ss:
        put(f"    {caller} -> {callee}")

    # ===================================================================

    f_deps.close()

# ------------------------------------------------------------------------------

def each_callee_name_in_algo(algo):
    for callee in each_op_reference_in_algo(algo):
        if isinstance(callee, str):
            yield callee
        else:
            assert isinstance(callee, ANode)
            if callee.prod.lhs_s == '{cap_word}':
                yield callee.source_text()

            elif callee.prod.lhs_s == '{OPN_BEFORE_PAREN}':
                if callee.prod.rhs_s == '{DOTTING}':
                    [dotting] = callee.children
                    [lhs, dsbn] = dotting.children
                    yield dsbn.source_text()
                elif callee.prod.rhs_s == '{var}.{cap_word}':
                    [var, cap_word] = callee.children
                    yield cap_word.source_text()
                elif callee.prod.rhs_s == '{var}':
                    # can't do much
                    if callee.source_text() == '_convOp_':
                        # Should extract this from "The TypedArray Constructors" table
                        yield 'ToInt8'
                        yield 'ToUint8'
                        yield 'ToUint8Clamp'
                        yield 'ToInt16'
                        yield 'ToUint16'
                        yield 'ToInt32'
                        yield 'ToUint32'
                        # PR 1515 BigInt:
                        yield 'ToBigInt64'
                        yield 'ToBigUint64'
                elif callee.prod.rhs_s == '{NUMERIC_TYPE_INDICATOR}::{low_word}':
                    [_, low_word] = callee.children
                    yield '::' + low_word.source_text()
                else:
                    yield callee.source_text()

            elif callee.prod.lhs_s == '{ISDO_NAME}':
                assert callee.prod.rhs_s == '{cap_word}'
                yield callee.source_text()

            else:
                assert 0, callee.prod

def each_op_reference_in_algo(algo):
    for d in algo.each_descendant_or_self():
        if d.prod.lhs_s == '{NAMED_OPERATION_INVOCATION}':
            rhs = d.prod.rhs_s
            if rhs in [
                'the {ISDO_NAME} of {PROD_REF}',
                '{ISDO_NAME} of {PROD_REF}',
                'the {cap_word} of {LOCAL_REF}',
                'the {cap_word} of {LOCAL_REF} (see {h_emu_xref})',
                'the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}',
                'the {cap_word} of {LOCAL_REF} {WITH_ARGS}',
                'the {cap_word} of {LOCAL_REF}; if {LOCAL_REF} is not present, use the numeric value zero',
                '{cap_word} for {LOCAL_REF} {WITH_ARGS}',
                '{cap_word} of {LOCAL_REF}',
                '{cap_word} of {LOCAL_REF} {WITH_ARGS}',
                '{cap_word}({nonterminal})',
            ]:
                yield d.children[0]

            elif rhs == '{PREFIX_PAREN}':
                # Handled below
                pass

            elif rhs == 'evaluating {LOCAL_REF}':
                # 'Evaluation' or 'regexp-Evaluate',
                # depending on the argument.
                [local_ref] = d.children
                if local_ref.source_text() in [
                    '|NonemptyClassRanges|',
                    '|ClassAtom|',
                    '|ClassAtomNoDash|',
                    '|ClassEscape|',
                    '|CharacterClassEscape|',
                ]:
                    yield 'regexp-Evaluate'
                else:
                    yield 'Evaluation'

            else:
                callee_names = {
                    'Abstract Equality Comparison {var} == {var}'      : ['Abstract Equality Comparison'],
                    'Abstract Relational Comparison {var} &lt; {var} with {var} equal to {LITERAL}' : [ 'Abstract Relational Comparison'],
                    'Abstract Relational Comparison {var} &lt; {var}'  : ['Abstract Relational Comparison'],
                    'Strict Equality Comparison {var} === {EX}'        : ['Strict Equality Comparison'],
                    'StringValue of the {nonterminal} of {nonterminal} {var}' : ['StringValue'],
                    'evaluating {LOCAL_REF} with argument {var}'       : ['regexp-Evaluate'],
                    'evaluating {LOCAL_REF}. This may be of type Reference' : ['Evaluation'],
                    'evaluating {nonterminal} {var}'                   : ['Evaluation'],
                    'the abstract operation named by {DOTTING} using the elements of {DOTTING} as its arguments': ['ScriptEvaluationJob', 'TopLevelModuleEvaluationJob'],
                    "the internal procedure that evaluates the above parse of {var} by applying the semantics provided in {h_emu_xref} using {var} as the pattern's List of {nonterminal} values and {var} as the flag parameters": ['regexp-Evaluate'],
                    'the UTF16Encoding of each code point of {EX}'     : ['UTF16Encoding'],
                    'the UTF16Encoding of the code points of {var}'    : ['UTF16Encoding'],
                    '{LOCAL_REF} Contains {nonterminal}'               : ['Contains'],
                    '{LOCAL_REF} Contains {var}'                       : ['Contains'],
                }[rhs]
                for callee_name in callee_names:
                    yield callee_name

        elif d.prod.lhs_s == '{PREFIX_PAREN}':
            [opn_before_paren, exlist_opt] = d.children
            assert opn_before_paren.prod.lhs_s == '{OPN_BEFORE_PAREN}'
            yield opn_before_paren

        elif str(d.prod) == '{CONDITION_1} : {var} and {var} are in a race in {var}':
            yield 'Races'

        elif str(d.prod) == '{EXPR} : the steps of an {cap_word} function as specified below':
            # [cap_word] = d.children
            # yield cap_word
            # No, because that's a function, not an operation.
            pass

        elif str(d.prod) == '{COMMAND} : Set fields of {var} with the values listed in {h_emu_xref} {that_have_not_already_etc}':
            yield 'CreateBuiltinFunction'
            yield 'initialize_unscopables'

        elif str(d.prod) == '{COMMAND} : IfAbruptRejectPromise({var}, {var}).':
            yield 'IfAbruptRejectPromise'

        elif str(d.prod) in [
            '{COMMAND} : ReturnIfAbrupt({EX}).',
            '{SMALL_COMMAND} : ReturnIfAbrupt({var})',
        ]:
            yield 'ReturnIfAbrupt'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_sdo_coverage():
    stderr('check_sdo_coverage...')
    spec.sdo_coverage_map = {}

    # collect sdo_coverage_info:
    for (op_name, op_info) in spec.info_for_op_named_.items():
        if op_info.kind == 'SDO':

            if op_name not in spec.sdo_coverage_map:
                spec.sdo_coverage_map[op_name] = {}

            for (discriminator, emu_alg, in_annex_b) in op_info.definitions:
                # XXX Exclude Annex B definitions from sdo_coverage analysis:
                if in_annex_b: continue

                if isinstance(discriminator, ANode):
                    assert discriminator.prod.lhs_s == '{nonterminal}'
                    assert discriminator.source_text() == '|HexDigit|'
                    discriminator.summary = [] # XXX?

                if discriminator is None:
                    assert op_name == 'Contains'
                    continue

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

    if sdo_name == 'CharacterValue' and lhs_nt == 'ClassEscape' and def_i == (3 if shared.g_outdir == '_one-grammar' else 2):
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

    if sdo_name in ['AllPrivateIdentifiersValid', 'ContainsArguments']:
        # PR 1668 private fields:
        # "For all other grammatical productions, ..."
        return True

    return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# import cProfile
# cProfile.run('main()', '_prof')

# vim: sw=4 ts=4 expandtab
