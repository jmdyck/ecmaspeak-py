
# ecmaspeak-py/Section.py:
# Identify "sections" in the spec, and ascertain their 'kind'.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, string, time
from collections import OrderedDict
from dataclasses import dataclass

import shared
from shared import stderr, header, msg_at_posn, spec
from HTML import HNode
import Pseudocode
import headers

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def make_and_check_sections():
    stderr("make_and_check_sections ...")

    Pseudocode.create_all_parsers()
    headers.oh_inc_f = shared.open_for_output('oh_warnings')

    spec.root_section = _make_section_tree(spec.doc_node)
    _set_section_identification_r(spec.root_section, None)

    t_start = time.time()

    prev_top_level_num = ''
    for section in spec.root_section.each_descendant_that_is_a_section():

        # "progress bar"
        top_level_num = section.section_num.split('.')[0]
        if top_level_num != prev_top_level_num:
            stderr(f" {top_level_num}", end='', flush=True)
            prev_top_level_num = top_level_num

        section.alg_defns = []

        _set_section_kind(section)

    stderr()

    t_end = time.time()
    stderr(f"analyzing sections took {t_end-t_start:.2f} seconds")

    Pseudocode.check_emu_alg_coverage()
    Pseudocode.check_emu_eqn_coverage()
    Pseudocode.report_all_parsers()

    headers.oh_inc_f.close()
    headers.note_unused_rules()

    _print_section_kinds(spec.root_section)
    _check_aoids(spec.root_section)
    _check_section_order(spec.root_section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _make_section_tree(doc_node):
    # We traverse the spec's doc-tree to find all the sections.
    # Each section is a pre-existing HNode --
    # mainly every <emu-clause>, but also every <emu-annex>,
    # one <emu-intro>, and the <body> element.
    #
    # Each HNode is already connected to its HNode children,
    # but we connect each section to its children in a different way.
    # Thus, we establish an alternative tree by which to traverse the document.
    # (The <body> node becomes the root of the section-tree.)

    # Set section attributes:
    # .section_level
    # .is_root_section
    # .block_children
    # .numless_children
    # .section_children
    # .heading_child
    # .bcen_{list,str,set}

    assert doc_node.element_name == '#DOC'
    [html_node] = [
        child
        for child in doc_node.children
        if child.element_name == 'html'
    ]
    [body_node] = [
        child
        for child in html_node.children
        if child.element_name == 'body'
    ]
    _make_section_tree_r(body_node, 0)
    return body_node

def _make_section_tree_r(section, section_level):
    section.section_level = section_level
    section.is_root_section = (section_level == 0)

    assert not section.inline_child_element_names
    # if section.inline_child_element_names:
    #     msg_at_posn(
    #         section.inner_start_posn,
    #         "'section' node contains inline items"
    #     )

    section.block_children = []
    section.numless_children = []
    section.section_children = []

    for child in section.children:
        if child.is_whitespace():
            pass

        elif child.element_name == '#COMMENT':
            pass

        elif child.is_a_section():
            section.section_children.append(child)

        elif child.element_name == 'h2':
            numless = Numless( child.inner_source_text() )
            section.numless_children.append(numless)

        elif section.numless_children:
            section.numless_children[-1].block_children.append(child)

        else:
            section.block_children.append(child)

    if section.is_root_section:
        section.heading_child = None
    else:
        h1 = section.block_children.pop(0)
        assert h1.element_name == 'h1'
        section.heading_child = h1

    if (
        len(section.block_children) == 0
        and
        len(section.numless_children) == 0
        and
        len(section.section_children) == 0
    ):
        msg_at_posn(
            section.start_posn,
            "section is empty!"
        )

    _set_bcen_attributes(section)

    for child in section.section_children:
        _make_section_tree_r(child, section_level+1)

# -------------

class Numless:
    # A numberless part of a section. Starts with an h2.
    def __init__(self, title):
        self.title = title
        self.block_children = []

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _set_section_identification_r(section, section_num):
    # Set section attributes:
    # .section_num
    # .section_id
    # .section_title

    section.section_num = section_num

    if section.is_root_section:
        section.section_id = None
        section.section_title = None

        clause_counter = 0
        annex_counter = 0
        for child in section.section_children:
            if child.element_name == 'emu-intro':
                sn = '0'
            elif child.element_name == 'emu-clause':
                clause_counter += 1
                sn = str(clause_counter)
            elif child.element_name == 'emu-annex':
                sn = string.ascii_uppercase[annex_counter]
                annex_counter += 1
            else:
                assert 0, child.element_name
            _set_section_identification_r(child, sn)

    else:
        section.section_id = section.attrs['id']
        section.section_title = section.heading_child.inner_source_text()

        child_clause_counter = 0
        for child in section.section_children:
            child_clause_counter += 1
            sn = section_num + '.' + str(child_clause_counter)
            _set_section_identification_r(child, sn)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _set_section_kind(section):
    # Set section attributes:
    # .section_kind
    # .section_title
    # .ste

    section.has_structured_header = False

    r = (
        _handle_root_section(section)
        or
        _handle_early_errors_section(section)
        or
        _handle_sdo_section(section)
        or
        _handle_oddball_op_section(section)
        or
        _handle_other_op_section(section)
        or
        _handle_function_section(section)
        or
        _handle_changes_section(section)
        or
        _handle_other_section(section)
    )
    assert r

    ensure_every_emu_alg_in_section_is_parsed(section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def ensure_every_emu_alg_in_section_is_parsed(section):
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

                    '\n              1. Otherwise, let ',
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

            # print('\n!', section.section_num, section.section_title)
            Pseudocode.parse(emu_alg)
            # Most of these are involved in the definition of shorthands,
            # which I don't handle well.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_root_section(section):
    if section.is_root_section:
        return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_early_errors_section(section):
    if section.section_title != 'Static Semantics: Early Errors':
        return False

    section.section_kind = 'early_errors'
    section.ste = {'op_name': 'Early Errors'}

    alg_header = AlgHeader_make(
        section = section,
        species = 'op: early error',
        name = 'Early Errors',
        for_phrase = 'Parse Node',
        params = [],
        also = [],
        node_at_end_of_header = section.heading_child,
    )

    patterns = [
        (
            # 89 cases, the vast majority
            ['emu-grammar', 'ul'],
            lambda emu_grammar, ul: (emu_grammar, None, ul)
        ),
        (
            # 3 cases:
            #   13.15.1   sec-assignment-operators-static-semantics-early-errors
            #   13.15.5.1 sec-destructuring-assignment-static-semantics-early-errors
            #   14.7.5.1  sec-for-in-and-for-of-statements-static-semantics-early-errors
            # Extra <p> constrains aplication of immediately following <ul>.
            # (See old bug 4378: https://tc39.github.io/archives/bugzilla/4378/)
            [
                'emu-grammar',
                ('p', 'If .+, the following Early Error rules are applied:'),
                'ul',
                ('p', 'If .+, the following Early Error rule is applied:'),
                'ul'
            ],
            lambda emu_grammar, p1, ul1, p2, ul2: [
                (emu_grammar, p1, ul1),
                (emu_grammar, p2, ul2),
            ]
        ),
        (
            # 1 case (13.2.5.1 Static Semantics: Early Errors)
            # sec-object-initializer-static-semantics-early-errors
            # Extra <p> constrains application of subsequent 2 emu-grammar+ul pairs.
            [
                ('p', '.+ the following Early Error rules .+ not applied .+'),
                'emu-grammar',
                'ul',
                'emu-note',
                'emu-grammar',
                'ul',
            ],
            lambda p, emu_grammar1, ul1, emu_note, emu_grammar2, ul2: [
                (emu_grammar1, p, ul1),
                (emu_grammar2, p, ul2),
            ]
        ),
        (
            # 1 case (B.1.4.1 "Static Semantics: Early Errors")
            [ ('p', 'The semantics of <emu-xref href="#[^"]+"></emu-xref> is extended as follows:') ],
            None
        ),
        (
            # 1 case (B.1.4.1 "Static Semantics: Early Errors")
            [ ('p', 'Additionally, the rules for the following productions are modified with the addition of the <ins>highlighted</ins> text:') ],
            None
        ),
        (
            # 18 cases
            ['emu-note'],
            None
        ),
    ]

    bodies = scan_section(section, patterns)

    for body in bodies:
        assert isinstance(body, tuple)
        (emu_grammar, p, ul) = body

        # TODO: handle <p>

        handle_early_error(emu_grammar, ul, alg_header)

    return True

# ------------------------------------------------------------------------------

def handle_early_error(emu_grammar, ul, alg_header):
    assert emu_grammar.element_name == 'emu-grammar'
    assert ul.element_name == 'ul'

    for li in ul.children:
        if li.element_name == '#LITERAL':
            assert li.source_text().isspace()
        elif li.element_name == 'li':
            tree = Pseudocode.parse(li, 'early_error')
            if tree is None: continue
            [ee_rule] = tree.children
            assert ee_rule.prod.lhs_s == '{EE_RULE}'
            if alg_header:
                AlgHeader_add_definition(alg_header, emu_grammar, ee_rule, make_annex_B_exception=True)
        else:
            assert 0, li.element_name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_sdo_section(section):

    # Since the merge of PR #2271,
    # almost all SDO sections are identified by `type="sdo"`.
    if section.attrs.get('type') == 'sdo':
        sdo_name = section.attrs['aoid']

    else:
        # But `type="sdo"` really means more like:
        # "This clause is the complete definition of exactly one SDO."
        # So there are various clauses that don't get `type="sdo"`
        # that we neverthless want to mark as SDO sections...

        # A clause that only *partially* defines an SDO:
        if section.section_title in [
            'Runtime Semantics: MV',
            'Static Semantics: MV',
            'Runtime Semantics: Evaluation',
        ]:
            sdo_name = re.sub('.*: ', '', section.section_title)

        elif section.parent.section_title == 'Static Semantics: HasCallInTailPosition':
            # 15.10.2.1 Statement Rules
            # 15.10.2.2 Expression Rules
            sdo_name = 'HasCallInTailPosition'

        elif (
            section.parent.section_id == 'sec-pattern-semantics'
            and
            section.section_title != 'Notation'
        ):
            # 22.2.2.*
            sdo_name = 'regexp-Evaluate'

        # An Annex B clause that extends the semantics of a main-body SDO:
        elif section.section_title in [
            'Static Semantics: IsCharacterClass',
            'Static Semantics: CharacterValue',
            'Static Semantics: NumericValue',
        ]:
            # B.1.4.2
            # B.1.4.3
            sdo_name = re.sub('.*: ', '', section.section_title)

        else:
            # Anything else isn't an SDO section.
            return False

    # -------------------------------------------
    # At this point, we know it's an SDO section.

    section.section_kind = 'syntax_directed_operation'

    section.ste = {'op_name': sdo_name}

    if section.section_title in ['Statement Rules', 'Expression Rules']:
        # TODO: Should copy this from section.parent
        params = [ AlgParam('_call_', '', 'unknown') ]

    else:
        # Parameters, if any, are stated in the section's first paragraph.
        params = []
        c0 = section.block_children[0]
        if c0.element_name == 'p':
            p_text = c0.source_text()
            if p_text.startswith('<p>With '):
                mo = re.match(r'^<p>With (.+)\.</p>$', p_text)
                assert mo, p_text
                params_s = mo.group(1)
                if mo := re.match(r'(.+?),? and (optional .+)', params_s):
                    parts = mo.groups()
                else:
                    parts = [params_s]

                for part in parts:
                    part_punct = '[]' if part.startswith('optional') else ''
                    part_params_s = re.sub('^(optional )?parameters? ', '', part)

                    for param in re.split(r', and |, | and ', part_params_s):
                        if param == '_argumentsList_ (a List)':
                            param_name = '_argumentsList_'
                            param_nature = 'a List'
                        else:
                            assert re.match(r'^_[a-zA-Z]+_$', param), param
                            param_name = param
                            param_nature = 'unknown'
                        params.append( AlgParam(param_name, part_punct, param_nature) )
                section.block_children.pop(0)
                _set_bcen_attributes(section)

    if sdo_name == 'regexp-Evaluate':
        # regexp-Evaluate is unique in that it doesn't have a uniform set of parameters:
        # sometimes it has the _direction_ parameter, and sometimes it doesn't.
        # Force it to always have the _direction_ parameter.
        assert [param.name for param in params] in [ [], ['_direction_'] ]
        params = [ AlgParam('_direction_', '', '1 or -1') ]
        # Don't make it optional, because then its type will be (Integer_ | not_passed),
        # and STA will complain when we use it in a context that expects just Integer_.

    if sdo_name == 'regexp-Evaluate':
        also = regexp_also
    else:
        also = []

    alg_header = AlgHeader_make(
        section = section,
        species = 'op: syntax-directed',
        name = sdo_name,
        for_phrase = 'Parse Node',
        params = params,
        also = also,
        node_at_end_of_header = section.heading_child,
    )

    # ------------------------------------------------------------------------------

    if 'ul' in section.bcen_set:
        # The rules are given in one or more <ul> elements.
        handle_inline_sdo_section_body(section, alg_header)

    else:
        patterns = [
            (
                # ~900 cases, the vast majority.
                ['emu-grammar', 'emu-alg'],
                lambda emu_grammar, emu_alg: (emu_grammar, emu_alg)
            ),
            (
                # 58 cases in RegExp 22.2.2.*
                [
                    ('p', "The production <emu-grammar>.+?</emu-grammar> evaluates as follows:"),
                    'emu-alg'
                ],
                lambda p, emu_alg: (p.children[1], emu_alg)
            ),
            (
                # 3 cases in RegExp 22.2.2.* (CharacterEscape, DecimalEscape, ClassEscape):
                [
                    ('p', "The \|\w+\| productions evaluate as follows:"),
                    'emu-grammar',
                    'emu-alg',
                ],
                lambda p, emu_grammar, emu_alg: (emu_grammar, emu_alg)
            ),
            (
                # 3 cases
                [
                    ('p', 'Every grammar production alternative in this specification which is not listed below implicitly has the following default definition of \w+:'),
                    'emu-alg'
                ],
                lambda p, emu_alg: (None, emu_alg)
            ),
            (
                # 2 cases in Annex B
                [
                    ('p', 'The semantics of <emu-xref [^<>]+></emu-xref> is extended as follows:'),
                    'emu-grammar',
                    'emu-alg'
                ],
                lambda p, emu_grammar, emu_alg: (emu_grammar, emu_alg)
            ),
            (
                # 90 cases
                ['emu-note'],
                None
            ),
            (
                # 2 cases:
                #
                # 13.5.3.1
                # Evaluation of |UnaryExpression : `typeof` UnaryExpression|
                # ends with "Return a String according to <reference to emu-table>."
                # and then the emu-alg is followed by an emu-table.
                #
                # 22.2.1.4
                # CharacterValue of |CharacterEscape :: ControlEscape| is
                # "Return the code point value according to Table 59."
                # and then the emu-alg is followed by an emu-table.
                #
                ['emu-table'],
                None
            ),
            (
                # 6 cases. They're basically Notes.
                ['p'],
                None
            ),
        ]

        bodies = scan_section(section, patterns)

        for body in bodies:
            (emu_grammar, emu_alg) = body
            AlgHeader_add_definition(alg_header, emu_grammar, emu_alg, make_annex_B_exception=True)

    return True

# ------------------------------------------------------------------------------

def handle_inline_sdo_section_body(section, alg_header):

    lis = []
    for bc in section.block_children:
        if bc.element_name == 'ul':
            # Each <li> in the <ul> is an "inline SDO".
            for ul_child in bc.children:
                if ul_child.is_whitespace(): continue
                assert ul_child.element_name == 'li'
                lis.append(ul_child)
        elif bc.element_name == 'emu-table':
            # "String Single Character Escape Sequences" in 12.8.4.1 "Static Semantics: SV"
            # This table has info that is necessary for executing one of the SV rules,
            # but we'll deal with it some other time?
            pass
        elif bc.element_name in ['p', 'emu-note']:
            # In practice, in this context, a <p> is basically a Note.
            pass
        else:
            assert 0, bc.element_name

    for li in lis:
        assert li.element_name == 'li'

        LI = Pseudocode.parse(li, 'inline_sdo')
        if LI is None: continue

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
                assert rule_sdo_name == alg_header.name
                rule_sdo_names.append(rule_sdo_name)
            elif cl == '{h_emu_grammar}':
                rule_grammars.append(child._hnode)
            elif cl == '{nonterminal}':
                rule_grammars.append(child)
            elif cl == '{EXPR}':
                assert rule_expr is None
                rule_expr = child
            elif cl in ['{NAMED_OPERATION_INVOCATION}', '{h_sub_fancy_f}']:
                if 'Note that if {NAMED_OPERATION_INVOCATION}' in ISDO_RULE.prod.rhs_s:
                    # skip it
                    pass
                else:
                    assert rule_expr is None
                    rule_expr = child
            else:
                assert 0, cl

        assert len(rule_sdo_names) == 1 # and so could simplify
        assert 0 < len(rule_grammars) <= 5
        for rule_sdo_name in rule_sdo_names:
            for rule_grammar in rule_grammars:
                AlgHeader_add_definition(alg_header, rule_grammar, rule_expr, make_annex_B_exception=True)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_oddball_op_section(section):
    # This function handles a few specific cases where even though section doesn't have
    # - a `type` attribute, or
    # - a structured header, or
    # - a preamble with standardized wording,
    # we still want to treat it like an op.

    if section.section_id in [
        'sec-object-environment-records-createimmutablebinding-n-s',
        'sec-module-environment-records-deletebinding-n',
    ]:
        # The clause exists only to tell us that the concrete method is never used.
        p = section.block_children[0]
        assert p.element_name == 'p'
        assert re.fullmatch(
            r'The \w+ concrete method of an? \w+ Environment Record is never used within this specification.',
            p.inner_source_text()
        )
        # Note that the start of this sentence looks like the start of a standardized preamble,
        # so we have to detect these cases before _handle_other_op_section's call
        # to _handle_header_with_std_preamble.

        # There's roughly two approaches:
        # - Create the thing, but make the body of it be (effectively) "Assert: False."
        # - Don't create the thing. (So if there *is* an attempt to use it, the lookup will fail.)
        # Let's try the latter.
        # I.e., don't create anything, but return True to indicate that we've handled this section.
        section.section_kind = 'env_rec_method_unused'
        section.ste = {}
        return True

    # ----

    if section.section_id == 'sec-weakref-execution':
        # 9.10.3
        op_name = 'WeakRef emptying thing'
        assert section.block_children[0].source_text().startswith(
            "<p>At any time, if a set of objects _S_ is not live,"
        )
        params = [ AlgParam('_S_', '', 'unknown') ]

    elif section.section_title in [
        'Valid Chosen Reads',
        'Coherent Reads',
        'Tear Free Reads',
    ]:
        # 29.7.*
        op_name = section.section_title
        assert section.block_children[0].source_text().startswith(
            "<p>A candidate execution _execution_ has "
        )
        params = [ AlgParam('_execution_', '', 'an execution') ]

    elif section.section_title in [
        'Races',
        'Data Races',
    ]:
        # 29.8, 29.9
        op_name = section.section_title
        assert section.block_children[0].source_text().startswith(
            "<p>For an execution _execution_, two events _E_ and _D_ in SharedDataBlockEventSet(_execution_) are in a "
        )
        params = [
            AlgParam('_execution_', '', 'an execution'),
            AlgParam('_E_'        , '', 'an event in SharedDataBlockEventSet(_execution_)'),
            AlgParam('_D_'        , '', 'an event in SharedDataBlockEventSet(_execution_)'),
        ]

    else:
        return False

    # --------------------------------------------

    section.section_kind = 'abstract_operation'

    section.ste = {'op_name': op_name}

    headers.oh_warn()
    headers.oh_warn(f"In {section.section_num} {section.section_title} ({section.section_id}),")
    headers.oh_warn(f"there is a non-standard preamble")

    alg_header = AlgHeader_make(
        section = section,
        species = 'op: solo',
        name = op_name,
        params = params,
        node_at_end_of_header = section.heading_child,
    )

    emu_alg = section.block_children[1]
    assert emu_alg.element_name == 'emu-alg'
    AlgHeader_add_definition(alg_header, None, emu_alg)

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_other_op_section(section):

    section_type = section.attrs.get('type')
    if section_type == 'sdo':
        assert 0 # Would have been handled already
        return False

    elif section_type is not None:
        # type="sdo" has been around for a while,
        # but all the other type="..." attributes were introduced in PR #545.
        # So we can assume that this section has a structured header?
        # (Or might authors add a `type` attribute but use an old-style header?)
        alg_header = _handle_structured_header(section)

    elif (alg_header := _handle_header_with_std_preamble(section)):
        pass

    else:
        return False

    # --------------------------------------------------------------------------

    op_species = alg_header.species
    op_name = alg_header.name

    n_emu_algs = section.bcen_list.count('emu-alg')
    if n_emu_algs == 0:
        emu_alg = None
    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        assert emu_alg.element_name == 'emu-alg'
    else:
        assert 0, n_emu_algs

    if emu_alg is None and 'emu-table' in section.bcen_set:
        assert section.bcen_str == 'emu-table' # it turns out
        [emu_table] = section.block_children
        handle_op_table(emu_table, alg_header)

    elif section.section_kind in [
        'host-defined_abstract_operation',
        'implementation-defined_abstract_operation',
    ]:
        if emu_alg is None:
            # That's what we'd expect.
            # Typically, there's a <ul> containing
            # requirements that the implementation must conform to.
            Pseudocode.ensure_alg(op_species, op_name)
        else:
            # 3 cases:
            # - 9.5.2 HostMakeJobCallback
            # - 9.5.3 HostCallJobCallback
            # - 9.10.4.1 HostEnqueueFinalizationRegistryCleanupJob
            # In the first two, the <emu-alg> is a default implementation,
            # which is actually required for non-browsers.
            # In the last, the <emu-alg> is the steps of an Abstract Closure
            # that defines the job to be scheduled.
            #
            # TODO: Handle these better.
            discriminator = None
            AlgHeader_add_definition(alg_header, discriminator, emu_alg)

    elif emu_alg is None:
        if section.section_title.startswith('BigInt::'):
            # 6 of the BigInt::* methods just give the semantics in the preamble.
            Pseudocode.ensure_alg(op_species, op_name)
        elif op_name == 'StringToBigInt':
            # StringToBigInt says:
            # "Apply the algorithm in 7.1.4.1 with the following changes: ..."
            # (ick)
            Pseudocode.ensure_alg(op_species, op_name)
        else:
            assert 0, (section.section_num, section.section_title)

    else:
        # The emu-alg is the 'body' of
        # (this definition of) the operation named by the section_title.

        if section.section_kind == 'abstract_operation':
            discriminator = None

        elif section.section_kind in [
            'numeric_method',
            'env_rec_method',
            'module_rec_method',
            'internal_method',
        ]:
            # type-discriminated operation
            discriminator = {
                # numeric_method:
                'The Number Type': 'Number',
                'The BigInt Type': 'BigInt',

                # env_rec_method:
                'Declarative Environment Records' : 'declarative Environment Record',
                'Object Environment Records'      : 'object Environment Record',
                'Function Environment Records'    : 'function Environment Record',
                'Global Environment Records'      : 'global Environment Record',
                'Module Environment Records'      : 'module Environment Record',

                # module_rec_method:
                'Cyclic Module Records'           : 'Cyclic Module Record',
                'Source Text Module Records'      : 'Source Text Module Record',

                # internal_method:
                'Ordinary Object Internal Methods and Internal Slots': 'ordinary object',
                'ECMAScript Function Objects'       : 'ECMAScript function object',
                'Built-in Function Objects'         : 'built-in function object',
                'Bound Function Exotic Objects'     : 'bound function exotic object',
                'Array Exotic Objects'              : 'Array exotic object',
                'String Exotic Objects'             : 'String exotic object',
                'Arguments Exotic Objects'          : 'arguments exotic object',
                'Integer-Indexed Exotic Objects'    : 'Integer-Indexed exotic object',
                'Module Namespace Exotic Objects'   : 'module namespace exotic object',
                'Immutable Prototype Exotic Objects': 'immutable prototype exotic object',
                'Proxy Object Internal Methods and Internal Slots': 'Proxy exotic object',
            }[section.parent.section_title]

        else:
            assert 0, section.section_kind

        AlgHeader_add_definition(alg_header, discriminator, emu_alg)

    # -----------------------------------------

    return True

# ------------------------------------------------------------------------------

def handle_op_table(emu_table, alg_header):
    # The op is defined by a table that splits on argument type.
    # I.e., each row has two cells:
    # - The first cell is the name of an ES language type.
    # - The second cell is a little algorithm,
    #   but it's generally not marked as an emu-alg.

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

        assert a.element_name == 'td'
        assert b.element_name == 'td'

        at = a.inner_source_text().strip()
        bt = b.inner_source_text().strip()

        discriminator = at

        x = ' '.join(c.element_name for c in b.children)

        if x in [
            '#LITERAL',
            '#LITERAL emu-xref #LITERAL',
            '#LITERAL sub #LITERAL',
            '#LITERAL sub #LITERAL sub #LITERAL',
        ]:
            AlgHeader_add_definition(alg_header, discriminator, b)

        elif x == '#LITERAL emu-note #LITERAL':
            # ToBoolean: row for 'Object' has a NOTE re [[IsHTMLDDA]]
            AlgHeader_add_definition(alg_header, discriminator, b)

        elif x == '#LITERAL p #LITERAL p #LITERAL':
            (_, p1, _, p2, _) = b.children
            AlgHeader_add_definition(alg_header, discriminator, b)
            pass

        elif x == '#LITERAL p #LITERAL emu-alg #LITERAL':
            (_, p, _, emu_alg, _) = b.children
            assert p.source_text() == '<p>Apply the following steps:</p>'
            AlgHeader_add_definition(alg_header, discriminator, emu_alg)

        else:
            assert 0, x

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

other_op_species_for_section_kind_ = {
    'env_rec_method'                           : 'op: concrete method: env rec',
    'module_rec_method'                        : 'op: concrete method: module rec',
    'numeric_method'                           : 'op: numeric method',
    'internal_method'                          : 'op: internal method',
    'abstract_operation'                       : 'op: solo',
    'host-defined_abstract_operation'          : 'op: host-defined',
    'implementation-defined_abstract_operation': 'op: implementation-defined',
}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_structured_header(section):
    section.has_structured_header = True

    dl = section.block_children.pop(0)
    assert dl.element_name == 'dl'
    assert dl.attrs.get('class') == 'header'
    section.dl_child = dl
    _set_bcen_attributes(section)

    section_type = section.attrs.get('type')

    if section_type == 'concrete method':
        if section.parent.parent.section_id == 'sec-the-environment-record-type-hierarchy':
            section.section_kind = 'env_rec_method'
        elif section.parent.parent.section_id == 'sec-module-semantics':
            section.section_kind = 'module_rec_method'
        else:
            assert 0, section.section_id
            
    else:
        section.section_kind = {
            'abstract operation': 'abstract_operation',
            'numeric method'    : 'numeric_method',
            'internal method'   : 'internal_method',
            'host-defined abstract operation'          : 'host-defined_abstract_operation',
            'implementation-defined abstract operation': 'implementation-defined_abstract_operation',
        }[section_type]

    h1 = section.heading_child
    h1_ist = h1.inner_source_text()

    if '\n' not in h1_ist:
        # single-line h1:
        mo = re.fullmatch(r'([A-Z][a-zA-Z]+|\[\[[A-Z][a-zA-Z]+\]\]) \( \)', h1_ist)
        assert mo
        op_name = mo.group(1)
        params = []

    else:
        # multi-line h1:
        posn_of_linestart_before_h1 = 1 + spec.text.rfind('\n', 0, h1.start_posn)
        h1_indent = h1.start_posn - posn_of_linestart_before_h1

        reo = re.compile(r'(?m)( +)(.*)')
        posns_for_line_ = []
        for mo in reo.finditer(spec.text, posn_of_linestart_before_h1, h1.end_posn):
            assert mo.end(1) == mo.start(2)
            posns_for_line_.append( (mo.start(1), mo.end(1), mo.end(2)) )

        if section.section_kind == 'numeric_method':
            op_name_pattern = r'[A-Z][a-zA-Z]+::[a-z][a-zA-Z]+'
        elif section.section_kind == 'internal_method':
            op_name_pattern = r'\[\[[A-Z][a-zA-Z]+\]\]'
        else:
            op_name_pattern = r'[A-Z][a-zA-Z0-9/]+'

        patterns = [
            (0, '<h1>'),
            (2, fr'(Static Semantics: )?({op_name_pattern}) \('),
            (4, r'(optional )?(_\w+_): (.+),'),
            (2, fr'\)'),
            (0, '</h1>'),
        ]
        which_semantics = 'UNSET'
        op_name = 'UNSET'
        params = []
        n_lines = len(posns_for_line_)
        for (line_i, (a,b,c)) in enumerate(posns_for_line_):
            if line_i in [0, 1]:
                pattern_i = line_i
            elif line_i in [n_lines-2, n_lines-1]:
                pattern_i = line_i - n_lines
            else:
                pattern_i = 2
            (expected_indent_add, expected_pattern) = patterns[pattern_i]

            actual_indent = b - a
            assert actual_indent == h1_indent + expected_indent_add

            mo = re.compile(expected_pattern).fullmatch(spec.text, b, c)
            if mo:
                d = mo.groupdict()
                if pattern_i == 1:
                    [which_semantics, op_name] = mo.groups()
                    if which_semantics is None: which_semantics = ''
                elif pattern_i == 2:
                    [optionality, param_name, param_nature] = mo.groups()
                    param_punct = '[]' if (optionality == 'optional ') else ''
                    params.append( AlgParam(param_name, param_punct, param_nature) )
                else:
                    assert mo.groups() == ()
            else:
                msg_at_posn(b, f"line doesn't match pattern /{expected_pattern}/")

        def brief_params(param_i):
            if param_i == len(params):
                return ''
            else:
                brief_for_subsequent_params = brief_params(param_i + 1)
                param = params[param_i]
                if param.punct == '[]':
                    comma = ' ' if param_i == 0 else ' , '
                    return f" [{comma}{param.name}{brief_for_subsequent_params} ]"
                else:
                    comma = ' ' if param_i == 0 else ', '
                    return f"{comma}{param.name}{brief_for_subsequent_params}"

        # overwrite section.section_title
        section.section_title = f"{which_semantics}{op_name} ({brief_params(0)} )"

    if '::' in op_name:
        (for_phrase, op_name) = re.split(r'(?=::)', op_name)
    else:
        for_phrase = None

    # --------------------------------------------------------------------------
    # Extract info from the <dl>

    dl_dict = {}
    dl_nw_children = [
        child 
        for child in dl.children
        if not child.is_whitespace()
    ]
    children_names = ''.join(
        child.element_name + ';'
        for child in dl_nw_children
    )
    assert re.fullmatch(r'(dt;dd;)*', children_names)
    for i in range(0, len(dl_nw_children), 2):
        dt = dl_nw_children[0]
        dd = dl_nw_children[1]
        # This will need to be generalized, but is okay for now:
        dt_s = dt.inner_source_text()
        dd_s = dd.inner_source_text()
        dl_dict[dt_s] = dd_s

    # ----------------------------------

    if 'for' in dl_dict:
        assert for_phrase is None, for_phrase
        for_phrase = dl_dict['for']

    if 'description' in dl_dict:
        retn = []
        reta = []
        sentences = re.split('(?<=\.) +', dl_dict['description'])
        for sentence in sentences:
            if sentence.startswith('It returns '):
                # Maybe if it's a numeric method, we shouldn't bother?
                for (pattern, nature) in [
                    ("It returns \*true\* if .+ and \*false\* otherwise.", 'a Boolean'),
                    ("It returns _argument_ converted to a Number value .+.", 'a Number'),
                    ("It returns _value_ argument converted to a non-negative integer if it is a valid integer index value.", 'a non-negative integer'),
                    ("It returns _value_ converted to a Number or a BigInt.", 'a Number or a BigInt'),
                    ("It returns _value_ converted to a numeric value of type Number or BigInt.", 'a Number or a BigInt'),
                    ("It returns a Number.", 'a Number'),
                    ("It returns a completion record which, if its \[\[Type\]\] is ~normal~, has a \[\[Value\]\] which is a Boolean.", 'a Boolean'),
                    ("It returns a completion record whose \[\[Type\]\] is ~normal~ and whose \[\[Value\]\] is a Boolean.", 'a Boolean'),
                    ("It returns a new Job Abstract Closure .+", 'a Job Abstract Closure'),
                    ("It returns a new promise resolved with _x_.", 'a promise'),
                    ("It returns an implementation-approximated value .+", 'a Number'),
                    ("It returns an integral Number representing .+", 'an integral Number'),
                    ("It returns either \*false\* or the end index of a match.", '*false* or a non-negative integer'),
                    ("It returns either ~not-matched~ or the end index of a match.", '~not-matched~ or a non-negative integer'),
                    ("It returns the BigInt value that .+", 'a BigInt'),
                    ("It returns the global object used by the currently running execution context.", 'an object'),
                    ("It returns the loaded value.", 'TBD'),
                    ("It returns the one's complement of _x_.+", 'TBD'),
                    ("It returns the sequence of Unicode code points that .+", 'a sequence of Unicode code points'),
                    ("It returns the value of its associated binding object's property whose name is the String value of the argument identifier _N_.", 'an ECMAScript language value'),
                    ("It returns the value of its bound identifier whose name is the value of the argument _N_.", 'an ECMAScript language value'),
                    ("It returns the value of the \*\"length\"\* property of an array-like object \(as a non-negative integer\).", 'a non-negative integer'),
                    ("It returns the value of the \*\"length\"\* property of an array-like object.", 'a non-negative integer'),
                ]:
                    if re.fullmatch(pattern, sentence):
                        retn.append(nature)
                        break
                else:
                    assert 0, sentence

            elif 'returning *true*, *false*, or *undefined*' in sentence:
                retn.append('a Boolean or *undefined*')

            elif 'returning *true* or *false*' in sentence:
                retn.append('a Boolean')

            elif sentence == 'Otherwise, it returns *undefined*.':
                retn.append('*undefined*'),

            elif sentence.startswith('It throws'):
                for (pattern, nature) in [
                    ('It throws an error .+',     'throw'),
                    ('It throws an exception .+', 'throw'),
                    ('It throws a \*TypeError\* exception .+', 'throw *TypeError*'),
                ]:
                    if re.fullmatch(pattern, sentence):
                        reta.append(nature)
                        break
                else:
                    assert 0, sentence

            # kludgey:
            if sentence == "It returns a completion record whose [[Type]] is ~normal~ and whose [[Value]] is a Boolean.":
                reta.append('N/A')

        return_nature_normal = ' or '.join(retn) if retn else None
        return_nature_abrupt = ' or '.join(reta) if reta else None

    else:
        return_nature_normal = None
        return_nature_abrupt = None

    # --------------------------------------------------------------------------

    # Hack this for now:
    if op_name == 'SortCompare':
        also = [
            ('_comparefn_', 'from the current invocation of the `sort` method')
        ]
    elif op_name in [
        'IsWordChar',
        'CharacterSetMatcher',
        'Canonicalize',
        'BackreferenceMatcher',
        'RegExpBuiltinExec',
        'CharacterRangeOrUnion',
    ]:
        also = regexp_also
    else:
        also = None

    op_species = other_op_species_for_section_kind_[section.section_kind]

    alg_header = AlgHeader_make(
        section = section,
        species = op_species,
        name = op_name,
        for_phrase = for_phrase,
        params = params,
        also = also,
        return_nature_normal = return_nature_normal,
        return_nature_abrupt = return_nature_abrupt,
        node_at_end_of_header = section.dl_child,
    )

    section.ste = { 'op_name': op_name }

    return alg_header

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

regexp_also = [
    # 21.2.2.1 Notation says:
    # "The descriptions below use the following variables:"
    ('_Input_'           , 'from somewhere'),
    ('_DotAll_'          , 'from somewhere'),
    ('_InputLength_'     , 'from somewhere'),
    ('_NcapturingParens_', 'from somewhere'),
    ('_IgnoreCase_'      , 'from somewhere'),
    ('_Multiline_'       , 'from somewhere'),
    ('_Unicode_'         , 'from somewhere'),
    ('_WordCharacters_'  , 'from somewhere'),
]

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_header_with_std_preamble(section):

    # Over the course of various PRs (latest #2427),
    # the first para ('preamble') of non-SDO operations
    # became standardized.
    s_ist = section.inner_source_text()
    h1_pattern = r'\n +<h1>(\S+ Semantics: )?(?P<op_name>\S+) \((?P<params_str>[^()]*)\)</h1>'
    for p_pattern in [
        r'\n +<p>The ((host|implementation)-defined )?(?P<kind>abstract operation)',
        r'\n +<p>The (?P=op_name) (?P<kind>(internal|concrete) method)',
    ]:
        pattern = h1_pattern + p_pattern
        mo = re.match(pattern, s_ist)
        if mo:
            p_dict = mo.groupdict()
            break
    else:
        return None

    # -------------------------------
    # At this point, we're committed.

    op_name = p_dict['op_name']

    for_phrase = None

    if p_dict['kind'] == 'abstract operation':
        if '::' in op_name:
            section.section_kind = 'numeric_method'
            (for_phrase, op_name) = re.split(r'(?=::)', op_name)
        else:
            section.section_kind = 'abstract_operation'

    elif p_dict['kind'] in ['host-defined abstract operation', 'implementation-defined abstract operation']:
        assert 0
        section.section_kind = 'abstract_operation'

    elif p_dict['kind'] == 'internal method':
        section.section_kind = 'internal_method'

    elif p_dict['kind'] == 'concrete method':
        if section.parent.parent.section_title == "The Environment Record Type Hierarchy":
            section.section_kind = 'env_rec_method'
        elif section.parent.parent.section_title == "Module Semantics":
            section.section_kind = 'module_rec_method'
        else:
            assert 0

    else:
        assert 0

    params = convert_parameter_listing_to_params(p_dict['params_str'])
    op_species = other_op_species_for_section_kind_[section.section_kind]

    alg_header = AlgHeader_make(
        section = section,
        species = op_species,
        name = op_name,
        for_phrase = for_phrase,
        params = params,
        node_at_end_of_header = None,
        # We could set it to section.heading_child,
        # but `node_at_end_of_header` is only used during STA,
        # and the idea is that this kind of header
        # will be changed to a structured header before applying STA.
    )

    section.ste = { 'op_name': alg_header.name }

    # --------------------------------------------------------------------------

    if 1:
        # Complain about the old header, suggest a structured one.

        posn_of_linestart_before_section = 1 + spec.text.rfind('\n', 0, section.start_posn)
        section_indent = section.start_posn - posn_of_linestart_before_section
        
        ind = ' ' * section_indent

        lines = []
        lines.append('vvvvvvvv')

        clause_start_tag = '<' + section.element_name
        for (attr_name, attr_val) in section.attrs.items():
            # suppress 'aoid' attr, because ecmarkup can generate it:
            if attr_name == 'aoid': continue

            clause_start_tag += f' {attr_name}="{attr_val}"'

            # insert 'type' attr immediately after 'id' attr:
            if attr_name == 'id':
                clause_start_tag += f''' type="{p_dict['kind']}"'''

        clause_start_tag += '>'
        lines.append(f"{ind}{clause_start_tag}")

        name_for_heading = op_name

        if section.section_kind == 'numeric_method':
            name_for_heading = for_phrase + op_name

        if section.section_title.startswith('Static Semantics:'):
            name_for_heading = 'Static Semantics: ' + name_for_heading

        if len(params) == 0:
            lines.append(f"{ind}  <h1>{name_for_heading} ( )</h1>")
        else:
            lines.append(f"{ind}  <h1>")
            lines.append(f"{ind}    {name_for_heading} (")
            for param in params:
                optionality = 'optional ' if param.punct == '[]' else ''
                lines.append(f"{ind}      {optionality}{param.name}: {param.nature},")
            lines.append(f"{ind}    )")
            lines.append(f"{ind}  </h1>")

        lines.append(f'{ind}  <dl class="header">')

        if False and for_phrase and kind != 'numeric method':
            _.dt("for")
            _.dd(self.for_phrase)
        
        lines.append(f'{ind}  </dl>')
        lines.append("^^^^^^^^")
        suggestion = '\n'.join(lines)

        msg_at_posn(section.inner_start_posn, f"Should use a structured header? e.g.:\n{suggestion}")

    return alg_header

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_function_section(section):

    if (
        section.section_title in [
            'Non-ECMAScript Functions',
            'URI Handling Functions',
        ]
        or
        section.section_title.startswith('IfAbrupt')
    ):
        # The section title would match one of the patterns below,
        # but we don't want it to,
        # because the section doesn't define a function.
        return False

    pattern_results = [

        (r'(?P<prop_path>[A-Z]\w+) \( \. \. \. \)',           'function_property_xref'),

        (r'(?P<prop_path>.+) Functions',                      'anonymous_built_in_function'),
        (r'(?P<prop_path>%ThrowTypeError%) <PARAMETER_LIST>', 'anonymous_built_in_function'),

        (r'(?P<prop_path>[A-Z]\w+) <PARAMETER_LIST>',         'CallConstruct'),
        (r'(?P<prop_path>_[A-Z]\w+_) <PARAMETER_LIST>',       'CallConstruct'),
        (r'(?P<prop_path>%[A-Z]\w+%) <PARAMETER_LIST>',       'CallConstruct'),

        (r'(?P<prop_path>get <PROP_PATH>)',                   'accessor_property'),
        (r'(?P<prop_path>set <PROP_PATH>)',                   'accessor_property'),

        (r'(?P<prop_path><PROP_PATH>) <PARAMETER_LIST>',      'function_property'),
        (r'(?P<prop_path>\w+) <PARAMETER_LIST>',              'function_property'),

    ]
    for (pattern, result) in pattern_results:
        pattern = (
            pattern
            .replace('<PARAMETER_LIST>', r'\((?P<params_str>[^()]*)\)')
            .replace('<PROP_PATH>',      r'(\w+|%\w+%)(\.\w+| \[ @@\w+ \])+')
        )
        mo = re.fullmatch(pattern, section.section_title)
        if mo:
            break
    else:
        return False

    # -----------

    check_section_title(section)

    section.section_kind = result

    section.ste = {}

    if section.section_kind == 'function_property_xref':
        assert section.bcen_str == 'p'
        assert re.fullmatch(
            r'<p>See <emu-xref href="#[^"]+"></emu-xref>.</p>',
            section.block_children[0].source_text()
        )
        return True

    p_dict = mo.groupdict()
    prop_path = p_dict['prop_path']

    if 'params_str' in p_dict:
        params = convert_parameter_listing_to_params(p_dict['params_str'])
    elif section.section_title.startswith('get '):
        assert section.section_kind == 'accessor_property'
        # The spec leaves off the empty parameter list
        params = []
    else:
        params = None

    n_emu_algs = section.bcen_list.count('emu-alg')

    # ======================================================

    # Handle the function that's declared by the section-heading.

    bif_species = {
        'CallConstruct'               : 'bif: value of data property',
        'accessor_property'           : 'bif: accessor function',
        'anonymous_built_in_function' : 'bif: * per realm',
        'function_property'           : 'bif: value of data property',
    }[section.section_kind]

    if n_emu_algs == 0:
        # Various possibilities:
        # - A Math function that we merely constrain, via a bullet-list.
        # - "This function is like that function" (except different, maybe).
        # - Other functions that we only define in prose.
        emu_alg_posn_a = len(section.block_children)
        emu_alg_a = None
    else:
        emu_alg_posn_a = section.bcen_list.index('emu-alg')
        emu_alg_a = section.block_children[emu_alg_posn_a]

    # convert heading-style to elsewhere-style:
    # prop_path = ( prop_path
    #     .replace(' [ ', '[')
    #     .replace(' ]',  ']')
    # )

    alg_header = AlgHeader_make(
        section = section,
        species = bif_species,
        name = prop_path,
        params = params,
        node_at_end_of_header = section.heading_child,
        preamble_nodes = section.block_children[0:emu_alg_posn_a],
    )

    if emu_alg_a:
        AlgHeader_add_definition(alg_header, None, emu_alg_a)

    # ======================================================

    # Handle any other algorithm in the section.

    if n_emu_algs > 1:
        # There's only one case of this left. (see PR #2302 or #2305)
        assert prop_path == '%TypedArray%.prototype.sort'
        assert n_emu_algs == 2

        # The first emu-alg is only the *start* of the full algorithm,
        # but we still want a header for the function. (created above)

        # The second emu-alg defines the TypedArray SortCompare operation.
        emu_alg_posn_b = section.bcen_list.index('emu-alg', emu_alg_posn_a+1)
        emu_alg_b = section.block_children[emu_alg_posn_b]

        headers.oh_warn()
        headers.oh_warn(f"In {section.section_num} {section.section_title},")
        headers.oh_warn(f"    an algorithm gets no info from heading")

        assert [
            p.source_text()
            for p in section.block_children[emu_alg_posn_a+1:emu_alg_posn_b]
        ] == [
            '<p>The following version of SortCompare is used by %TypedArray%`.prototype.sort`. It performs a numeric comparison rather than the string comparison used in <emu-xref href="#sec-array.prototype.sort"></emu-xref>.</p>',
            '<p>The abstract operation TypedArraySortCompare takes arguments _x_ and _y_. It also has access to the _comparefn_ and _buffer_ values of the current invocation of the `sort` method. It performs the following steps when called:</p>',
        ]

        alg_header = AlgHeader_make(
            section = section,
            species = 'op: solo',
            name = 'TypedArraySortCompare',
            params = [
                AlgParam('_x_', '', 'unknown'),
                AlgParam('_y_', '', 'unknown'),
            ],
            also = [
                ('_comparefn_', 'from the `sort` method'),
                ('_buffer_',    'from the `sort` method'),
            ],
            node_at_end_of_header = section.block_children[emu_alg_posn_a+1],
        )

        AlgHeader_add_definition(alg_header, None, emu_alg_b)

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_other_section(section):

    check_section_title(section)

    # We infer a section's kind almost entirely based on its title.
    pattern_results = [
            (r'Implicit Completion Values',                        'shorthand'),
            (r'Throw an Exception',                                'shorthand'),
            (r'ReturnIfAbrupt',                                    'shorthand'),
            (r'ReturnIfAbrupt Shorthands',                         'shorthand'),
            (r'Await',                                             'shorthand'),
            (r'IfAbruptRejectPromise \( _value_, _capability_ \)', 'shorthand'),
            (r'IfAbruptCloseIterator \( _value_, _iteratorRecord_ \)', 'shorthand'),

            (r'.+ Instances',             'properties_of_instances'),
            (r'Module Namespace Objects', 'properties_of_instances'),

            (r'Properties of Valid Executions', 'catchall'),
            (r'(Additional )?Properties of .+', 'properties_of_an_intrinsic_object'),
            (r'The [\w%.]+ Object',             'properties_of_an_intrinsic_object'),

            (r'The \w+ Constructor',               'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The _NativeError_ Constructors',    'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The _TypedArray_ Constructors',     'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The %TypedArray% Intrinsic Object', 'Call_and_Construct_ims_of_an_intrinsic_object'),

            (r'_NativeError_ Object Structure', 'loop'),

            (r'Non-ECMAScript Functions',                          'catchall'),
            (r'URI Handling Functions',                            'group_of_properties2'),
            (r'(Value|Function|Constructor|Other) Properties of .+', 'group_of_properties1'),

            (r'<PROP_PATH>',                                 'other_property'),
            (r'[a-z]\w+|Infinity|NaN',                       'other_property'),
            (r'@@\w+',                                       'other_property'),

            (r'.*',                                'catchall'),
        ]
    # Look for the first pattern in `pattern_results`
    # that matches (via re.fullmatch) `section.section_title`.
    for (pattern, result) in pattern_results:
        pattern = (
            pattern
            .replace('<PROP_PATH>',      r'(\w+|%\w+%)(\.\w+| \[ @@\w+ \])+')
        )
        mo = re.fullmatch(pattern, section.section_title)
        if mo:
            break
    else:
        assert 0, section.section_title

    assert isinstance(result, str)
    section.section_kind = result

    section.ste = {}

    if section.parent.section_title == 'Terms and Definitions' and section.section_kind == 'other_property':
        section.section_kind = 'catchall'

    if section.parent.section_title == 'Other Properties of the Global Object':
        assert section.section_kind == 'catchall'
        section.section_kind = 'other_property_xref'

    # -----------

    # The section_title doesn't declare an operation or a function-property,
    # so we don't expect an algorithm.
    # But sometimes there are some anyway.

    for child in section.block_children:
        if child.element_name == 'emu-eqn':
            handle_emu_eqn(child, section)

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        if section.section_title == 'Mathematical Operations':
            Pseudocode.ensure_alg('op: solo', 'abs')
            Pseudocode.ensure_alg('op: solo', 'min')
            Pseudocode.ensure_alg('op: solo', 'max')
            Pseudocode.ensure_alg('op: solo', 'floor')
            Pseudocode.ensure_alg('op: solo', '\U0001d53d')
            Pseudocode.ensure_alg('op: solo', '\u211d')
            Pseudocode.ensure_alg('op: solo', '\u2124')

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]

        if section.section_title == 'Algorithm Conventions':
            # It's just the example of algorithm layout.
            # Skip it.
            pass

        elif section.section_title == 'Array.prototype [ @@unscopables ]':
            # The section_title identifies a data property,
            # and the algorithm results in its initial value.
            # So CreateIntrinsics invokes this alg, implicitly and indirectly.

            alg_header = AlgHeader_make(
                section = section,
                species = 'op: solo',
                name = 'initializer for @@unscopables',
                params = [],
                node_at_end_of_header = section.block_children[emu_alg_posn-1],
            )

            AlgHeader_add_definition(alg_header, None, emu_alg)

        elif section.section_kind == 'properties_of_an_intrinsic_object':
            # In addition to telling you about the intrinsic object,
            # it also defines an abstract operation that is used
            # by the object's function properties.
            mo = re.fullmatch(r'Properties of the (\w+) Prototype Object', section.section_title)
            which = mo.group(1)
            op_name = f"this{'Time' if which == 'Date' else which}Value"

            headers.oh_warn()
            headers.oh_warn(f"In {section.section_num} {section.section_title},")
            headers.oh_warn(f"    an algorithm gets no info from heading")

            preamble = section.block_children[emu_alg_posn-1]
            assert preamble.source_text() == f'<p>The abstract operation <dfn id="{op_name.lower()}" aoid="{op_name}" oldids="sec-{op_name.lower()}">{op_name}</dfn> takes argument _value_. It performs the following steps when called:</p>'

            alg_header = AlgHeader_make(
                section = section,
                species = 'op: solo',
                name = op_name,
                params = [ AlgParam('_value_', '', 'unknown') ],
                node_at_end_of_header = preamble,
            )

            AlgHeader_add_definition(alg_header, None, emu_alg)

        elif section.section_title == 'The Abstract Closure Specification Type':
            # The emu-alg is an example showing the definition and use
            # of an abstract closure.
            # Skip it.
            pass

        else:
            assert 0, (section.section_num, section.section_title)

    else:

        if section.section_kind == 'shorthand':
            if section.section_title == 'Implicit Completion Values':
                Pseudocode.ensure_alg('shorthand', 'Completion')
            elif section.section_title in [
                'ReturnIfAbrupt',
                'Await',
            ]:
                Pseudocode.ensure_alg('shorthand', section.section_title)
            elif section.section_title == 'IfAbruptRejectPromise ( _value_, _capability_ )':
                Pseudocode.ensure_alg('shorthand', 'IfAbruptRejectPromise')
            else:
                pass
                # print('>', section.section_num, section.section_title)
            pass
        elif section.section_title == 'Syntax-Directed Operations':
            # just examples
            pass
        else:
            assert 0, (section.section_num, section.section_title)

    return True

# ------------------------------------------------------------------------------

def handle_emu_eqn(emu_eqn, section):
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

    tree = Pseudocode.parse(emu_eqn)
    if tree is None: return

    assert tree.prod.lhs_s == '{EMU_EQN_DEF}'
    [child] = tree.children

    if child.prod.lhs_s == '{CONSTANT_DEF}':
        [constant_name, dec_int_lit] = child.children[0:2]
        assert constant_name.source_text() == aoid
        # XXX Pseudocode.alg_add_defn('constant', aoid, None, dec_int_lit, section)

    elif child.prod.lhs_s == '{OPERATION_DEF}':
        [op_name, parameter, body] = child.children
        assert op_name.source_text() == aoid
        parameter_name = parameter.source_text()

        alg_header = AlgHeader_make(
            section = section,
            species = 'op: solo',
            name = aoid,
            params = [ AlgParam(parameter_name, '', 'unknown') ],
            node_at_end_of_header = emu_eqn,
        )

        AlgHeader_add_definition(alg_header, None, body)

    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def convert_parameter_listing_to_params(parameter_listing):
    params = []
    parameter_listing = parameter_listing.strip()
    if parameter_listing != '':
        if parameter_listing == '_value1_, _value2_, ..._values_':
            # Math.{hypot,max,min}
            parameter_listing = '..._values_'
        elif parameter_listing in [
            '_p1_, _p2_, ..., _pn_, _body_', # old
            '_p1_, _p2_, &hellip; , _pn_, _body_' # new
        ]:
            # Function, GeneratorFunction, AsyncGeneratorFunction, AsyncFunction
            parameter_listing = '..._args_ [ , _body_ ]'

        param_strs = parameter_listing.split(', ')
        subsequent_are_optional = False
        for param_str in param_strs:
            if param_str.startswith('[ '):
                subsequent_are_optional = True
                param_str = param_str[2:]

            mo = re.match(r'^(\.\.\.)?(_\w+_)(.*)$', param_str)
            assert mo, repr(parameter_listing)
            (opt_dots, param_name, suffix) = mo.groups()


            assert not (opt_dots and subsequent_are_optional)

            if opt_dots:
                param_punct = '...'
            elif subsequent_are_optional:
                param_punct = '[]'
            else:
                param_punct = ''

            params.append( AlgParam(param_name, param_punct, 'unknown') )

            if re.match(r'^( \])*$', suffix):
                pass
            elif suffix == ' [ ':
                subsequent_are_optional = True
            else:
                assert 0, repr(parameter_listing)

    return params

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_changes_section(section):

    def blah_solo_op(op_name, emu_alg):
        Pseudocode.parse(emu_alg)

    def blah_composite_sdo(op_name, emu_grammar, emu_alg):
        Pseudocode.parse(emu_alg)

    def blah_early_error(emu_grammar, ul):
        handle_early_error(emu_grammar, ul, None)

    # For calls to scan_section, we're going to assume this holds,
    # but be sure to undo it if we ultimately return False.
    section.section_kind = 'changes'

    def e(s):
        return (s
            .replace('EMU-XREF',    r'<emu-xref [^<>]+></emu-xref>')
            .replace('EMU-GRAMMAR', r'<emu-grammar>[^<>]+</emu-grammar>')
            .replace('NONTERMINAL', r'\|\w+\|')
        )

    # --------------------------------------------------------------------------
    if section.section_title == 'Pattern Semantics' and section.section_num.startswith('B.'):
        # B.1.4.4

        patterns = [

            # -------------------
            # Use an existing algorithm, but with a substitution:
            (
                [
                    ('p', e("Within EMU-XREF reference to &ldquo;EMU-GRAMMAR &rdquo; are to be interpreted as meaning &ldquo;EMU-GRAMMAR &rdquo; or &ldquo;EMU-GRAMMAR &rdquo;.")),
                ],
                lambda p: None
            ),
            (
                [
                    ('p', e("The production EMU-GRAMMAR evaluates the same as the production EMU-GRAMMAR but with NONTERMINAL substituted for NONTERMINAL\.")),
                ],
                lambda p: None
            ),
            (
                [
                    ('p', e("\w+ \(EMU-XREF\) evaluation rules for the EMU-GRAMMAR and EMU-GRAMMAR productions are also used for the NONTERMINAL productions, but with NONTERMINAL substituted for NONTERMINAL.")),
                ],
                lambda p: None
            ),
            (
                [
                    ('p', e("\w+ \(EMU-XREF\) evaluation rules for the NONTERMINAL productions except for EMU-GRAMMAR are also used for the NONTERMINAL productions, but with NONTERMINAL substituted for NONTERMINAL. The following evaluation rules, with parameter _direction_, are also added:")),
                ],
                lambda p: None
            ),

            # -------------------
            # Give a full emu-alg
            (
                # 2 cases:
                [
                    ('p', e("The production EMU-GRAMMAR evaluates as follows:")),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_composite_sdo('regexp-Evaluate', p.children[1], emu_alg)
            ),
            (
                # 4 cases:
                [
                    ('p', e("(\w+) \(EMU-XREF\) includes the following additional evaluation rule:")),
                    ('p', e("The production EMU-GRAMMAR evaluates as follows:")),
                    'emu-alg'
                ],
                lambda p1, p2, emu_alg: blah_composite_sdo('regexp-Evaluate', p2.children[1], emu_alg)
            ),
            (
                # 2 cases:
                [
                    ('p', e("(?:\w+) \(EMU-XREF\) modifies the following evaluation rule:")),
                    ('p', e("The production EMU-GRAMMAR evaluates as follows:")),
                    'emu-alg'
                ],
                lambda p1, p2, emu_alg: blah_composite_sdo('regexp-Evaluate', p2.children[1], emu_alg)
            ),

            # -----------------------

            (
                # Introducing the section
                [
                    ('p', e("The semantics of EMU-XREF is extended as follows:")),
                ],
                None
            ),
            (
                # 
                [
                    ('p', e("(\w+) \(EMU-XREF\) includes the following additional evaluation rules?:")),
                ],
                None
            ),

            # -------------------
            (
                ['emu-note'],
                None
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif (mo := re.fullmatch('Changes to ([A-Z]\w+)', section.section_title)):
        op_name = mo.group(1)
        patterns = [
            (
                # B.3.2.{1,2,3,6}:
                [
                    ('p', e(f'During {op_name} the following steps are performed in place of step EMU-XREF:')),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_solo_op(op_name, emu_alg)
            ),
            (
                # B.3.6.1:
                [
                    ('p', e('The result column in EMU-XREF for an argument type of Object is replaced with the following algorithm:')),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_solo_op(op_name, emu_alg)
            ),
            (
                # B.3.6.2:
                [
                    ('p', e(f'The following steps replace step EMU-XREF of the {op_name} algorithm:')),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_solo_op(op_name, emu_alg)
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif (mo := re.fullmatch('Changes to (.+) Static Semantics: Early Errors', section.section_title)):
        # B.3.2.{4,5}
        patterns = [
            (
                [
                    ('p', e('The rules for the following production in EMU-XREF are modified with the addition of the <ins>highlighted</ins> text:')),
                    'emu-grammar',
                    'ul',
                ],
                lambda p, emu_grammar, ul: blah_early_error(emu_grammar, ul)
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_title == 'VariableStatements in Catch Blocks':
        # B.3.4
        patterns = [
            (
                [
                    ('p', e('The content of subclause EMU-XREF is replaced with the following:')),
                    'emu-grammar',
                    'ul'
                ],
                lambda p, emu_grammar, ul: blah_early_error(emu_grammar, ul)
            ),
            (
                ['emu-note'],
                None
            ),
            (
                [
                    ('p', e('.+ This change is accomplished by modifying the algorithm of EMU-XREF as follows:')),
                ],
                None
            ),
            (
                [
                    ('p', e('Step EMU-XREF is replaced by:')),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_solo_op('EvalDeclarationInstantiation', emu_alg)
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_title == 'Initializers in ForIn Statement Heads':
        # B.3.5
        patterns = [
            (
                [
                    ('p', e('The following augments the NONTERMINAL production in EMU-XREF:')),
                    'emu-grammar',
                    ('p', 'This production only applies when parsing non-strict code.'),
                ],
                lambda p, emu_grammar, _: None
            ),
            (
                [
                    ('p', e('The (?:static|runtime) semantics of (\w+) in EMU-XREF are augmented with the following:')),
                    'emu-grammar',
                    'emu-alg',
                ],
                lambda op_name, emu_grammar, emu_alg: blah_composite_sdo(op_name, emu_grammar, emu_alg)
            ),
        ]
        scan_section(section, patterns) 

    # --------------------------------------------------------------------------
    elif (mo := re.fullmatch('Changes to (.+)', section.section_title)):
        # B.3.6.3
        assert mo.group(1) == 'the `typeof` Operator'
        assert section.bcen_str == 'p emu-table'
        patterns = [
            (
                [
                    ('p', e('The following table entry is inserted into EMU-XREF immediately preceding the entry for "Object \(implements \[\[Call\]\]\)":')),
                    'emu-table'
                ],
                lambda p, emu_table: None
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    else:
        del section.section_kind
        return False

    # ==========================================================================

    section.ste = {}

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_section_title(section):
    h1 = section.heading_child
    title = section.section_title

    # Check capitalization.
    if section.parent.section_title != 'Terms and Definitions':
        mo = re.search(r' \b(?!(an|and|for|in|of|on|the|to|with))([a-z]\w+)', title)
        if mo:
            msg_at_posn(
                h1.inner_start_posn + mo.start() + 1,
                "title word '%s' should be capitalized?" % mo.group(2)
            )

    # Check references to well-known symbols.
    mo1 = re.search('\[ *@', title)
    if mo1:
        mo2 = re.search(r'( |^)\[ @@\w+ \]( |$)', title)
        if not mo2:
            msg_at_posn(
                h1.inner_start_posn + mo1.start(),
                "Title's reference to well-known symbol does not conform to expected pattern"
            )

    # Check parentheses and spaces
    assert title.count('(') <= 1
    assert title.count(')') <= 1
    lpp = title.find('(')
    if lpp >= 0:
        if re.search(r' \(( .+)? \)( Concrete Method)?$', title):
            # space before and after '('
            # space before ")"
            # If param list is empty, just one space between parens.
            pass
        elif title == 'RegExp (Regular Expression) Objects':
            # Use of parens that isn't a parameter list.
            pass
        else:
            msg_at_posn(
                h1.inner_start_posn + lpp,
                "Something odd here wrt parens + spaces"
            )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _set_bcen_attributes(section):
    # Set section attributes:
    # .bcen_{list,str,set}

    # "bcen" = "block children element names"
    section.bcen_list = [
        c.element_name
        for c in section.block_children
    ]
    section.bcen_str = ' '.join(section.bcen_list)
    section.bcen_set = set(section.bcen_list)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _print_section_kinds(section):
    global g_sections_f
    if section.is_root_section:
        g_sections_f = shared.open_for_output('sections')
    else:
        if not(hasattr(section, 'section_kind')): section.section_kind = 'UNSET!'
        print("%s%-47s%s %s" % (
                '  '*(section.section_level-1),
                section.section_kind,
                section.section_num,
                section.section_title
            ),
            file=g_sections_f
        )

    for child in section.section_children:
        _print_section_kinds(child)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _check_aoids(section):
    if section.is_root_section:
        pass

    else:
        aoid = section.attrs.get('aoid', None)
        op_name = section.ste.get('op_name', None)

        if section.section_kind == 'shorthand':
            assert op_name is None
            # aoid might or might not be None

        else:

            if section.section_kind == 'catchall':
                assert op_name is None

                if section.parent.section_title == 'Relations of Candidate Executions':
                    # Should we have a 'relation' kind?
                    # (The Memory Model clauses are weird.)
                    expected_aoid = section.section_title
                else:
                    expected_aoid = None

            elif section.section_kind == 'syntax_directed_operation':
                if op_name in [
                    'MV',
                    'Evaluation',
                    'HasCallInTailPosition',
                    'regexp-Evaluate',
                ]:
                    # After 2271, there are still a few SDOs that are defined piecewise.
                    expected_aoid = None
                elif section.element_name == 'emu-annex' and op_name in [
                    'IsCharacterClass',
                    'CharacterValue',
                ]:
                    # These can't duplicate the aoid of the main-spec clause.
                    expected_aoid = None
                else:
                    expected_aoid = op_name

            else:
                expected_aoid = None

            if aoid != expected_aoid:
                if aoid is None:
                    msg = f'Should this clause have aoid="{expected_aoid}"?'
                elif expected_aoid is None:
                    msg = f"Didn't expect this clause to have an aoid"
                else:
                    msg = f'Expected aoid="{expected_aoid}"'

                msg_at_posn(section.start_posn, msg)

    for child in section.section_children:
        _check_aoids(child)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _check_section_order(section):
    # In some sections, the subsections should be in "alphabetical order".

    if section.is_root_section:
        pass
    else:

        if section.section_kind in [
            'group_of_properties1',
            'group_of_properties2',
            'properties_of_an_intrinsic_object',
            'properties_of_instances',
        ]:
            prev_title = None
            prev_t = None
            for child in section.section_children:
                if child.section_kind not in [
                    'group_of_properties1',
                    'group_of_properties2',
                    'catchall',
                    'anonymous_built_in_function',
                ]:
                    assert re.search(r'_property(_xref)?$', child.section_kind), child.section_kind
                    t = child.section_title
                    t = t.lower()
                    t = t.replace('int8', 'int08')
                    t = re.sub(r'^get ', '', t)
                    t = re.sub(r'(^|\.)__', r'\1zz__', t) # to put __proto__ last
                    if section.section_title == 'Properties of the RegExp Prototype Object':
                        t = re.sub(r' \[ @@(\w+) \]', r'.\1', t)
                    else:
                        t = re.sub(r' \[ @@(\w+) \]', r'.zz_\1', t)
                    if prev_t is not None and t <= prev_t:
                        msg_at_posn(child.start_posn, '"%s" should be before "%s"' % (child.section_title, prev_title))
                    prev_t = t
                    prev_title = child.section_title

    for child in section.section_children:
        _check_section_order(child)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def scan_section(section, patterns):
    try:
        results = scan_nodes(section.block_children, patterns)
    except ScanError as e:
        msg_at_posn(e.node.start_posn, f"Unexpected node in {section.section_kind} section")
        results = []
    return results

def scan_nodes(hnodes, patterns):
    results = []
    next_i = 0
    while next_i < len(hnodes):
        for (b, (pattern, processor)) in enumerate(patterns):
            assert isinstance(pattern, list)

            n = len(pattern)
            if next_i + n > len(hnodes):
                # This pattern is too long to match at this point in hnodes.
                continue

            match_results = [
                node_matches_atom(child, element_atom)
                for (child, element_atom) in zip(hnodes[next_i:], pattern)
            ]
            if not all(match_results):
                # pattern didn't match
                continue

            matched_nodes = hnodes[next_i : next_i + n]
            if processor is None:
                pass
            elif processor == 'print':
                print()
                for node in matched_nodes:
                    print('>', node.source_text())
            elif callable(processor):
                # arguments = matched_nodes
                arguments = []
                for (matched_node, match_result) in zip(matched_nodes, match_results):
                    # If the atom captured something(s), use that/them as the arguments to tha callable.
                    if hasattr(match_result, 'groups') and len(match_result.groups()) > 0:
                        arguments.extend(match_result.groups())
                    else:
                        arguments.append(matched_node)
                result = processor(*arguments)
                if type(result) == type([]):
                    results.extend(result)
                else:
                    results.append(result)
            else:
                assert 0, processor
            next_i += n
            break
        else:
            raise ScanError(hnodes[next_i])
    return results

@dataclass(frozen = True)
class ScanError(BaseException):
    node: HNode

def node_matches_atom(node, atom):
    if isinstance(atom, str):
        return (node.element_name == atom)
    elif isinstance(atom, tuple):
        (desired_element_name, desired_content_re) = atom
        return (
            node.element_name == desired_element_name
            and
            re.fullmatch(desired_content_re, node.inner_source_text())
        )
    else:
        assert 0, atom

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

@dataclass
class AlgParam:
    name: str
    punct: str # '' | '[]' | '...'
    nature: str

def AlgHeader_set_attributes_from_params(alg_header, params):
    # Sets .param_nature_, .param_names, .rest_params, and .optional_params.

    alg_header.param_names = []

    for param in params:
        assert isinstance(param, AlgParam)

        if param.nature != 'unknown':
            alg_header.param_nature_[param.name] = param.nature

        alg_header.param_names.append(param.name)

        if param.punct == '...':
            alg_header.rest_params.add(param.name)
        elif param.punct == '[]':
            alg_header.optional_params.add(param.name)
        elif param.punct == '':
            pass
        else:
            assert 0, param_punct

# ------------------------------------------------------------------------------

def AlgHeader_make(
    *,
    section,
    species,
    name,
    params,
    node_at_end_of_header,
    for_phrase           = None,
    return_nature_normal = None,
    return_nature_abrupt = None,
    also                 = None,
    preamble_nodes       = None,
):
    alg_header = headers.AlgHeader()
    alg_header.section = section
    alg_header.species = species
    alg_header.name = name
    alg_header.node_at_end_of_header = node_at_end_of_header
    alg_header.for_phrase = for_phrase
    alg_header.return_nature_normal = return_nature_normal
    alg_header.return_nature_abrupt = return_nature_abrupt
    alg_header.also = also

    if params is not None:
        AlgHeader_set_attributes_from_params(alg_header, params)

    if preamble_nodes:
        headers.check_header_against_prose(alg_header, preamble_nodes)

    alg_header.finish_initialization()

    return alg_header

# ------------------------------------------------------------------------------

def AlgHeader_add_definition(alg_header, discriminator, hnode_or_anode, make_annex_B_exception=False):
    alg_defn = Pseudocode.alg_add_defn(
        alg_header.species,
        alg_header.name,
        discriminator,
        hnode_or_anode,
        alg_header.section,
    )
    if not make_annex_B_exception or not alg_header.section.section_num.startswith('B'):
        alg_header.add_defn(alg_defn)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
