
# ecmaspeak-py/Section.py:
# Identify "sections" in the spec, and ascertain their 'kind'.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, string, time, pdb, types

import shared
from shared import stderr, msg_at_node, msg_at_posn, spec
from HTML import HNode
import Pseudocode
import function_preambles as fpr
import intrinsics
from intrinsics import get_pdn, S_Property, S_InternalSlot
from algos import ensure_alg, AlgParam, AlgHeader, AlgDefn, write_header_info, check_alg_consistency
import records
from NodeGrammar import NodeGrammar

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def make_and_check_sections():
    stderr("make_and_check_sections ...")

    fpr.oh_inc_f = shared.open_for_output('oh_warnings')

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

        _set_section_kind(section)

    stderr()

    t_end = time.time()
    stderr(f"analyzing sections took {t_end-t_start:.2f} seconds")

    Pseudocode.check_emu_alg_coverage()
    Pseudocode.check_emu_eqn_coverage()
    Pseudocode.report_all_parsers()

    fpr.oh_inc_f.close()
    fpr.note_unused_rules()

    _print_section_kinds()
    _print_unused_ispl()
    _print_intrinsic_facts()
    _check_aoids()
    _check_section_order()

    write_header_info()
    check_alg_consistency()

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
    _make_section_tree_r(doc_node, 0)
    return doc_node

def _make_section_tree_r(section, section_level):
    section.section_level = section_level
    section.is_root_section = (section_level == 0)

    assert not section.inline_child_element_names
    # if section.inline_child_element_names:
    #     msg_at_node(
    #         section,
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
        msg_at_node(
            section,
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
    # .alg_headers

    section.has_structured_header = False
    section.alg_headers = []

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

    check_id(section)

    extract_intrinsic_info(section)

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

    alg_header = AlgHeader_make(
        section = section,
        species = 'op: discriminated by syntax: early error',
        name = 'Early Errors',
        params = [],
        node_at_end_of_header = section.heading_child,
    )

    patterns = [
        (
            # 89 cases, the vast majority
            ['emu-grammar', 'ul'],
            lambda emu_grammar, ul: (emu_grammar, None, ul)
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

        EarlyErrorAlgDefn(alg_header, emu_grammar, ul, p)

    return True

# ------------------------------------------------------------------------------

class EarlyErrorAlgDefn(AlgDefn):
    # An early error block consists of:
    # - an <emu-grammar> element (containing 1 or more productions),
    # - a <ul> element (containing 1 or more "It is a Syntax Error" items), and
    # - rarely, a <p> element that constrains the applicability of the rules.

    def __init__(self, alg_header, emu_grammar, ul, kludgey_p):
        assert (
            alg_header is None
            # only for Annex B, because we want to syntax-check the rules,
            # but not add them to the alg_header
            or
            isinstance(alg_header, AlgHeader)
        )
        assert (
            isinstance(emu_grammar, HNode)
            and
            emu_grammar.element_name == 'emu-grammar'
        )
        assert (
            isinstance(ul, HNode)
            and
            ul.element_name == 'ul'
        )
        assert kludgey_p is None or (
            isinstance(kludgey_p, HNode)
            and
            kludgey_p.element_name == 'p'
        )

        self.parent_header = alg_header
        self.emu_grammar = emu_grammar
        self.ul = ul
        self.kludgey_p = kludgey_p

        # ----

        self.emu_grammars = [emu_grammar]

        self.lis = []
        self.anodes = []

        for li in ul.children:
            if li.element_name == '#LITERAL':
                assert li.source_text().isspace()
            elif li.element_name == 'li':
                self.lis.append(li)

                tree = Pseudocode.parse(li, 'early_error')
                if tree is None:
                    ee_rule = None
                else:
                    assert tree.prod.lhs_s == '{EARLY_ERROR_RULE}'
                    [ee_rule] = tree.children
                    assert ee_rule.prod.lhs_s == '{EE_RULE}'
                self.anodes.append(ee_rule)

            else:
                assert 0, li.element_name

        # ----

        if alg_header: alg_header.u_defns.append(self)

    def get_puk_set(self):
        return self.emu_grammar.puk_set

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_sdo_section(section):

    # Since the merge of PR #2271,
    # almost all SDO sections are identified by `type="sdo"`.
    if section.attrs.get('type') == 'sdo':
        if section.section_title == 'Runtime Semantics: Evaluation':
            # These don't have a <dl class="header">,
            # and so don't fit my idea of a structured header.
            section.section_kind = 'syntax_directed_operation'
            alg_header = AlgHeader_make(
                section = section,
                species = 'op: discriminated by syntax: steps',
                name = 'Evaluation',
                params = [],
                node_at_end_of_header = section.heading_child
            )
        else:
            alg_header = _handle_structured_header(section)
            if alg_header is None: return True

    else:
        # But there are various clauses that don't get `type="sdo"`
        # that we neverthless want to mark as SDO sections...

        # A clause that only *partially* defines an SDO:
        if section.section_title in [
            'Runtime Semantics: MV',
            'Static Semantics: MV',
        ]:
            sdo_name = re.sub('.*: ', '', section.section_title)

        # An Annex B clause that extends the semantics of a main-body SDO:
        elif section.section_title in [
            'Static Semantics: IsCharacterClass',
            'Static Semantics: CharacterValue',
        ]:
            # B.1.2.3
            # B.1.2.4
            sdo_name = re.sub('.*: ', '', section.section_title)

        else:
            # Anything else isn't an SDO section.
            return False

        section.section_kind = 'syntax_directed_operation'
        params = []
        return_nature_node = None

        alg_header = AlgHeader_make(
            section = section,
            species = 'op: discriminated by syntax: steps',
            name = sdo_name,
            params = params,
            node_at_end_of_header = section.heading_child,
            return_nature_node = return_nature_node,
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
                # 3 cases
                [
                    ('p', r'Every grammar production alternative in this specification which is not listed below implicitly has the following default definition of \w+:'),
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
            UsualSdoAlgDefn(alg_header, emu_grammar, emu_alg)

    return True

class UsualSdoAlgDefn(AlgDefn):
    def __init__(self, alg_header, emu_grammar, emu_alg):
        assert isinstance(alg_header, AlgHeader)
        assert (
            emu_grammar is None
                # and self.parent_header.name in ops_with_implicit_defns
            or
            isinstance(emu_grammar, HNode) and emu_grammar.element_name == 'emu-grammar'
        )
        assert isinstance(emu_alg, HNode) and emu_alg.element_name == 'emu-alg'

        self.parent_header = alg_header
        self.emu_grammar = emu_grammar
        self.emu_alg = emu_alg

        anode = Pseudocode.parse(emu_alg)
        assert anode is None or anode.prod.lhs_s == '{EMU_ALG_BODY}'

        self.emu_grammars = [emu_grammar]
        self.anodes = [anode]

        alg_header.u_defns.append(self)

    def get_puk_set(self):
        if self.emu_grammar is None:
            puk = ('*default*', '', '')
            puk_set = set([puk])
        else:
            puk_set = self.emu_grammar.puk_set
            if not puk_set:
                stderr(f"! sdo_coverage may be broken because no puk_set for {self.emu_grammar.source_text()}")

        return puk_set

# ------------------------------------------------------------------------------

def handle_inline_sdo_section_body(section, alg_header):

    for bc in section.block_children:
        if bc.element_name == 'ul':
            # Each <li> in the <ul> is an "inline SDO".
            for ul_child in bc.children:
                if ul_child.is_whitespace(): continue
                assert ul_child.element_name == 'li'
                InlineSdoAlgDefn(alg_header, ul_child)

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

class InlineSdoAlgDefn(AlgDefn):
    def __init__(self, alg_header, li):
        assert isinstance(alg_header, AlgHeader)
        assert isinstance(li, HNode) and li.element_name == 'li'

        self.parent_header = alg_header
        self.li = li

        self.emu_grammars = [* li.each_child_named('emu-grammar')]
        assert len(self.emu_grammars) > 0

        INLINE_SDO_RULE = Pseudocode.parse(li, 'inline_sdo')
        if INLINE_SDO_RULE is None:
            rule_expr_anode = None

        else:
            assert INLINE_SDO_RULE.prod.lhs_s == '{INLINE_SDO_RULE}'
            [ISDO_RULE] = INLINE_SDO_RULE.children
            assert str(ISDO_RULE.prod) == '{ISDO_RULE} : The {cap_word} {OF_PRODUCTIONS} is {EXPR}.'

            [cap_word, of_productions, rule_expr_anode] = ISDO_RULE.children

            [rule_sdo_name] = cap_word.children
            assert rule_sdo_name == alg_header.name

            emu_grammar_anodes = of_productions.children

            assert len(self.emu_grammars) == len(emu_grammar_anodes)
            for (emu_grammar_hnode, emu_grammar_anode) in zip(self.emu_grammars, emu_grammar_anodes):
                emu_grammar_anode._hnode = emu_grammar_hnode

            assert rule_expr_anode.prod.lhs_s == '{EXPR}'

        self.anodes = [rule_expr_anode]

        alg_header.u_defns.append(self)

    def get_puk_set(self):
        result = set()
        for emu_grammar in self.emu_grammars:
            result |= emu_grammar.puk_set
        return result

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
        mo = re.fullmatch(
            r'The (\w+) concrete method of (an? (\w+ Environment Record)) is never used within this specification.',
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

        # Actually, if there's an attempt to invoke DeleteBinding on a module ER,
        # and the module ER schema doesn't have anything for that method,
        # the lookup *won't* fail, it will propagate up to the declarative ER schema,
        # which *does* have a definition for that method, which might succeed.
        # So we'd fail to detect that an unexpected thing had occurred.
        # So we do want *something* in the schema to 'trap' the invocation.
        (method_name, for_phrase, discriminator) = mo.groups()

        # This is a bit kludgey.
        # I could use _handle_header_with_std_preamble,
        # but I'd have to tweak it somewhat, and I don't feel like it.
        # Could maybe even leave these cases to _handle_other_op_section.
        params = {
            'CreateImmutableBinding': [
                AlgParam('_N_', '', 'a String'),
                AlgParam('_S_', '', 'a Boolean'),
            ],
            'DeleteBinding': [
                AlgParam('_N_', '', 'a String'),
            ],
        }[method_name]
        alg_header = AlgHeader_make(
            section = section,
            species = 'op: discriminated by type: env rec',
            name = method_name,
            params = params,
            node_at_end_of_header = p,
            for_phrase = for_phrase,
        )

        rs = spec.RecordSchema_for_name_[discriminator.title()]
        rs.add_method_defn(records.MethodDefn(alg_header, None))
        return True

    # ----

    if section.section_id == 'sec-weakref-execution':
        # 9.10.3
        op_name = 'WeakRef emptying thing'
        assert section.block_children[0].source_text().startswith(
            "<p>At any time, if a set of objects and/or symbols _S_ is not live,"
        )
        params = [ AlgParam('_S_', '', 'a List of Objects and/or Symbols') ]

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
            "<p>For an execution _execution_ and events _E_ and _D_ that are contained in SharedDataBlockEventSet(_execution_)"
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

    fpr.oh_warn()
    fpr.oh_warn(f"In {section.section_num} {section.section_title} ({section.section_id}),")
    fpr.oh_warn(f"there is a non-standard preamble")

    alg_header = AlgHeader_make(
        section = section,
        species = 'op: singular',
        name = op_name,
        params = params,
        node_at_end_of_header = section.heading_child,
    )

    emu_alg = section.block_children[1]
    assert emu_alg.element_name == 'emu-alg'
    SimpleAlgDefn(alg_header, emu_alg)

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
        if alg_header is None: return True

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
            pass
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
            SimpleAlgDefn(alg_header, emu_alg)

    elif emu_alg is None:
        assert 0, (section.section_num, section.section_title)

    else:
        # The emu-alg is the 'body' of
        # (this definition of) the operation named by the section_title.

        if alg_header.for_phrase is None:
            SimpleAlgDefn(alg_header, emu_alg)

        else:
            # type-discriminated operation
            mo = re.fullmatch(r'an? (.+?)( _\w+_)?', alg_header.for_phrase)
            type_str = mo.group(1)
            TypeDirectedAlgDefn(alg_header, type_str, emu_alg)

            if section.section_kind.endswith('_rec_method'):
                assert len(alg_header.u_defns) == 1
                [alg_defn] = alg_header.u_defns
                rs = spec.RecordSchema_for_name_[type_str.title()]
                rs.add_method_defn(records.MethodDefn(alg_header, alg_defn))

    # -----------------------------------------

    if section.section_id == 'sec-maybesimplecasefolding':
        ensure_alg('op: singular', 'scf')

    return True

class SimpleAlgDefn(AlgDefn):
    def __init__(self, alg_header, emu_alg):
        assert isinstance(alg_header, AlgHeader)
        assert isinstance(emu_alg, HNode) and emu_alg.element_name == 'emu-alg'

        self.parent_header = alg_header
        self.emu_alg = emu_alg

        anode = Pseudocode.parse(emu_alg, None)
        assert anode is None or anode.prod.lhs_s == '{EMU_ALG_BODY}'
        self.anodes = [anode]

        alg_header.u_defns.append(self)

class TypeDirectedAlgDefn(AlgDefn):
    def __init__(self, alg_header, type_str, emu_alg):
        assert isinstance(alg_header, AlgHeader)
        assert isinstance(type_str, str)
        assert isinstance(emu_alg, HNode) and emu_alg.element_name == 'emu-alg'

        self.parent_header = alg_header
        self.type_str = type_str
        self.emu_alg = emu_alg

        anode = Pseudocode.parse(emu_alg)
        assert anode is None or anode.prod.lhs_s == '{EMU_ALG_BODY}'
        self.anodes = [anode]

        alg_header.u_defns.append(self)

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
    for tr in table.each_child_named('tr'):
        (_, a, _, b, _) = tr.children 

        if a.element_name == 'th' and b.element_name == 'th':
            assert a.inner_source_text().strip() == 'Argument Type'
            assert b.inner_source_text().strip() == 'Result'
            continue

        TabularAlgDefn(alg_header, tr)

class TabularAlgDefn(AlgDefn):
    def __init__(self, alg_header, tr):
        assert isinstance(alg_header, AlgHeader)
        assert isinstance(tr, HNode) and tr.element_name == 'tr'

        self.parent_header = alg_header
        self.tr = tr

        (_, type_td, _, result_td, _) = tr.children 

        assert type_td.element_name == 'td'
        assert result_td.element_name == 'td'

        self.type_str = type_td.inner_source_text().strip()

        x = ' '.join(c.element_name for c in result_td.children)

        if x == '#LITERAL p #LITERAL emu-alg #LITERAL':
            (_, p, _, emu_alg, _) = result_td.children
            assert p.source_text() == '<p>Apply the following steps:</p>'
            anode = Pseudocode.parse(emu_alg)
            assert anode is None or anode.prod.lhs_s == '{EMU_ALG_BODY}'

        elif x in [
            '#LITERAL',
            '#LITERAL emu-xref #LITERAL',
            '#LITERAL sub #LITERAL',
            '#LITERAL sub #LITERAL sub #LITERAL',

            '#LITERAL emu-note #LITERAL',
            # ToBoolean: row for 'Object' has a NOTE re [[IsHTMLDDA]]

            '#LITERAL p #LITERAL p #LITERAL',
        ]:
            anode = Pseudocode.parse(result_td, 'one_line_alg')
            assert anode is None or anode.prod.lhs_s == '{ONE_LINE_ALG}'

        else:
            assert 0, x

        self.anodes = [anode]

        alg_header.u_defns.append(self)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

other_op_species_for_section_kind_ = {
    'syntax_directed_operation'                : 'op: discriminated by syntax: steps',
    'env_rec_method'                           : 'op: discriminated by type: env rec',
    'module_rec_method'                        : 'op: discriminated by type: module rec',
    'internal_method'                          : 'op: discriminated by type: object',
    'abstract_operation'                       : 'op: singular',
    'numeric_method'                           : 'op: singular: numeric method',
    'host-defined_abstract_operation'          : 'op: singular: host-defined',
    'implementation-defined_abstract_operation': 'op: singular: implementation-defined',
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
        elif section.parent.parent.parent.section_id == 'sec-module-semantics':
            section.section_kind = 'module_rec_method'
        else:
            assert 0, section.section_id
            
    else:
        section.section_kind = {
            'abstract operation': 'abstract_operation',
            'numeric method'    : 'numeric_method',
            'internal method'   : 'internal_method',
            'sdo'               : 'syntax_directed_operation',
            'host-defined abstract operation'          : 'host-defined_abstract_operation',
            'implementation-defined abstract operation': 'implementation-defined_abstract_operation',
        }[section_type]

    # --------------------------------------------

    h1 = section.heading_child
    h1_body = Pseudocode.parse(h1)
    if h1_body is None: return None

    L = len(h1_body.children)
    if L == 3:
        (which_semantics, op_name, return_nature) = h1_body.children
        params = []
    elif L == 4:
        (which_semantics, op_name, parameter_lines, return_nature) = h1_body.children
        params = []
        assert parameter_lines.prod.lhs_s == '{PARAMETER_DECLS}'
        for parameter_decl in each_item_in_left_recursive_list(parameter_lines):
            assert parameter_decl.prod.lhs_s == '{PARAMETER_DECL}'
            [optionality, param_name, param_nature] = parameter_decl.children
            optionality = optionality.source_text()
            param_name = param_name.source_text()
            param_nature = param_nature.source_text()
            param_punct = '[]' if (optionality == 'optional ') else ''
            params.append( AlgParam(param_name, param_punct, param_nature, parameter_decl) )
    else:
        assert 0, L
    which_semantics = which_semantics.source_text()
    op_name = op_name.source_text()

    if section.section_kind == 'numeric_method':
        op_name_pattern = r'[A-Z][a-zA-Z]+::[a-z][a-zA-Z]+'
    elif section.section_kind == 'internal_method':
        op_name_pattern = r'\[\[[A-Z][a-zA-Z]+\]\]'
    else:
        op_name_pattern = r'[a-zA-Z][a-zA-Z0-9/]+'
    assert re.fullmatch(op_name_pattern, op_name)

    # overwrite section.section_title
    if section_type == 'sdo':
        parameter_part = ''
    else:
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
        parameter_part = f" ({brief_params(0)} )"
    section.section_title = f"{which_semantics}{op_name}{parameter_part}"

    param_names = set(
        param.name
        for param in params
    )

    # -----

    for_phrase = None
    for_phrase_node = None

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
        dt = dl_nw_children[i+0]
        dd = dl_nw_children[i+1]
        dt_s = dt.inner_source_text()
        assert dt_s in ['for', 'effects', 'description', 'skip global checks', 'skip return checks'], dt_s
        assert dt_s not in dl_dict
        dl_dict[dt_s] = dd

    # ----------------------------------

    if 'for' in dl_dict:
        for_dd = dl_dict['for']
        assert for_phrase is None, for_phrase
        for_phrase = for_dd.inner_source_text()
        for_phrase_node = Pseudocode.parse(for_dd)

        if mo := re.search(r'\b_\w+_\b', for_phrase):
            param_names.add(mo.group(0))

    if 'effects' in dl_dict:
        effect_dd = dl_dict['effects']
        assert effect_dd.inner_source_text() == 'user-code'
        pass

    if 'description' in dl_dict:
        description_dd = dl_dict['description']

        def is_a_sub_of(subnature, vd):

            p = str(vd.prod)
            if p in [
                '{VALUE_DESCRIPTION} : either {VAL_DESC_DISJUNCTION}',
                '{VALUE_DESCRIPTION} : {VAL_DESC_DISJUNCTION}',
            ]:
                [vd_disjunction] = vd.children
                return any(
                    is_a_sub_of(subnature, vd_child)
                    for vd_child in vd_disjunction.children
                )

            elif p in [
                '{VALUE_DESCRIPTION} : {VAL_DESC}',
                '{VAL_DESC} : a normal completion containing {VALUE_DESCRIPTION}',
            ]:
                [vd_child] = vd.children
                return is_a_sub_of(subnature, vd_child)

            elif vd.children == [] or p in [
                '{VAL_DESC} : {LITERAL}',
                '{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION}',
            ]:
                vds = vd.source_text()
                return (
                    subnature == vds
                )

            elif p == '{VAL_DESC} : an integral Number in {INTERVAL}':
                return (subnature == 'an integral Number')

            elif p == '{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}) and {dsb_word} ({VALUE_DESCRIPTION})':
                return (subnature == vd.source_text())

            else:
                assert 0, p

        sentences = re.split(r'(?<=\.) +', description_dd.inner_source_text())
        for sentence in sentences:
            mo = re.fullmatch(r'(.+) (returns|returning) (.+)', sentence)
            if mo:
                (pre, verb, post) = mo.groups()
                if (
                    pre.endswith('whose [[NextMethod]]')
                    # CreateListIteratorRecord
                    or
                    pre == 'It does not enforce that the constructor function'
                    or
                    pre.endswith('that when executed')
                    or
                    pre.endswith('where _predicate_')
                    or
                    pre == '_op_ takes two List of byte values arguments and'

                ):
                    continue

                patterns = [
                    # ----------------
                    # language values:

                    (r'either ~done~ indicating .+ or the value from the IteratorResult object .+',  ['~done~', 'an ECMAScript language value']),
                    (r'the value of its associated binding object\'s property .+',  'an ECMAScript language value'),
                    (r'the value of its bound identifier .+',                       'an ECMAScript language value'),

                    # Undefined
                    (r'\*undefined\*.', '*undefined*'),

                    # Boolean
                    (r'\*true\* if and only if .+',               'a Boolean'),
                    (r'\*true\*, \*false\*, or \*undefined\* .+', ['a Boolean', '*undefined*']),

                    # Number/BigInt
                    (r'\*1\*<sub>\U0001d53d</sub> if .+ and \*\+0\*<sub>\U0001d53d</sub> otherwise.', ['*1*<sub>𝔽</sub>', '*+0*<sub>𝔽</sub>']),
                    (r'_value_ converted to a Number or a BigInt.',  ['a Number', 'a BigInt']),
                    (r'a Number identifying the day of the week .+', 'an integral Number'),
                    (r'a Number identifying the month .+',           'an integral Number'),
                    (r'an implementation-approximated value representing the result of raising _base_ to the _exponent_ power.', 'a Number'),
                    (r'the day number of .+',                        'an integral Number'),
                    (r'the day of the month .+',                     'an integral Number'),
                    (r'the full year associated .+',                 'an integral Number'),
                    (r'the hour of the day .+',                      'an integral Number'),
                    (r'the loaded value.',                           ['a Number', 'a BigInt']), #?
                    (r'the millisecond of the second .+',            'an integral Number'),
                    (r'the minute of the hour .+',                   'an integral Number'),
                    (r'the number of days in year _y_.',             ['*365*<sub>𝔽</sub>', '*366*<sub>𝔽</sub>']),
                    (r'the number of milliseconds since .+',         'an integral Number'),
                    (r'the one\'s complement of _x_.',               'a BigInt'),
                    (r'the respective Number value.',                'a Number'),
                    (r'the second of the minute .+',                 'an integral Number'),
                    (r'the time value of the start of year _y_.',    'a time value'),
                    (r'the value of the \*"length"\* property of an array-like object.', 'an integral Number'),
                    (r'the year in which .+',                        'an integral Number'),

                    # String
                    (r'a String representing .+', 'a String'),

                    # Object
                    (r'a Promise which .+',     'a Promise'),
                    (r'a new promise .+',       'a Promise'),
                    (r'either ~done~ indicating .+ or the IteratorResult object .+', ['~done~', 'an Object']),
                    (r'the global object .+',   'an Object'),
                    (r'the object that is .+',  'an Object'),

                    # --------------------
                    # specification values:

                    # List
                    (r'a List of byte values.',                                   'a List of byte values'),
                    (r'the sequence of Unicode code points that results from .+', 'a List of code points'),

                    # Record
                    (r'a Record that gives the index and value of the element found.', 'a Record with fields [[Index]] (an integral Number) and [[Value]] (an ECMAScript language value)'),

                    # mathematical
                    (r'that integer if it is non-negative and corresponds with an integer index.', 'a non-negative integer'),
                    (r'the code unit index corresponding to .+',     'a non-negative integer'),
                    (r'the length of _S_.',                          'a non-negative integer'),
                    (r'the number of left-capturing parentheses .+', 'a non-negative integer'),

                    # CharSet
                    (r'_A_.',                   'a CharSet'),
                    (r'the resulting CharSet.', 'a CharSet'),

                    # Closure
                    (r'a new Job Abstract Closure that .+', 'a Job Abstract Closure'),

                ]
                for (pattern, subnatures) in patterns:
                    if re.fullmatch(pattern, post):
                        if isinstance(subnatures, str):
                            subnatures = [subnatures]
                        for subnature in subnatures:
                            if not is_a_sub_of(subnature, return_nature):
                                msg_at_node(
                                    description_dd,
                                    f"This description implies that {subnature!r} should be (part of) the declared return type, but it isn't."
                                )
                            
                
                        break
                else:
                    # no break, i.e., no matching pattern
                    msg_at_node(
                        description_dd,
                        "This description talks about a return value, but we don't have a pattern that matches the wording"
                    )

            for varname in re.findall(r'\b_\w+_\b', sentence):
                if varname in param_names:
                    # The usual case
                    pass
                elif (op_name, varname) in [
                    ("Number::toString", "_r_"),
                    ("BigInt::toString", "_r_"),
                    # "The digits used in the representation of a number using radix _r_ are ..."

                    ("CanonicalNumericIndexString", "_n_"),
                    # "... matches ToString(_n_) for some Number value _n_, ..."

                    ("MaybeSimpleCaseFolding", "_cp_"),
                    # The description is referring to an external function,
                    # and including a parameter list.

                    ("AllocateTypedArray", "_TypedArray_"),
                    # It's referring to the family of TypedArray constructors
                    # as if it's a singular thing.
                ]:
                    pass
                else:
                    msg_at_node(
                        description_dd,
                        f"This description mentions `{varname}`, which is not a parameter."
                    )

    # --------------------------------------------------------------------------

    op_species = other_op_species_for_section_kind_[section.section_kind]

    alg_header = AlgHeader_make(
        section = section,
        species = op_species,
        name = op_name,
        for_phrase = for_phrase,
        for_phrase_node = for_phrase_node,
        params = params,
        return_nature_node = return_nature,
        node_at_end_of_header = section.dl_child,
    )

    return alg_header

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
        node_at_end_of_header = section.heading_child
    )

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

        msg_at_node(section, f"Should use a structured header? e.g.:\n{suggestion}")

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
            .replace('<PROP_PATH>',      r'(\w+|%\w+%)(\.\w+| \[ %Symbol\.\w+% \])+')
        )
        mo = re.fullmatch(pattern, section.section_title)
        if mo:
            break
    else:
        return False

    p_dict = mo.groupdict()
    section.section_kind = result

    # -----------

    check_section_title(section)

    if section.section_kind == 'function_property_xref':
        assert section.bcen_str == 'p'
        assert re.fullmatch(
            r'<p>See <emu-xref href="#[^"]+"></emu-xref>.</p>',
            section.block_children[0].source_text()
        )
        return True

    prop_path = p_dict['prop_path']

    if 'params_str' in p_dict:
        params = convert_parameter_listing_to_params(p_dict['params_str'])
    elif section.section_title.startswith('get '):
        assert section.section_kind == 'accessor_property'
        # The spec leaves off the empty parameter list
        params = []
    else:
        assert section.section_kind == 'anonymous_built_in_function' or section.section_title.startswith('set ')
        params = None # AlgHeader_make will deduce parameter list from the preamble

    n_emu_algs = section.bcen_list.count('emu-alg')
    assert n_emu_algs in [0, 1]

    # ======================================================

    # Handle the function that's declared by the section-heading.

    bif_species = {
        'CallConstruct'               : 'bif: intrinsic',
        'accessor_property'           : 'bif: intrinsic: accessor function',
        'anonymous_built_in_function' : 'bif: * per realm',
        'function_property'           : 'bif: intrinsic',
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
        SimpleAlgDefn(alg_header, emu_alg_a)

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_other_section(section):

    check_section_title(section)

    # We infer a section's kind almost entirely based on its title.
    pattern_results = [
            (r'Implicit Normal Completion',                        'shorthand'),
            (r'Implicit Completion Values',                        'shorthand'),
            (r'Throw an Exception',                                'shorthand'),
            (r'ReturnIfAbrupt',                                    'shorthand'),
            (r'ReturnIfAbrupt Shorthands',                         'shorthand'),
            (r'IfAbruptRejectPromise \( _value_, _capability_ \)', 'shorthand'),
            (r'IfAbruptCloseIterator \( _value_, _iteratorRecord_ \)', 'shorthand'),

            (r'.+ Instances',             'instances: info // properties'),
            (r'Module Namespace Objects', 'instances: info // properties'),

            (r'Properties of Valid Executions', 'catchall'),
            (r'Properties of .+',               'intrinsic: info // properties'),
            (r'The [\w%.]+ Object',             'intrinsic: info // properties'),
            (r'Additional Properties of .+',    'intrinsic: - // properties'),

            (r'The \w+ Constructor',               'intrinsic: info // CallConstruct'),
            (r'The _NativeError_ Constructors',    'intrinsic: info // CallConstruct'),
            (r'The _TypedArray_ Constructors',     'intrinsic: info // CallConstruct'),
            (r'The %TypedArray% Intrinsic Object', 'intrinsic: info // CallConstruct'),

            (r'_NativeError_ Object Structure', 'loop'),

            (r'Non-ECMAScript Functions',                          'catchall'),
            (r'URI Handling Functions',                            '- // properties'),
            (r'(Value|Function|Constructor|Other) Properties of .+', '- // properties'),
            (r'Legacy Object.prototype Accessor Methods'           , '- // properties'),

            (r'<PROP_PATH>',                                 'other_property'),
            (r'[a-z]\w+|Infinity|NaN',                       'other_property'),
            (r'%Symbol\.\w+%',                               'other_property'),

            (r'.*',                                'catchall'),
        ]
    # Look for the first pattern in `pattern_results`
    # that matches (via re.fullmatch) `section.section_title`.
    for (pattern, result) in pattern_results:
        pattern = (
            pattern
            .replace('<PROP_PATH>',      r'(\w+|%\w+%)(\.\w+| \[ %Symbol\.\w+% \])+')
        )
        mo = re.fullmatch(pattern, section.section_title)
        if mo:
            break
    else:
        assert 0, section.section_title

    # -----------

    if section.parent.section_title == 'Terms and Definitions' and result == 'other_property':
        section.section_kind = 'catchall'

    elif section.parent.section_title == 'Other Properties of the Global Object':
        assert result == 'catchall'
        section.section_kind = 'other_property_xref'

    else:
        section.section_kind = result

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
            ensure_alg('op: singular', 'abs')
            ensure_alg('op: singular', 'min')
            ensure_alg('op: singular', 'max')
            ensure_alg('op: singular', 'floor')
            ensure_alg('op: singular', 'truncate')
            ensure_alg('op: singular', '\U0001d53d')
            ensure_alg('op: singular', '\u211d')
            ensure_alg('op: singular', '\u2124')

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]

        if section.section_title == 'Algorithm Conventions':
            # It's just the example of algorithm layout.
            # Skip it.
            pass

        elif section.section_title == 'The Abstract Closure Specification Type':
            # The emu-alg is an example showing the definition and use
            # of an abstract closure.
            # Skip it.
            pass

        elif section.section_title == 'Array.prototype [ %Symbol.unscopables% ]':
            # The section_title identifies a data property,
            # and the algorithm results in its initial value.
            # So CreateIntrinsics invokes this alg, implicitly and indirectly.

            alg_header = AlgHeader_make(
                section = section,
                species = 'op: singular',
                name = 'initializer for %Symbol.unscopables%',
                params = [],
                node_at_end_of_header = section.block_children[emu_alg_posn-1],
            )

            SimpleAlgDefn(alg_header, emu_alg)

        else:
            assert 0, (section.section_num, section.section_title)

    else:

        if section.section_kind == 'shorthand':
            if section.section_title == 'Implicit Completion Values':
                ensure_alg('shorthand', 'Completion')
            elif section.section_title in [
                'ReturnIfAbrupt',
                'Await',
            ]:
                ensure_alg('shorthand', section.section_title)
            elif section.section_title == 'IfAbruptRejectPromise ( _value_, _capability_ )':
                ensure_alg('shorthand', 'IfAbruptRejectPromise')
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
    assert emu_eqn.attrs['id'] == 'eqn-' + aoid

    tree = Pseudocode.parse(emu_eqn)
    if tree is None: return

    assert tree.prod.lhs_s == '{EMU_EQN_DEF}'
    [child] = tree.children

    if child.prod.lhs_s == '{CONSTANT_DEF}':
        [constant_name, dec_int_lit] = child.children[0:2]
        assert constant_name.source_text() == aoid
        # TODO: Define a constant named {aoid} defined by {dec_int_lit}

    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def convert_parameter_listing_to_params(parameter_listing):
    params = []
    parameter_listing = parameter_listing.strip()
    if parameter_listing != '':
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

    def blah_early_error_block(emu_grammar, ul):
        EarlyErrorAlgDefn(None, emu_grammar, ul, None)

    # For calls to scan_section, we're going to assume this holds,
    # but be sure to undo it if we ultimately return False.
    section.section_kind = 'changes'

    # --------------------------------------------------------------------------
    if section.section_num.startswith('B.') and section.section_title == 'Runtime Semantics: CompileSubpattern':
        # B.1.2.5
        patterns = [
            (
                [
                    ('p', r"The semantics of \w+ is extended as follows:"),
                ],
                None
            ),
            (
                [
                    ('p', r"The rule for EMU-GRAMMAR is the same as for EMU-GRAMMAR but with NONTERMINAL substituted for NONTERMINAL\."),
                ],
                lambda p: None
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_num.startswith('B.') and section.section_title == 'Runtime Semantics: CompileAssertion':
        # B.1.2.6
        patterns = [
            (
                [
                    ('p', r"\w+ rules for the EMU-GRAMMAR and EMU-GRAMMAR productions are also used for the NONTERMINAL productions, but with NONTERMINAL substituted for NONTERMINAL."),
                ],
                lambda p: None
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_num.startswith('B.') and section.section_title == 'Runtime Semantics: CompileAtom':
        # B.1.2.7
        patterns = [
            (
                [
                    ('p', r"\w+ rules for the NONTERMINAL productions except for EMU-GRAMMAR are also used for the NONTERMINAL productions, but with NONTERMINAL substituted for NONTERMINAL. The following rules, with parameter _direction_, are also added:"),
                ],
                lambda p: None
            ),
            (
                [
                    'emu-grammar',
                    'emu-alg'
                ],
                lambda emu_grammar, emu_alg: blah_composite_sdo('CompileAtom', emu_grammar, emu_alg)
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_num.startswith('B.') and section.section_title == 'Runtime Semantics: CompileToCharSet':
        # B.1.2.8
        patterns = [
            (
                [
                    ('p', "The semantics of EMU-XREF is extended as follows:"),
                ],
                None
            ),
            (
                [
                    ('p', "The following two rules replace the corresponding rules of CompileToCharSet."),
                ],
                None
            ),
            (
                [
                    ('p', "In addition, the following rules are added to CompileToCharSet."),
                ],
                None
            ),
            (
                [
                    'emu-grammar',
                    'emu-alg',
                ],
                lambda emu_grammar, emu_alg: blah_composite_sdo('CompileToCharSet', emu_grammar, emu_alg)
            ),
            (
                ['emu-note'],
                None
            ),

        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_num.startswith('B.') and section.section_title == 'Static Semantics: ParsePattern ( _patternText_, _u_, _v_ )':
        # B.1.2.9
        # This defines an extended version of an abstract operation.
        # It seems like it should be converted to have a structured header,
        # but note that Annex B sections that give
        # an extended version of an *SDO* don't have a structured header
        # (even though the main-body defn of the SDO does).
        #
        # If we changed it to have a structured header,
        # then "The semantics of X is extended as follows" would fall in an odd place?
        patterns = [
            (
                [
                    ('p', "The semantics of EMU-XREF is extended as follows:"),
                    ('p', "The abstract operation ParsePattern .+"),
                    'emu-alg',
                ],
                lambda p1, p2, emu_alg: blah_solo_op('ParsePattern', emu_alg)
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif (mo := re.fullmatch(r'Changes to ([A-Z]\w+)', section.section_title)):
        op_name = mo.group(1)
        patterns = [
            (
                # B.3.2.{1,2,3,6}:
                [
                    ('p', f'During {op_name} the following steps are performed in place of step EMU-XREF:'),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_solo_op(op_name, emu_alg)
            ),
            (
                # B.3.6.1:
                [
                    ('p', f'The following step replaces step EMU-XREF of {op_name}:'),
                    'emu-alg'
                ],
                lambda p, emu_alg: blah_solo_op(op_name, emu_alg)
            ),
            (
                # B.3.6.2:
                [
                    ('p', f'The following steps replace step EMU-XREF of {op_name}:'),
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
                    ('p', 'The rules for the following production in EMU-XREF are modified with the addition of the <ins>highlighted</ins> text:'),
                    'emu-grammar',
                    'ul',
                ],
                lambda p, emu_grammar, ul: blah_early_error_block(emu_grammar, ul)
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    elif section.section_title == 'VariableStatements in Catch Blocks':
        # B.3.4
        patterns = [
            (
                [
                    ('p', 'The content of subclause EMU-XREF is replaced with the following:'),
                    'emu-grammar',
                    'ul'
                ],
                lambda p, emu_grammar, ul: blah_early_error_block(emu_grammar, ul)
            ),
            (
                ['emu-note'],
                None
            ),
            (
                [
                    ('p', '.+ This change is accomplished by modifying the algorithm of EMU-XREF as follows:'),
                ],
                None
            ),
            (
                [
                    ('p', 'Step EMU-XREF is replaced by:'),
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
                    ('p', 'The following augments the NONTERMINAL production in EMU-XREF:'),
                    'emu-grammar',
                    ('p', 'This production only applies when parsing non-strict code.'),
                ],
                lambda p, emu_grammar, _: None
            ),
            (
                [
                    ('p', r'The (?:static|runtime) semantics of (\w+) in EMU-XREF are augmented with the following:'),
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
        assert section.bcen_str == 'p emu-alg'
        patterns = [
            (
                [
                    ('p', 'The following step replaces step EMU-XREF of EMU-XREF:'),
                    'emu-alg'
                ],
                lambda p, emu_alg: None
            ),
        ]
        scan_section(section, patterns)

    # --------------------------------------------------------------------------
    else:
        del section.section_kind
        return False

    # ==========================================================================

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def scan_section(section, patterns):
    def e(s):
        return (s
            .replace('EMU-XREF',    r'<emu-xref [^<>]+>[^<>]*</emu-xref>')
            .replace('EMU-GRAMMAR', r'<emu-grammar>[^<>]+</emu-grammar>')
            .replace('NONTERMINAL', r'\|\w+\|')
        )
    return NodeGrammar(patterns, e).scan_section(section)

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
    mo1 = re.search(r'\[ *@', title)
    if mo1:
        mo2 = re.search(r'( |^)\[ %Symbol\.\w+% \]( |$)', title)
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

def check_id(section):
    remove_param_list = lambda s: re.sub(r' \(.+', '', s)
    remove_initial_The = lambda s: re.sub(r'^The ', '', s)
    trim_underscores_from_aliases = lambda s: re.sub(r'\b_([A-Za-z]+)_\b', r'\1', s)
    prepend_parent_section_title = lambda s: section.parent.section_title + ' ' + s
    remove_backticks = lambda s: s.replace('`', '')
    convert_to_lowercase = lambda s: s.lower()
    change_space_to_hyphen = lambda s: s.replace(' ', '-')
    prepend_sec = lambda s: 'sec-' + s

    # ----------------------------------------------------------------
    if (
        '_property' in section.section_kind
        or
        section.section_kind in ['CallConstruct']
    ):
        pipeline = [
            undo_3238,

            # If the title is a single word (possibly followed by a parameter list),
            # then maybe prepend the parent section's title (47 cases).
            [
                None,
                lambda s: (
                    (section.parent.section_title + ' ' + s)
                    if
                    re.fullmatch(r'\w+( \(.*\))?', s)
                    else
                    s
                )
            ],
            # but remove initial 'The' (3 cases):
            lambda s: re.sub('The ', '', s),
            # and maybe change "Instances" to "Instance" for some reason (3 cases).
            [ None, lambda s: s.replace(' Instances ', ' Instance ') ],

            # If there's a parameter list,
            # either remove it, or extract its parameter names.
            [ remove_param_list, extract_param_names ],
            # but drop a final '_options_' parameter (because it's optional?) (3 cases)
            lambda s: re.sub(r' _options_$', '', s),

            # Remove the underscores from any alias names.
            # (This handles the parameter names extracted above,
            # but also things like _NativeError_ and _TypedArray_.)
            trim_underscores_from_aliases,

            # If a property key is a symbol, drop the square brackets:
            lambda s: re.sub(r' \[ (%Symbol\.\w+%) \]', r' \1', s),

            # If it's an accessor property, maybe drop the initial 'get' (2 cases)
            [ None, lambda s: re.sub(r'^get ', '', s) ],

            # Maybe split certain compound words (19 cases).
            [ None, split_certain_words ],

            # Lower-case everything, except maybe the last property-name (8 cases)
            [ convert_to_lowercase, lower_except_last_propname ],

            # Change spaces to hyphens
            change_space_to_hyphen,
            # and maybe change dots to hyphens too, but never after "%symbol" (11 cases)
            [ None, lambda s: re.sub(r'(?<!%symbol)\.', '-', s) ],

            # And prepend 'sec-'
            prepend_sec,
        ]
        failures = [
            'sec-constructor-properties-of-the-global-object-finnalization-registry', # 'finnal'
            'sec-function-p1-p2-pn-body',                           # parameter-list changed
            'sec-bigint-constructor-number-value',                  # 'number'
            'sec-finalization-registry-cleanup-callback',           # split param name
            'sec-async-function-constructor-arguments',             # 'constructor' + 'arguments'
            'sec-async-function-constructor-prototype',             # 'constructor'
            'sec-async-function-prototype-properties-constructor',  # 'properties'
            'sec-async-function-prototype-properties-toStringTag',  # 'properties'
            'String.prototype.trimleft',                            # missing 'sec-'
            'String.prototype.trimright',                           # missing 'sec-'
        ]

    # ----------------------------------------------------------------
    elif section.section_kind in [
        'intrinsic: info // CallConstruct',
        'intrinsic: info // properties',
        'intrinsic: - // properties',
    ]:
        pipeline = [
            undo_3238,
            remove_initial_The,
            [ None, lambda s: re.sub(r' the (.+) Object$', r' \1', s) ], # 3 cases
            trim_underscores_from_aliases, # 6 cases
            split_certain_words, # 12 cases
            convert_to_lowercase,
            change_space_to_hyphen,
            prepend_sec,
        ]
        failures = [
            'sec-properties-of-the-aggregate-error-constructors',      # plural
            'sec-properties-of-the-aggregate-error-prototype-objects', # plural
            'sec-properties-of-the-%typedarrayprototype%-object',      # misplaced %
            'sec-properties-of-typedarray-prototype-objects',          # dropped 'the'
            'sec-asynciteratorprototype',                              # dropped 'object'
            'sec-properties-of-asyncgeneratorfunction',                # dropped 'the constructor'
            'sec-async-function-constructor-properties',               # "Properties of ..."
            'sec-async-function-prototype-properties',                 # "Properties of ...
        ]

    # ----------------------------------------------------------------
    elif section.section_kind in [
        'shorthand',
        '- // properties',
        'instances: info // properties',
        'anonymous_built_in_function',
        'loop',
    ]:
        pipeline = [
            remove_param_list,
            trim_underscores_from_aliases, # 2 cases
            split_certain_words, # 4 cases
            remove_backticks,
            convert_to_lowercase,
            change_space_to_hyphen,
            prepend_sec,
        ]
        failures = [
            'sec-properties-of-the-arraybuffer-instances',       # inserted 'the'
            'sec-properties-of-the-sharedarraybuffer-instances', # inserted 'the'
            'sec-properties-of-asyncgenerator-intances',         # 'intances'
            'sec-object.prototype-legacy-accessor-methods',      # word order
        ]

    # ----------------------------------------------------------------
    elif section.section_kind == 'abstract_operation':
        pipeline = [
            lambda s: re.sub(r'^(Static|Runtime) Semantics: ', '', s),

            # but some sections that *don't* have "Runtime Semantics" in the title
            # *do* have "runtime-semantics" in the id, go figure.
            (
                (lambda s: 'Runtime Semantics ' + s)
                if
                section.section_title.startswith((
                    'ForIn/OfHeadEvaluation',
                    'ForIn/OfBodyEvaluation',
                    'CaseClauseIsSelected',
                    'ScriptEvaluation',
                    'RepeatMatcher',
                    'IsWordChar',
                    'CharacterSetMatcher',
                    'Canonicalize',
                    'CharacterRange',
                    'HasEitherUnicodeFlag',
                    'UnicodeMatchProperty',
                    'UnicodeMatchPropertyValue',
                    'CharacterRangeOrUnion',
                ))
                else
                None
            ),

            (
                extract_param_names
                if
                section.section_title.startswith((
                    'IsExtensible',
                    'Get ',
                    'Set ',
                    'UTC ',
                    'Canonicalize ',
                    'UnicodeMatchProperty ',
                    'UnicodeMatchPropertyValue '
                ))
                else
                remove_param_list
            ),
            # but drop _rer_ because that was added later
            lambda s: re.sub(r' _rer_\b', '', s),

            trim_underscores_from_aliases,

            # Maybe tack 'abstract-operation' on the end
            (
                (lambda s: s + ' Abstract Operation')
                if
                section.section_title.startswith((
                    'RepeatMatcher',
                    'IsWordChar',
                    'CharacterSetMatcher',
                    'CharacterRange',
                    'HasEitherUnicodeFlag',
                    'CharacterRangeOrUnion',
                ))
                else
                (lambda s: s + ' AO')
                if
                section.section_title.startswith('Completion ')
                else
                None
            ),

            # Maybe split words
            [ None, split_words ],
            # but rejoin 'Typed Array'
            lambda s: re.sub(r'\bTyped Array\b', 'TypedArray', s),

            lambda s: s.replace('/', ''),

            # Maybe convert to lower-case
            (
                None
                if 
                section.section_title.startswith((
                    'ContinueDynamicImport',
                    'InnerModuleLoading',
                    'ContinueModuleLoading',
                    'InnerModuleLinking',
                    'GetImportedModule',
                    'FinishLoadingImportedModule',
                    'SetterThatIgnoresPrototypeProperties',
                    'ModuleRequestsEqual',
                    'AllImportAttributesSupported',
                    'IncrementModuleAsyncEvaluationCount',
                    'EvaluateModuleSync',
                ))
                else
                convert_to_lowercase
            ),

            change_space_to_hyphen,

            (
                None
                if
                section.section_title.startswith((
                    'TypedArraySpeciesCreate',
                    'Await ',
                ))
                else
                prepend_sec
            ),
        ]
        failures = [
            'sec-createlistiteratorRecord',
            'sec-weakref-execution',
            'sec-utf16decodesurrogatepair',
            'sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset',
            'sec-timezoneestring',
            'sec-async-functions-abstract-operations-async-function-start',
            'sec-sharedatablockeventset',
            'sec-tear-free-aligned-reads',
            'sec-createiterresultobject', # PR #3335 changed the op name without changing the id
        ]

    # ----------------------------------------------------------------
    elif section.section_kind in [
        'host-defined_abstract_operation',
        'implementation-defined_abstract_operation',
    ]:
        pipeline = [
            remove_param_list,
            convert_to_lowercase,
            prepend_sec,
        ]
        failures = [
            'sec-host-cleanup-finalization-registry',
            'sec-HostLoadImportedModule',
            'sec-host-promise-rejection-tracker',
        ]

    # ----------------------------------------------------------------
    elif section.section_kind == 'syntax_directed_operation':
        pipeline = (
            [
                [
                    lambda s: s.replace(':', ''),
                    lambda s: re.sub(r'^(Static|Runtime) Semantics: ', '', s)
                ],
            ]
            +
            (
                [
                    prepend_parent_section_title,
                    remove_initial_The,
                    lambda s: s.replace('( `+` )', 'plus'),
                    lambda s: s.replace('( `-` )', 'minus'),
                    lambda s: re.sub(r' \( `[^`()]+` \) ', ' ', s),
                    remove_backticks,
                    lambda s: s.replace(',', ''),
                    lambda s: s.replace(' + ', ' plus ').replace(' - ', ' minus '),
                    lambda s: s.replace('Exponentiation', 'Exp'),
                ]
                if
                (
                    section.section_title == 'Runtime Semantics: Evaluation'
                    and
                    section.parent.section_title != 'Syntax-Directed Operations'
                )

                else
                [
                    prepend_parent_section_title,
                ]
                if
                re.match(r'Runtime Semantics: (Property|Rest)BindingInitialization', section.section_title)

                else
                [
                    lambda s: 'Patterns ' + s,
                    split_words,
                    (lambda s: s + ' AnnexB') if section.element_name == 'emu-annex' else None
                ]
                if
                section.section_title.endswith((
                    'CapturingGroupNumber',
                    'IsCharacterClass',
                    'CharacterValue'
                ))

                else
                [
                ]
            )
            +
            [
                convert_to_lowercase,
                change_space_to_hyphen,
                prepend_sec,
            ]
        )
        failures = [
            'sec-runtime-semantics-mv-for-stringintegerliteral',
            'sec-string-literals-static-semantics-mv',
            'sec-optional-chaining-evaluation',
            'sec-optional-chaining-chain-evaluation',
            'sec-import-call-runtime-semantics-evaluation',
            'sec-for-in-and-for-of-statements-runtime-semantics-evaluation',
            'sec-asyncgenerator-definitions-evaluation',
            'sec-static-semantics-classelementevaluation',
            'sec-script-semantics-runtime-semantics-evaluation',
        ]

    # ----------------------------------------------------------------
    elif section.section_kind == 'numeric_method':
        pipeline = [
            remove_param_list,
            lambda s: re.sub(r'^(\w+)::(\w+)$', lambda mo: (mo.group(1).lower() + '-' + mo.group(2)), s),
            lambda s: 'numeric-types-' + s,
            prepend_sec,
        ]
        failures = [
            'sec-numeric-types-number-tostring',
            'sec-numeric-types-bigint-tostring',
        ]

    # ----------------------------------------------------------------
    elif section.section_kind in [
        'env_rec_method',
        'env_rec_method_unused',
    ]:
        exceptional = section.section_title.startswith((
            'BindThisValue ',
            'GetSuperBase ',
            'HasVarDeclaration ',
            'HasLexicalDeclaration ',
            'HasRestrictedGlobalProperty ',
            'CanDeclareGlobalVar ',
            'CanDeclareGlobalFunction ',
            'CreateGlobalVarBinding ',
            'CreateGlobalFunctionBinding ',
            'CreateImportBinding ',
        ))

        pipeline = (
            (
                [
                    remove_param_list,
                ]
                if
                exceptional
                else
                [
                    prepend_parent_section_title,
                    extract_param_names,
                    trim_underscores_from_aliases,
                ]
            )
            +
            [
                convert_to_lowercase,
                change_space_to_hyphen,
                prepend_sec,
            ]
        )
        failures = [
        ]

    # ----------------------------------------------------------------
    elif section.section_kind == 'internal_method':
        pipeline = (
            [
                lambda s: re.sub(r'^\[\[(\w+)\]\]', r'\1', s),
            ]
            +
            (
                [
                    remove_param_list,
                    lambda s: 'TypedArray ' + s,
                ]
                if
                'TypedArray' in section.parent.section_title
                else
                [
                    extract_param_names,
                    trim_underscores_from_aliases,
                    prepend_parent_section_title,
                ]
            )
            +
            [
                convert_to_lowercase,
                change_space_to_hyphen,
                prepend_sec,
            ]
        )
        failures = [
        ]

    # ----------------------------------------------------------------
    elif section.section_kind == 'early_errors':
        pipeline = [
            [ lambda s: re.sub('^Static Semantics: ', '', s), lambda s: s.replace(':', '') ],
            prepend_parent_section_title,
            remove_initial_The,
            remove_backticks,
            convert_to_lowercase,
            change_space_to_hyphen,
            prepend_sec,
        ]
        failures = [
            'sec-primary-expression-regular-expression-literals-static-semantics-early-errors',
            'sec-static-semantics-template-early-errors',
            'sec-left-hand-side-expressions-static-semantics-early-errors',
            'sec-for-in-and-for-of-statements-static-semantics-early-errors',
            'sec-patterns-static-semantics-early-errors-annexb',
        ]

    # ----------------------------------------------------------------
    elif section.section_kind in ['catchall', 'changes', 'module_rec_method']:
        return
        # The pipeline below would be a start,
        # but it still leaves tons of false positives.

        pipeline = [
            remove_initial_The,
            lambda s: s.replace('( `+` )', 'plus'),
            lambda s: s.replace('( `-` )', 'minus'),
            lambda s: re.sub(r' \( `[^`()]+` \)', '', s),
            remove_backticks,
            (
                [ None, prepend_parent_section_title ]
                if
                section.parent.section_title in ['Terms and Definitions', 'Literals']

                else
                prepend_parent_section_title
                if
                section.parent.section_title in ['ECMAScript Language Types']

                else
                None
            ),
            convert_to_lowercase,
            change_space_to_hyphen,
            prepend_sec,
        ]

    # ----------------------------------------------------------------
    else:
        assert 0, section.section_kind

    # ----------------------------------------------------------------

    possibles = apply_pipeline(section.section_title, pipeline)
    if section.section_id not in possibles and section.section_id not in failures:
        # print()
        # print(section.section_kind)
        # print(section.section_title)
        # for poss in sorted(possibles): print(poss)
        # print('-' * len(section.section_id))
        # print(section.section_id)

        msg = f"Based on the section's kind ({section.section_kind}) and title, the value of its `id` attribute should be one of:"
        for poss in sorted(possibles):
            msg += '\n--    ' + poss

        msg_at_node(section, msg)

def extract_param_names(s):
    mo = re.fullmatch(r'(.+) \((.*)\)', s)
    if mo:
        (pre, param_list) = mo.groups()
        param_names = re.findall(r'\w+', param_list)
        if param_names:
            return pre + ' ' + ' '.join(param_names)
        else:
            return pre
    else:
        return s

def lower_except_last_propname(s):
    mo = re.fullmatch(r'(.*)(\.\w+)([^\.]*)', s)
    if mo:
        (a, b, c) = mo.groups()
        return a.lower() + b + c.lower()
    else:
        return s.lower()

def split_words(s):
    r = re.sub(r'([a-z])([A-Z])', r'\1 \2', s)
    r = re.sub(r'(JSON)(Module)', r'\1 \2', r)
    return r

def split_certain_words(s):
    return ( s
        .replace('AggregateError', 'Aggregate Error')
        .replace('AsyncFunction', 'Async Function')
        .replace('FinalizationRegistry', 'Finalization Registry')
        .replace('WeakRef', 'Weak Ref')
    )

def undo_3238(s):
    # PR #3238 changed how the spec refers to certain intrinsics,
    # which changed the titles of certain sections.
    # However, the PR didn't make collateral changes
    # to the `id` attribute of those sections.
    # So here, we locally undo those title-changes,
    # so that the generated ids match the actual ids.
    # (Alternatively, we could have just added those ids
    # to the appropriate `failures` lists.)
    s = re.sub(r'The %((Async)?Generator)Prototype% Object', r'Properties of the \1 Prototype Object', s)
    s = re.sub(r'%((Async)?Generator)Prototype%', r'\1.prototype', s)
    return s

def apply_pipeline(starter, pipeline):
    currents = {starter}
    for transformer in pipeline:
        if transformer is None:
            # leave currents unchanged
            pass
        elif callable(transformer):
            currents = {
                transformer(current)
                for current in currents
            }

        elif type(transformer) == type([]):
            nexts = set()
            for current in currents:
                for alt in transformer:
                    if alt is None:
                        nexts.add(current)
                    elif callable(alt):
                        nexts.add(alt(current))
                    else:
                        assert 0, alt
            currents = nexts

        else:
            assert 0, transformer

    return currents

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def extract_intrinsic_info(section):
    section.intrinsic_facts_raw = []
    section.intrinsic_facts_cooked = []

    if section.section_title in [
        'Well-Known Intrinsic Objects',
        'Additional Properties of the Global Object',
    ]:
        extract_intrinsic_info_from_WKI_section(section)
    elif section.section_kind.startswith('intrinsic: info'):
        extract_intrinsic_info_from_p_ul_section(section)
    elif section.section_kind == 'CallConstruct':
        extract_intrinsic_info_from_CallConstruct_section(section)
    elif '_property' in section.section_kind:
        extract_intrinsic_info_from_property_section(section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

non_global_wkis = []

def extract_intrinsic_info_from_WKI_section(section):
    [wki_table] = [
        child
        for child in section.block_children
        if child.element_name == 'emu-table'
    ]
    for (percent_name, global_name, phrase) in intrinsics.each_row_in_wki_table(wki_table):
        section.put_fact(percent_name, 'exists', '')

        if global_name:
            global_name = detick(global_name)
            section.put_fact(percent_name, 'is-aka', global_name)
            section.put_fact(
                'the global object',
                'has-prop',
                S_Property(
                    pystr_to_spec_String_literal(global_name),
                    {'[[Value]]': percent_name}
                )
            )
        else:
            non_global_wkis.append(percent_name)

        if phrase:
            section.put_fact(percent_name, 'is-aka', detick(phrase))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def extract_intrinsic_info_from_p_ul_section(section):

    assert section.bcen_str.startswith('p ul')
    (p, ul) = section.block_children[0:2]

    assert p.element_name == 'p'
    p_ist = p.inner_source_text()

    if '<dfn' in p_ist:
        mo = re.fullmatch(r'(.+)<dfn\b[^<>]*>(.+)</dfn>(.+)', p_ist)
        dfn_phrase = mo.group(2)
        p_ist = mo.expand(r'\1\2\3')
    else:
        dfn_phrase = None

    # ----------------------------------------------------------------
    # section_title + intro <p>

    if (mo := re.fullmatch(r'(Properties of the|The) (_\w+_) (Constructor|Prototype Object)s', section.section_title)):
        # _NativeError_ and _TypedArray_
        (_, var, what) = mo.groups()
        what = what.lower()
        subject = f"each {var} {what}"
        assert p_ist == f"Each {var} {what}:"

    elif (mo := re.fullmatch(r'(Properties of the|The) (%\w+(?:\.\w+)?%|[A-Z]\w+) (Constructor|Prototype Object|Intrinsic Object|Object)', section.section_title)):
        # the usual case
        (prefix, id, suffix) = mo.groups()
        if id == 'Global': id = 'global'
        assert p_ist == 'The ' + id + ' ' + suffix.lower() + ':'
        subject = 'the ' + id + ' ' + suffix.lower()

    else:
        assert 0, section.section_title

    if dfn_phrase:
        # Any mention of {dfn_phrase} in the spec will be autolinked to here,
        # so in effect, {dfn_phrase} is a synonym for whatever is being defined here.
        section.put_fact(subject, 'is-aka', dfn_phrase)

    # ----------------------------------------------------------------
    # <ul>

    assert ul.element_name == 'ul'
    for li in ul.children:
        if li.is_whitespace(): continue
        assert li.element_name == 'li'
        li_ist = li.inner_source_text().strip()

        # -------------------
        # is AKA

        if mo := re.fullmatch(r'is <dfn>(%\w+(\.\w+)*%)</dfn>( \(see <emu-xref [^<>]+></emu-xref>\))?\.', li_ist):
            section.put_fact(subject, 'is-aka', mo.group(1))

        # -------------------
        # ordinary vs exotic object (which subsumes internal methods + slots)

        # ordinary
        elif li_ist in [
            'is an ordinary object.',
            'is itself an ordinary object.',
        ]:
            section.put_fact(subject, 'is', 'an ordinary object')
        elif li_ist == 'is itself a Boolean object; it has a [[BooleanData]] internal slot with the value *false*.':
            section.put_fact(subject, 'is', 'an ordinary object')
            section.put_fact(subject, 'has-slot', S_InternalSlot('[[BooleanData]]', '*false*'))
        elif li_ist == 'is itself a Number object; it has a [[NumberData]] internal slot with the value *+0*<sub>\U0001d53d</sub>.':
            section.put_fact(subject, 'is', 'an ordinary object')
            section.put_fact(subject, 'has-slot', S_InternalSlot('[[NumberData]]', '*+0*<sub>\U0001d53d</sub>'))

        # exotic
        elif li_ist == 'is a String exotic object and has the internal methods specified for such objects.':
            section.put_fact(subject, 'is', 'a String exotic object')
        elif li_ist == 'is an Array exotic object and has the internal methods specified for such objects.':
            section.put_fact(subject, 'is', 'an Array exotic object')
        elif li_ist == 'has the internal methods defined for ordinary objects, except for the [[SetPrototypeOf]] method, which is as defined in <emu-xref href="#sec-immutable-prototype-exotic-objects-setprototypeof-v"></emu-xref>. (Thus, it is an immutable prototype exotic object.)':
            section.put_fact(subject, 'is', 'an immutable prototype exotic object whose other internal methods are ordinary')

        # function
        # (All intrinsics are built-in, so we don't have to say "built-in".)
        elif li_ist in [
            'is a function whose behaviour differs based upon the number and types of its arguments. The actual behaviour of a call of _TypedArray_ depends upon the number and kind of arguments that are passed to it.',
            'is a function whose behaviour differs based upon the number and types of its arguments.',
            'is a standard built-in function object that inherits from the Function constructor.',
            'is itself a built-in function object.',
            'returns a new Symbol value when called as a function.',
            'is not intended to be used with the `new` operator.',
        ]:
            section.put_fact(subject, 'is', 'a function object')

        elif li_ist == 'accepts any arguments and returns *undefined* when invoked.':
            section.put_fact(subject, 'has-slot', S_InternalSlot('[[ccb]]', f"prose in {section.section_id}"))

        # constructor
        elif li_ist in [
            'performs a type conversion when called as a function rather than as a constructor.',
            'returns a String representing the current time (UTC) when called as a function rather than as a constructor.',
            'is not intended to be called as a function and will throw an exception when called in that manner.',
            'creates a new ordinary object when called as a constructor.',
            'is a constructor function object that all of the _TypedArray_ constructor objects inherit from.',
            'will throw an error when invoked, because it is an abstract class constructor. The _TypedArray_ constructors do not perform a `super` call to it.',
            'when called as a function rather than as a constructor, returns either a new RegExp object, or the argument itself if the only argument is a RegExp object.',
        ]:
            section.put_fact(subject, 'is', 'a constructor')
        elif (
            re.fullmatch(r'(also )?creates and initializes a new \w+( object)? when called as a function rather than as a constructor.( A call of the object as a function is equivalent to calling it as a constructor with the same arguments.)? Thus the function call .+ is equivalent to the object creation expression .+ with the same arguments.', li_ist)
            or
            re.fullmatch(r'creates and initializes a new \w+( object)? when called as a constructor.', li_ist)
            or
            re.fullmatch(r'when called as a function, returns either a new RegExp object, or the argument itself if the only argument is a RegExp object.', li_ist)
        ):
            section.put_fact(subject, 'is', 'a constructor')

        # negative statements that don't tell us anything about what it *is*:
        elif li_ist in [
            'is not a function object.',
            'does not have a [[Call]] internal method; it cannot be invoked as a function.',
            'does not have a [[Construct]] internal method; it cannot be used as a constructor with the `new` operator.',
        ]:
            pass

        # ----------------------
        # internal slots

        # has
        elif mo := re.fullmatch(r'has an? (\[\[\w+\]\]) internal slot whose value is (%\w+(?:\.\w+)*%|\*null\*|\*true\*|the empty String|host-defined)\.', li_ist):
            section.put_fact(subject, 'has-slot', S_InternalSlot(mo.group(1), mo.group(2)))

        # does not have
        elif mo := re.fullmatch(r'does not have a \[\[\w+\]\] internal slot\.', li_ist):
            pass
        elif mo := re.fullmatch(r'does not have a \[\[\w+\]\] internal slot or any of the other internal slots of Promise instances\.', li_ist):
            pass
        elif mo := re.fullmatch(r'does not have a \[\[\w+\]\] or any other of the internal slots that are specific to _TypedArray_ instance objects\.', li_ist):
            pass
        elif mo := re.fullmatch(r'does not have \[\[\w+\]\] and \[\[\w+\]\] internal slots\.', li_ist):
            pass
        elif mo := re.fullmatch(r'does not have an \[\[\w+\]\] or \[\[\w+\]\] internal slot\.', li_ist):
            pass
        elif mo := re.fullmatch(r'does not have a \[\[\w+\]\], \[\[\w+\]\], \[\[\w+\]\], or \[\[\w+\]\] internal slot\.', li_ist):
            pass

        elif mo := re.fullmatch(r'''(?x)
                is\ not\ an?\ (\w+)\ (object|instance)
                (\ or\ an\ AggregateError\ instance)?
                (;\ it|\ and)\ does\ not\ have\ an?\ \[\[\w+\]\]\ internal\ slot
                (
                    \.
                |
                    \ or\ any\ of\ the\ other\ internal\ slots\ of\ RegExp\ instance\ objects\.
                |
                    \ or\ any\ other\ of\ the\ internal\ slots\ listed\ in\ <emu-xref\ [^<>]+></emu-xref>\.
                |
                    \ or\ any\ other\ of\ the\ internal\ slots\ listed\ in\ <emu-xref\ [^<>]+></emu-xref>\ or\ <emu-xref\ [^<>]+></emu-xref>\.
                )
            ''', li_ist):
            assert mo.group(1) != 'ordinary'

        # ----------------------
        # subclassing it

        elif (
            re.fullmatch(r'''(?x)
                may\ be\ used\ as\ the\ value\ 
                    ( in | of )
                \ an\ `extends`\ clause\ of\ a\ class\ definition
                (
                    \.
                |
                    \ but\ a\ `super`\ call\ to\ it\ will\ cause\ an\ exception\.
                |
                    \.
                    \ Subclass\ constructors\ that\ intend\ to\ inherit\ the\ (specified|exotic)\ 
                        ( \w+ | `\w+` )
                    \ behaviour\ must\ include\ a\ `super`\ call\ to\ the\ 
                        ( \w+ | `\w+` )
                    \ constructor\ to(\ create\ and)?\ initialize\ 
                        ( a\ subclass\ instance | the\ subclass\ instance | subclass\ instances )
                    (
                        \ that\ are\ Array\ exotic\ objects.\ However,\ most\ of\ the\ `Array.prototype`\ methods\ are\ generic\ methods\ that\ are\ not\ dependent\ upon\ their\ \*this\*\ value\ being\ an\ Array\ exotic\ object\.
                    |
                        \ with\ 
                        (
                            the\ internal\ state\ necessary\ to\ support\ 
                            (
                                the(\ `\w+`\ and)?\ `\w+.prototype`\ built-in\ methods
                            |
                                the\ %\w+%`.prototype`\ built-in\ methods
                            )
                        |
                            an?\ \[\[\w+\]\]\ internal\ slot
                        |
                            the\ necessary\ internal\ slots
                        |
                            the\ internal\ slots\ necessary\ for\ built-in\ (.+)\ behaviour.
                            \ All\ ECMAScript\ syntactic\ forms\ for\ defining\ (.+)\ objects\ create(\ direct)?\ instances\ of\ (\w+)\.
                            \ There\ is\ no\ syntactic\ means\ to\ create\ instances\ of\ (\w+)\ subclasses
                            (\ except\ for\ the\ built-in\ GeneratorFunction,\ AsyncFunction,\ and\ AsyncGeneratorFunction\ subclasses)?
                        )
                        \.
                    )
                )
            ''', li_ist)
        ):
            pass

        elif li_ist == 'is designed to be subclassable. It may be used as the value of an *extends* clause of a class definition.':
            pass

        elif li_ist == 'acts as the abstract superclass of the various _TypedArray_ constructors.':
            pass

        elif li_ist == 'is not intended to be subclassed.':
            pass
        elif li_ist == 'is not intended to be used with the `new` operator or to be subclassed. It may be used as the value of an `extends` clause of a class definition but a `super` call to the BigInt constructor will cause an exception.':
            pass

        # ----------------------
        # properties

        elif li_ist == 'contains two functions, `parse` and `stringify`, that are used to parse and construct JSON texts.':
            section.put_fact(subject, 'has-prop', S_Property('*"parse"*',     {}))
            section.put_fact(subject, 'has-prop', S_Property('*"stringify"*', {}))

        elif mo := re.fullmatch(r'has a (\*"\w+"\*) property whose( initial)? value is (.+) and whose attributes are ({.+})\.', li_ist):
            section.put_fact(subject, 'has-prop', S_Property(mo.group(1), {'[[Value]]': mo.group(3), **attr_string_to_dict(mo.group(4))}))
        elif mo := re.fullmatch(r'has a (\*"\w+"\*) property whose( initial)? value is (.+)\.', li_ist):
            section.put_fact(subject, 'has-prop', S_Property(mo.group(1), {'[[Value]]': mo.group(3)}))

        elif mo := re.fullmatch(r'has properties that are indirectly inherited by all \w+ instances\.', li_ist):
            pass
        elif mo := re.fullmatch(r'has properties that are inherited by all (.+) Iterator objects\.', li_ist):
            pass
        elif li_ist == 'has properties that are inherited by all Iterator Helper objects.':
            pass
        elif li_ist == 'along with its corresponding prototype object, provides common properties that are inherited by all _TypedArray_ constructors and their instances.':
            pass

        elif li_ist == 'may have host-defined properties in addition to the properties defined in this specification. This may include a property whose value is the global object itself.':
            pass

        elif li_ist in [
            'does not have a *"prototype"* property because Proxy objects do not have a [[Prototype]] internal slot that requires initialization.',
            'does not have a *"prototype"* property.',
        ]:
            pass

        elif li_ist in [
            'has the following properties:',
            'has the following additional properties:',
        ]:
            pass

        # -------------------
        # global name

        elif mo := re.fullmatch(r'is the initial value of the (\*"\w+"\*) property of the global object(, if that property is present \(see below\))?\.', li_ist):
            section.put_fact('the global object', 'has-prop', S_Property(mo.group(1), {'[[Value]]': subject}))

        elif li_ist == 'does not have a global name or appear as a property of the global object.':
            pass

        # -------------------
        # other

        elif li_ist == 'is never directly accessible to ECMAScript code.':
            pass

        elif re.fullmatch('is an intrinsic object that has the structure described below, differing only in the name used as the constructor name instead of _TypedArray_, in <emu-xref [^<>]+></emu-xref>.', li_ist):
            pass

        elif li_ist == 'is a subclass of `Function`.': # This should be above, but I'm not sure where it fits in.
            pass

        elif li_ist == 'is created before control enters any execution context.':
            pass

        else:
            assert 0, li.inner_source_text().strip()

    # ----------------------------------------------------

    # TODO: convert to scan_section?
    # Not with ispl, because I don't think there's any overlap.
    # But just to be more consistent in processing.
    # And also to be alerted if a pattern is no longer used.
    for child in section.block_children[2:]:
        if child.element_name == 'p':
            cst = child.inner_source_text()
            if re.match(r'Unless explicitly (defined|stated) otherwise, the methods of the (Date|Number|String) prototype object defined below are not generic and the \*this\* value passed to them must be ', cst):
                # The methods in question refer to "this Foo object/value" (or don't),
                # so I don't need to do anything extra to handle this sentence.
                pass
            elif cst.startswith('The abstract operation <dfn'):
                # The preamble to an emu-alg. Handled in _handle_other_section().
                pass
            elif (
                cst.startswith('In following descriptions of functions that are properties of the Date prototype object, the phrase “<dfn id="this-Date-object">this Date object</dfn>” refers to')
                or
                re.match(r'The phrase “this (Number|BigInt) value” within the specification of a method refers to', cst)
            ):
                # I just hard-code these. They're unlikely to change.
                pass
            elif (
                cst.startswith('The Atomics object provides functions that') # 25.4
                or
                cst.startswith('The JSON Data Interchange Format is defined in ECMA-404.')
            ):
                # No specific normative content?
                pass
            elif cst == 'Whenever a host does not provide concurrent access to SharedArrayBuffers it may omit the *"SharedArrayBuffer"* property of the global object.':
                # Not sure yet whether I'm going to provide it or not.
                pass
            else:
                assert 0
        elif child.element_name == 'emu-alg':
            # Handled in _handle_other_section()
            pass
        elif child.element_name == 'emu-note':
            pass
        else:
            assert 0, child.element_name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def extract_intrinsic_info_from_CallConstruct_section(section):

    mo = re.fullmatch(r'(\S+) \([^()]+\)', section.section_title)
    assert mo
    name = mo.group(1)
    section.put_fact(name, 'is', 'a constructor')

    if name in non_global_wkis or f"%{name}%" in non_global_wkis:
        # (Currently: %ThrowTypeError%, %TypedArray%, GeneratorFunction, AsyncGeneratorFunction, AsyncFunction)
        # The function defined by this section
        # is a well-known intrinsic,
        # but doesn't have a global name.
        # (I.e., it isn't the value of a property of the global object.)
        section.this_property = None
    else:
        section.this_property = types.SimpleNamespace()
        section.this_property.container = 'the global object'
        section.this_property.key = pystr_to_spec_String_literal(name)

    section.this_object = name

    ispl.scan_section(section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def extract_intrinsic_info_from_property_section(section):

    # Skip sections that are within "Properties of Foo Instances" sections.
    # TODO: move this distinction into section_kind?
    anc = section
    while True:
        if anc.section_kind.startswith('instances:'):
            # {section} is within a "Properties of Foo Instances" section.
            return
        if anc.section_kind.startswith('intrinsic:'):
            # This is what I want.
            break
        anc = anc.parent

    # -------------------------------------------------

    # We know that this section is telling us about
    # some property of some intrinsic/global object.
    # Figure out which object and which property.

    id_from_title = re.sub(r' \(.*', '', section.section_title)

    if mo := re.fullmatch('(get|set) (.+)', id_from_title):
        (getset, path) = mo.groups()
    else:
        getset = None
        path = id_from_title

    (t_container, t_key) = split_prop_path(path)

    if t_container is None:
        assert (
            section.parent.section_title.endswith(' Properties of the Global Object')
            or
            section.parent.parent.section_title.endswith(' Properties of the Global Object')
        )
        t_container = 'the global object'

    section.this_property = types.SimpleNamespace()
    section.this_property.container = t_container
    section.this_property.key       = t_key

    section.this_property_has_attributes({})
    # Running scan_section on the section's content
    # will almost certainly expand on this fact,
    # but this is a backstop in case it doesn't.

    # --------------------------------------------

    # First, dispense with sections that are simply a cross-reference to another section.
    # All they tell us is that the property exists, and we've already captured that.

    if section.section_kind.endswith('_xref'):
        assert section.bcen_str == 'p'
        p = section.block_children[0]
        p_ist = p.inner_source_text()
        mo = re.fullmatch(r'See <emu-xref href="#([^"]+)"></emu-xref>\.', p_ist)
        assert mo
        refd_id = mo.group(1)

        if section.this_property.key == '*"WeakSet"*':
            assert refd_id == 'sec-weakset-objects'
            # But that's inconsistent:
            # within "Constructor Properties of the Global Object",
            # the clause for "Foo ( . . .)" references "The Foo Constructor"
            # (SPEC BUG, ish)
            refd_id = 'sec-weakset-constructor'
        return

    # ---------------------------------------

    # The phrase `Foo.prototype` (without percents) is 'isolated'.
    #
    # The spec doesn't explicitly equate `Foo.prototype` with `the Foo prototype object`,
    # but when you get a section entitled "Properties of the Foo Prototype Object"
    # and its child-sections have titles like "Foo.prototype.bar",
    # then it's pretty clear that we are to treat the phrases in question as synonyms
    # (in this context at least).
    # 
    # (True, the spec does equate `the Foo prototype object` with %Foo.prototype%,
    # which is by definition initially-equivalent to %Foo%.prototype,
    # which is initially-equivalent to Foo.prototype
    # *if* %Foo% is initially-equivalent to Foo,
    # but that isn't always the case,
    # and I don't want to have to look elsewhere to find that out.)
    #
    # So I use the former criterion to establish the equivalence.

    if section.this_property.container.endswith('.prototype'):
        if mo := re.fullmatch(r'Properties of the (\S+) Prototype Object', section.parent.section_title):
            section.put_fact(mo.expand(r'the \1 prototype object'), 'is-aka', section.this_property.container)
        elif mo := re.fullmatch(r'Properties of the (_\w+_) Prototype Objects', section.parent.section_title):
            section.put_fact(mo.expand(r'each \1 prototype object'), 'is-aka', section.this_property.container)

    # --------------------------------------------------------

    # There's a similar problem (and similar solution) for
    # constructors that aren't properties of the global object.
    #
    # E.g., consider AsyncFunction:
    # The WKI table declares %AsyncFunction% but doesn't (can't) give it a global name,
    # and under "ECMAscript Language Association" says
    # "The constructor of async function objects (27.7.1)"
    # That phrase isn't useful for my purposes, because it doesn't occur elsewhere.
    # 27.7.1 equates "the AsyncFunction constructor" to %AsyncFunction%,
    # but "AsyncFunction" (which appears in section titles) is terminologically isolated.

    # (This isn't a problem for constructors that *are* global properties,
    # because for them, the WKI table equates %Foo% with `Foo`.)

    if mo := re.fullmatch(r'Properties of the (\S+) Constructor', section.parent.section_title):
        section.put_fact(mo.expand(r'the \1 constructor'), 'is-aka', section.this_property.container)
    elif mo := re.fullmatch(r'Properties of the (_\w+_) Constructors', section.parent.section_title):
        section.put_fact(mo.expand(r'each \1 constructor'), 'is-aka', section.this_property.container)

    # -------------------------------------------------

    # Ultimately, I need to know what all the distinct intrinsics are,
    # so I'm arranging things so that every distinct percent-delimited name
    # mentioned in a fact denotes a distinct intrinsic.
    #
    # In the facts for this section, I'll be using `section.this_object`
    # to refer to the intrinsic object defined by this section, if any.
    # So if this section *doesn't* define an intrinsic object,
    # it's important that I not accidentally generate a fact that mentions
    # section.this_object.
    # As a safeguard, I'll only set `section.this_object`
    # when I expect this section to define an intrinsic object.

    if section.section_kind == 'accessor_property':
        section_defines_object = True

    elif section.section_kind == 'function_property':
        # We know, from the parameter list in the section heading,
        # that this section defines an intrinsic data property
        # whose [[Value]] is a function object.
        #
        # However, that function object might be defined elsewhere.
        # E.g. Date.prototype.toGMTString and Date.prototype.toUTCString
        # are the same function. The section for Date.prototype.toGMTString
        # just refers to %Date.prototype.toUTCString%

        for child in section.block_children:
            if (
                child.element_name == 'p'
                and
                re.fullmatch(
                    r'The initial value of the \S+ property is %\S+%(, defined in .+)?\.',
                    child.inner_source_text()
                )
            ):
                # The function object is defined elsewhere,
                section_defines_object = False
                break
        else:
            section_defines_object = True
        
    elif section.section_kind == 'other_property':
        if section.section_title == 'Array.prototype [ %Symbol.unscopables% ]':
            # The only not-well-known intrinsic that isn't a function?
            section_defines_object = True
        else:
            # The [[Value]] of the property defined by this section
            # is either a primitive value
            # (e.g. Math.PI or Math[%Symbol.toStringTag%]),
            # or an object defined elsewhere
            # (e.g. Array.prototype or Array.prototype.constructor).
            section_defines_object = False

    else:
        assert 0, section.section_kind

    if section_defines_object:
        section.this_object = id_from_title

    # -----------------------------------

    ispl.scan_section(section)

# ==============================================================================

# Intrinsic Section Pattern/Parsing List
# i.e., a list of patterns (and corresponding actions)
# with which to "parse" (roughly speaking)
# a section that gives info about an intrinsic
# (except for a <p><ul> section, probably).
#
# Note that order is significant:
# Text might match multiple patterns,
# but the earliest of them is the one that succeeds.
# (So in general, specific patterns should precede general patterns.)

ispl_units = []

def for_patterns(*patterns):
    pattern_list = []
    for pattern in patterns:
        if not isinstance(pattern, tuple):
            pattern = tuple([pattern])

        pattern_atoms = []
        for pattern_str in pattern:
            assert isinstance(pattern_str, str)
            if re.fullmatch(r'[\w-]+', pattern_str):
                # This is just the name of an element (HNode)
                pattern_atom = pattern_str
            else:
                # This is a regex for the text of a <p> element.
                pattern_atom = ('p', pattern_str)
            pattern_atoms.append(pattern_atom)
        pattern_list.append(pattern_atoms)

    def decorator(func):
        for pattern in pattern_list:
            ispl_units.append((pattern, func))
        return func

    return decorator

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# ==============================================================================
# The section defines an accessor property,
# or just the [[Get]] or [[Set]] attribute of an accessor property.

@for_patterns(
    (r"{THIS} is an accessor property whose set accessor function is \*undefined\*\. Its get accessor function performs the following steps when called:", 'emu-alg')
)
def _(section, mo, emu_alg):
    confirm_this_property(section, mo.group('this'))

    propAttrs = {
        '[[Get]]': section.this_object,
        '[[Set]]': '*undefined*',
    }
    section.this_property_has_attributes(propAttrs)

    section.defines_a_function_via('emu-alg')

# -------------------

@for_patterns(
    r"{THIS} is an accessor property with attributes {ATTRS}. The \[\[Get\]\] and \[\[Set\]\] attributes are defined as follows:"
)
def _(section, mo):
    assert section.bcen_str in ['p', 'p emu-note']
    # I.e., the <p> that matches the above is the only block-child in the section.
    # <emu-note> after child-sections is odd?
    # The "as follows:" refers to the following two subsections.

    (g, s) = section.section_children
    assert g.section_title.startswith('get ')
    assert s.section_title.startswith('set ')
    propAttrs = {
        '[[Get]]': g.section_title,
        '[[Set]]': s.section_title,
        **attr_string_to_dict(mo.group('attrs'))
    }
    section.this_property_has_attributes(propAttrs)

# ------------------------------------------------------------------------------

@for_patterns(
    (r'The value of the (\[\[[GS]et\]\]) attribute is a built-in function that .+\. It performs the following steps when called:', 'emu-alg')
)
def _(section, mo, emu_alg):
    propAttrs = { mo.group(1): section.this_object }
    section.this_property_has_attributes(propAttrs)

    section.defines_a_function_via('emu-alg')

# ==============================================================================
# Blocks that indicate that this section defines a intrinsic function
# (other than an accessor function, handled above).
# This function is usually the initial value of a data property (of some intrinsic object),
# but in some cases it's an 'orphan'.

# ------------------------------------------------------------------------------

@for_patterns(
    (r"{THIS_FUNCTION} performs the following steps when called:", 'emu-alg'),
)
def _(section, mo, emu_alg):
    check_this_function(section, mo)
    section.this_property_has_attributes({'[[Value]]': section.this_object})
    section.defines_a_function_via('emu-alg')

# ----------------------------------------------------------

@for_patterns(
    # `sort` has lots of unique sentences
    (
        r"This method sorts the elements of this array\. .+",
        r"It performs the following steps when called:",
        'emu-alg',
        'emu-note',
        'emu-note',
        'emu-note',
    ),

    # Comment out this one to find cases where a function's <emu-alg> appears without a preamble,
    # or with a preamble that doesn't mention "the following steps" or some such.
    'emu-alg',
)
def _(section, *_):
    section.this_property_has_attributes({'[[Value]]': section.this_object})
    section.defines_a_function_via('emu-alg')

# ------------------------------------------------------------------------------

@for_patterns(

    (r"An ECMAScript implementation that includes the ECMA-402 Internationalization API must implement {THIS_FUNCTION} as specified in the ECMA-402 specification\. If an ECMAScript implementation does not include the ECMA-402 API the following specification of this method is used."),
    (r"Given zero or more arguments, {THIS_FUNCTION} calls ToNumber on each of the arguments .+"),
    (r"Given zero or more arguments, {THIS_FUNCTION} returns .+"),
    (r"The interpretation and use of the arguments of {THIS_FUNCTION} are the same as for .+"),
    (r"The meanings? of the optional parameters to {THIS_FUNCTION} are defined in the ECMA-402 specification; implementations that do not include ECMA-402 support must not use those parameter positions for anything else."),

    (r"{THIS_FUNCTION} adds .+"),
    (r"{THIS_FUNCTION} applies .+"),
    (r"{THIS_FUNCTION} behaves .+"),
    (r"{THIS_FUNCTION} compares .+"),
    (r"{THIS_FUNCTION} computes .+"),
    (r"{THIS_FUNCTION} converts .+"),
    (r"{THIS_FUNCTION} copies .+"),
    (r"{THIS_FUNCTION} creates .+"),
    (r"{THIS_FUNCTION} interprets a String value .+"),
    (r"{THIS_FUNCTION} is a property of the global object. It computes a new version of a String value in which .+"),
    (r"{THIS_FUNCTION} is called by ECMAScript language operators .+"),
    (r"{THIS_FUNCTION} may be called with a variable number of arguments. .+"),
    (r"{THIS_FUNCTION} may be called with any number of arguments .+"),
    (r"{THIS_FUNCTION} notifies .+"),
    (r"{THIS_FUNCTION} parses .+"),
    (r"{THIS_FUNCTION} performs a regular expression match of .+"),
    (r"{THIS_FUNCTION} prepends .+"),
    (r"{THIS_FUNCTION} produces .+"),
    (r"{THIS_FUNCTION} provides .+"),
    (r"{THIS_FUNCTION} puts .+"),
    (r"{THIS_FUNCTION} removes .+"),
    (r"{THIS_FUNCTION} returns .+"),
    (r"{THIS_FUNCTION} searches .+"),
    (r"{THIS_FUNCTION} sets .+"),
    (r"{THIS_FUNCTION} works .+"),
)
def _(section, mo):
    check_this_function(section, mo)
    section.this_property_has_attributes({'[[Value]]': section.this_object})
    section.defines_a_function_via('prose')

@for_patterns(
    (r"This is a distinct method that.+"),
)
def _(section, mo):
    section.this_property_has_attributes({'[[Value]]': section.this_object})
    section.defines_a_function_via('prose')

# ==============================================================================
# Other blocks that give info about attributes
# of the data property defined by this section:

@for_patterns(
    (r"The( initial)? value of the {THIS} data property is an object created by the following steps:", 'emu-alg'),
)
def _(section, mo, emu_alg):
    confirm_this_property(section, mo.group('this'))
    section.this_property_has_attributes({'[[Value]]': section.this_object})
    section.put_fact(section.this_object, 'exists', '')

# ------------------------------------------------------------------------------

@for_patterns(
    (r"The( initial)? value of {THIS} is {VALUE} \({H_EMU_XREF}\)\. Each _NativeError_ constructor has a distinct prototype object\."),
    (r"The( initial)? value of {THIS} is {VALUE} \(see {H_EMU_XREF}\)\. This property has the attributes {ATTRS}\."),

    (r"The( initial)? value of the {THIS} property is {VALUE}, defined in {H_EMU_XREF}\."),
    (r"The( initial)? value of the {THIS}( data)? property is {VALUE}\."),
    (r"The( initial)? value of {THIS} is {VALUE}\."),

    (r"The initial value of the {THIS} property of the prototype for a given _NativeError_ constructor is {VALUE}\."),
    (r"The initial value of the {THIS} property of the prototype for a given _TypedArray_ constructor is {VALUE}\."),

)
def _(section, mo):
    if 'this' in mo.groupdict():
        confirm_this_property(section, mo.group('this'))

    if 'attrs' in mo.groupdict():
        attr_dict = attr_string_to_dict(mo.group('attrs'))
    else:
        attr_dict = {}

    section.this_property_has_attributes({'[[Value]]': mo.group('value'), **attr_dict})

# ------------------------------------------------------------------------------

@for_patterns(
    (r"(The Number value for .+)"), # should be?: "The value of [this property] is the Number value for ..."
)
def _(section, mo):
    section.this_property_has_attributes({'[[Value]]': mo.group(1)}) 

# ------------------------------------------------------------------------------

@for_patterns(
    (r"This property has the attributes {ATTRS}\."),
)
def _(section, mo):
    attr_dict = attr_string_to_dict(mo.group('attrs'))
    section.this_property_has_attributes(attr_dict)

# ==============================================================================
# Other blocks that give information about a (sub-)property
# of the object defined by this section

@for_patterns(
    r"The( initial)? value of the {SUB} property of {THIS_FUNCTION} is {VALUE}\.", # *"name"* x20
    r"The {SUB} property of {THIS_FUNCTION} is {VALUE}\.",          # *"length"* x28
)
def _(section, mo):
    check_this_function(section, mo)

    sub_prop_id = mo.group('sub')
    value_desc = mo.group('value')
    section.put_fact(
        section.this_object,
        'has-prop',
        S_Property(sub_prop_id, {'[[Value]]': value_desc}))

@for_patterns(
    r"The {SUB} property of {THIS_FUNCTION} has the attributes {ATTRS}." # %ThrowTypeError% ( )
)
def _(section, mo):
    check_this_function(section, mo)

    sub_prop_id = mo.group('sub')
    attr_dict = attr_string_to_dict(mo.group('attrs'))
    section.put_fact(
        section.this_object,
        'has-prop',
        S_Property(sub_prop_id, attr_dict)
    )

# ------------------------------------------------------------------------------

@for_patterns(
    (r"It is an anonymous built-in function object that is defined once for each realm.")
)
def _(section, mo):
    #> Functions that are identified as anonymous functions use the empty String as the value of the *"name"* property.
    section.put_fact(section.this_object, 'has-prop', S_Property('*"name"*', {'[[Value]]': '*""*'}))

# ==============================================================================
# Blocks that give other info about object defined by this section

@for_patterns(
    r'The value of the (\[\[\w+\]\]) internal slot of {THIS_FUNCTION} is {VALUE}.'
)
def _(section, mo):
    check_this_function(section, mo)
    section.put_fact(section.this_object, 'has-slot', S_InternalSlot(mo.group(1), mo.group('value')))

# ------------------------------------------------------------------------------

@for_patterns(
    (r"{THIS_FUNCTION} is the <dfn>(?P<percented>%.+%)</dfn> intrinsic object\."),
)
def _(section, mo):
    check_this_function(section, mo)
    section.put_fact(section.this_object, 'is-aka', mo.group('percented'))

# ==============================================================================
# Blocks that don't generate any intrinsic facts

@for_patterns(
    (r"{THIS_FUNCTION} is not generic[;.] .+"),
)
def _(section, mo):
    check_this_function(section, mo)

# ------------------------------------------------------------------------------

@for_patterns(
    (r'The initial value of the \*"globalThis"\* property of the global object in a Realm Record .+'),

    # -------

    (r"The last argument \(if any\) specifies the body .+"),

    # Other unique sentences
    (r"If the String conforms to the {H_EMU_XREF}, .+"),
    (r"The actual value of the string passed in step {H_EMU_XREF} is either .+"), # Should be emu-note?
    (r"Before performing the comparisons, this method performs the following steps to prepare the Strings:", 'emu-alg'),
    (r"Each `Math.random` function created for distinct realms must produce a distinct sequence of values from successive calls."),
    (r"When replacing a code unit of numeric value .+"),
    (r"If _start_ is strictly greater than _end_, they are swapped."),
    (r"If either argument is \*NaN\* or negative, it is replaced with zero; .+"),
    (r"In the IEEE 754-2019 double precision binary representation, .+"),
    (r"The <dfn>GlobalSymbolRegistry List</dfn> is an append-only List that is globally available. .+"),
    (r"The actual return values are implementation-defined .+"),
    (r"The meaning of the optional second and third parameters to this method .+"),
    (r"The optional _reviver_ parameter is a function that takes two parameters, .+"),
    (r"The optional parameters to this method are not used .+"),
    (r"The result must be derived according to the locale-insensitive case mappings .+"),
    (r"This property is non-writable and non-configurable to prevent tampering .+"), # should be an emu-note?

    (r"If `x` is any Date whose milliseconds amount is zero .+", 'pre', r"However, the expression", 'pre', "is not required to produce .+"),
)
def _(section, *_):
    pass

@for_patterns(
    ('emu-grammar'), # only in Function.prototype.toString
    ('emu-table'), # Symbol.for, "GlobalSymbolRegistry Record Fields"
    ('emu-note'),
)
def _(section, _):
    pass

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def ispl_prep(s):
    return (s
        .replace('{H_EMU_XREF}', r'<emu-xref href="#(?P<refd_id>[^"]+)">[^<>]*</emu-xref>')
        .replace('{ATTRS}', r'(?P<attrs>{[^{}]+})')
        .replace('{VALUE}', r'(?P<value>.+)')
        .replace('{SUB}',   r'(?P<sub>\S+)')
        .replace('{THIS}',  r'(?P<this>\S+)')
        .replace('{THIS_FUNCTION}', r'''(?P<this_function>(?x:
                ([Tt]he|[Aa]|Each)\ (?P<func_name1>\S+)\ (?P<func_what1>function|method|constructor\ function|constructor|intrinsic\ object)
                |
                (?P<func_name2>\S+)
                |
                [Tt]his\ (?P<func_what3>function|method)
            ))''')
    )

ispl = NodeGrammar(ispl_units, ispl_prep)

def _print_unused_ispl():
    stderr()
    stderr("Unused patterns in ispl:")
    n_shown = 0
    for pattern in ispl.each_unused_pattern():
        stderr('    ', pattern)
        n_shown += 1
    if n_shown == 0:
        stderr('    (none)')
    stderr()

# ------------------------------------------------------------------------------

def check_this_function(section, mo):
    # print(mo.group('this_function'))

    func_name = mo.group('func_name1') or mo.group('func_name2')
    if func_name and func_name != 'It':
        confirm_this_property(section, func_name)

        if mo.group(2) == 'Each':
            # e.g., "Each _NativeError_ function" or "Each _TypedArray_ constructor"
            # I think converting these to "This function" might be misleading.
            pass
        else:
            msg_at_posn(section.start_posn, f"Named function")

    # if '`' in mo.group(0): msg_at_posn(section.start_posn, 'check backtick')

    func_what = mo.group('func_what1') or mo.group('func_what3')
    if func_what:
        if (
            ('.prototype' in section.section_title or 'Prototype%' in section.section_title)
                and not section.section_title.startswith('get ')
            or
            section.this_object in [
                'Array.from',
                'Array.of',
                '%TypedArray%.from',
                '%TypedArray%.of',
            ]
        ):
            # We expect it to be referred to as a "method"
            if func_what != 'method':
                msg_at_posn(section.start_posn, f"Expected 'method', got {func_what!r}")
        else:
            # We don't expect it to be referred to as a "method"
            if func_what == 'method':
                msg_at_posn(section.start_posn, f"Didn't expect 'method', but got it")
                # This complains at:
                # - Array.from
                # - Array.of
                # - %TypedArray%.from
                # - %TypedArray%.of


def confirm_this_property(section, this_prop_t):
    # print(f"! ctp: {this_prop_t}")
    try:
        (p_container, p_key) = split_prop_path(detick(this_prop_t))
    except AssertionError:
        # print(f"! ctp: {this_prop_t!r}")
        return

    if section.this_property is not None:
        assert p_container == section.this_property.container or p_container is None
        assert p_key       == section.this_property.key
    else:
        assert p_container is None

# ------------------------------------------------------------------------------

def split_prop_path(path):
    if re.fullmatch(r'%Symbol\.\w+%', path):
        return (None, path)
    if mo := re.fullmatch(r'\*"\w+"\*', path):
        return (None, path)

    mo = re.fullmatch(r'(%\w+%|\w+)(\.\w+| ?\[ ?%Symbol\.\w+% ?\])*', path)
    assert mo, path

    if mo.group(2) is None:
        # Nothing after the first path component.
        # {path} is just a single word.
        assert re.fullmatch(r'\w+', path)
        return (None, pystr_to_spec_String_literal(path))

    else:
        # {path} is a proper path.
        # Split off the last component:
        mo = re.fullmatch(r'(.+?)(\.(\w+)| ?\[ ?(%Symbol\.\w+%) ?\])$', path)
        (g1, _, g3, g4) = mo.groups()
        if g3:
            return (g1, pystr_to_spec_String_literal(g3))
        elif g4:
            return (g1, g4)
        else:
            assert 0, path

# ------------------------------------------------------------------------------

def attr_string_to_dict(st):
    mo = re.fullmatch('{ (.+) }', st)
    assert mo
    fields = mo.group(1).split(', ')
    attrs = dict(
        re.fullmatch(r'(\[\[\w+\]\]): (.+)', field).groups()
        for field in fields
    )
    return attrs

def pystr_to_spec_String_literal(pystr):
    assert '"' not in pystr
    return f'*"{pystr}"*'

def detick(st):
    return st.replace('`', '')

# ==============================================================================

def section_this_property_has_attributes(section, propAttrs):
    if section.this_property is None:
        # stderr(f"! skipping {propAttrs} in {section.section_title} because it doesn't define a property")
        return

    section.put_fact(
        section.this_property.container,
        'has-prop',
        S_Property(section.this_property.key, propAttrs)
    )

setattr(HNode, 'this_property_has_attributes', section_this_property_has_attributes)

# ------------------------------------------------------------------------------

def section_defines_a_function_via(section, mechanism):
    assert mechanism in ['emu-alg', 'prose']
    section.put_fact(section.this_object, 'is', 'a function object')
    section.put_fact(section.this_object, 'has-slot', S_InternalSlot('[[ccb]]', f"{mechanism} in {section.section_id}"))

setattr(HNode, 'defines_a_function_via', section_defines_a_function_via)

# ------------------------------------------------------------------------------

NativeError_expansions = None
TypedArray_expansions = None

def section_put_fact(section, L, verb, R):

    section.intrinsic_facts_raw.append((L,verb,R))

    # ----------------------------------------------------------------
    # Expand facts involving 'variables' (_NativeError_, _TypedArray_)

    global NativeError_expansions, TypedArray_expansions
    if NativeError_expansions is None:
        NativeError_section = spec.node_with_id_['sec-native-error-types-used-in-this-standard']
        NativeError_expansions = [
            child.section_title
            for child in NativeError_section.section_children
        ]

        TypedArray_table = spec.node_with_id_['table-the-typedarray-constructors']
        TypedArray_expansions = [
            re.sub(r'<br>\n.+', '', row.cell_texts[0])
            for row in TypedArray_table._data_rows
        ]

    expanded_facts = []

    for (name, expansions) in [
        ('NativeError', NativeError_expansions),
        ('TypedArray',  TypedArray_expansions),
    ]:
        uvar = f"_{name}_"
        if uvar in section.section_title:
            # We expect every fact in this section to reference {uvar}.

            for expansion in expansions:

                def expand_str(s):
                    return (s
                        .replace(f'the corresponding {uvar} prototype intrinsic object (<emu-xref href="#sec-properties-of-typedarray-prototype-objects"></emu-xref>)', f'the {expansion} prototype object') # SPEC: drop "intrinsic"?
                        .replace(f'the constructor itself', f'the {expansion} constructor')
                        .replace(f'the String value consisting of the name of the constructor (the name used instead of _NativeError_)', f'*"{expansion}"*')

                        .replace(f"each {uvar}", f"the {expansion}")
                        .replace(f"a {uvar}", f"the {expansion}") # for "a _NativeError_ prototype object" SPEC BUG?
                        .replace(uvar, expansion)
                        .replace(f'the String value <emu-val>"<var>{name}</var>"</emu-val>', f'*"{expansion}"*')

                        .replace('the String value of the constructor name specified for it in <emu-xref href="#table-the-typedarray-constructors"></emu-xref>', f'*"{expansion}"*')
                    )

                def expand_attrs(attrs):
                    return {
                        n: expand_str(v)
                        for (n, v) in attrs.items()
                    }

                # -------------------

                assert isinstance(L, str)
                xL = expand_str(L)

                if isinstance(R, str):
                    xR = expand_str(R)

                elif isinstance(R, S_InternalSlot):
                    xR = S_InternalSlot(
                        R.name,
                        expand_str(R.value),
                    )
                elif isinstance(R, S_Property):
                    xR = S_Property(
                        expand_str(R.key),
                        expand_attrs(R.attrs)
                    )
                else:
                    assert 0, R

                xfact = (xL, verb, xR)
                expanded_facts.append(xfact)

            break

    else:
        xfact = (L, verb, R)
        expanded_facts.append(xfact)

    # -----------------------------------------

    # Normalize object-references

    for (xL, verb, xR) in expanded_facts:

        nL = get_pdn(xL)

        def normalize_str(s):
            if s.startswith((
                '*',
                'the largest',
                'the smallest',
                'the Number value',
                'The Number value',
                'the Element Size',
                'the empty String',
                'the String value',
                'the well-known symbol',
                '1', # SPEC BUG
            )):
                # It denotes a primitive value
                return s
            elif s.startswith((
                'host-defined',
                'emu-alg in',
                'prose in',
            )):
                # Hm
                return s
            else:
                # It refers to an intrinsic object
                return get_pdn(s)

        def normalize_attrs(attrs):
            return {
                n: normalize_str(v)
                for(n, v) in attrs.items()
            }

        if verb in ['exists', 'is']:
            nR = xR
        elif isinstance(xR, str):
            nR = normalize_str(xR)
        elif isinstance(xR, S_InternalSlot):
            nR = S_InternalSlot(
                xR.name,
                normalize_str(xR.value),
            )
        elif isinstance(xR, S_Property):
            nR = S_Property(
                xR.key,
                normalize_attrs(xR.attrs)
            )
        else:
            assert 0, xR

        if verb == 'is-aka':
            assert nL == nR
        else:
            normalized_fact = (nL, verb, nR)
            section.intrinsic_facts_cooked.append(normalized_fact)

setattr(HNode, 'put_fact', section_put_fact)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _print_intrinsic_facts():
    facts_f = shared.open_for_output('intrinsic_facts')
    def put(*args): print(*args, file=facts_f)

    for section in spec.root_section.each_descendant_that_is_a_section():
        if section.intrinsic_facts_raw:
            put()
            put(section.section_num, section.section_title)
            for (L,verb,R) in section.intrinsic_facts_raw:
                put(f"    {L} {verb.upper()} {R}")

    facts_f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _print_section_kinds():
    sections_f = shared.open_for_output('sections')

    for section in spec.root_section.each_descendant_that_is_a_section():
        if not(hasattr(section, 'section_kind')): section.section_kind = 'UNSET!'
        print("%s%-47s%s %s" % (
                '  '*(section.section_level-1),
                section.section_kind,
                section.section_num,
                section.section_title
            ),
            file=sections_f
        )

    sections_f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _check_aoids():
    for section in spec.root_section.each_descendant_that_is_a_section():
        aoid = section.attrs.get('aoid', None)
        op_name = section.alg_headers[0].name if section.alg_headers else None

        if section.section_kind == 'shorthand':
            assert op_name is None
            # aoid might or might not be None

        else:

            if section.section_kind == 'catchall':
                assert (
                    op_name is None
                )

                if section.parent.section_title == 'Relations of Candidate Executions':
                    # Should we have a 'relation' kind?
                    # (The Memory Model clauses are weird.)
                    expected_aoid = section.section_title
                else:
                    expected_aoid = None

            elif section.section_kind == 'syntax_directed_operation':
                expected_aoid = None

            else:
                expected_aoid = None

            if aoid != expected_aoid:
                if aoid is None:
                    msg = f'Should this clause have aoid="{expected_aoid}"?'
                elif expected_aoid is None:
                    msg = f"Didn't expect this clause to have an aoid"
                else:
                    msg = f'Expected aoid="{expected_aoid}"'

                msg_at_node(section, msg)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _check_section_order():
    # In some sections, the subsections should be in "alphabetical order".

    for section in spec.root_section.each_descendant_that_is_a_section():
        if section.section_kind.endswith('// properties'):
            # Each descendant section (if any) is expected to define a property.
            prev_title = None
            prev_t = None
            for child in section.section_children:
                if child.section_kind in [
                    'accessor_property',
                    'function_property',
                    'function_property_xref',
                    'other_property',
                    'other_property_xref',
                ]:
                    t = child.section_title
                    t = t.lower()
                    t = t.replace('int8', 'int08')
                    t = re.sub(r'^get ', '', t)
                    t = re.sub(r'(^|\.)__', r'\1zz__', t) # to put __proto__ last
                    if section.section_title == 'Properties of the RegExp Prototype Object':
                        t = re.sub(r' \[ %symbol\.(\w+)% \]', r'.\1', t)
                    else:
                        t = re.sub(r' \[ %symbol\.(\w+)% \]', r'.zz_\1', t)
                    if prev_t is not None and t <= prev_t:
                        msg_at_node(child, '"%s" should be before "%s"' % (child.section_title, prev_title))
                    # TODO: collate digits after letters
                    prev_t = t
                    prev_title = child.section_title

                else:
                    if section.section_title == 'URI Handling Functions':
                        # PR #2839 made AOs 'Encode' + 'Decode' siblings of functions
                        assert child.section_kind == 'abstract_operation'
                    else:
                        assert child.section_kind in [
                            '- // properties',
                            'catchall',
                        ], child.section_kind

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def AlgHeader_make(
    *,
    section,
    species,
    name,
    params,
    node_at_end_of_header,
    for_phrase           = None,
    for_phrase_node      = None,
    return_nature_node   = None,
    preamble_nodes       = None,
):
    alg_header = AlgHeader()
    alg_header.section = section
    alg_header.species = species
    alg_header.name = name
    alg_header.node_at_end_of_header = node_at_end_of_header
    alg_header.for_phrase = for_phrase
    alg_header.for_phrase_node = for_phrase_node
    alg_header.return_nature_node = return_nature_node

    if params is not None:
        assert all(isinstance(param, AlgParam) for param in params)
        alg_header.params = params

    if preamble_nodes:
        fpr.check_header_against_prose(alg_header, preamble_nodes)

    alg_header.finish_initialization()

    section.alg_headers.append(alg_header)

    return alg_header

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def each_item_in_left_recursive_list(list_node):
    if len(list_node.children) == 1:
        [item_node] = list_node.children
        yield item_node
    elif len(list_node.children) == 2:
        [list_node, item_node] = list_node.children
        yield from each_item_in_left_recursive_list(list_node)
        yield item_node
    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
