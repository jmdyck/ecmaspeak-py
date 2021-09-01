
# ecmaspeak-py/Section.py:
# Identify "sections" in the spec, and ascertain their 'kind'.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, string, time
from collections import OrderedDict

import shared
from shared import stderr, header, msg_at_posn, spec
from HTML import HNode
import Pseudocode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def make_and_check_sections():
    stderr("make_and_check_sections ...")

    Pseudocode.create_all_parsers()

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
    section.ste = {'op_name': 'Early Errors', 'parameters': OrderedDict()}

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
            handle_early_error(curr_emu_grammar, child, section)
        elif child.element_name in ['p', 'emu-note']:
            pass
        else:
            assert 0, child.element_name

    return True

# ------------------------------------------------------------------------------

def handle_early_error(emu_grammar, ul, section):
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
            Pseudocode.alg_add_defn('op: early error', 'Early Errors', emu_grammar, ee_rule, section)
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
            #! assert 'op_name' not in section.ste
            #! section.ste['op_name'] = 'regexp-Evaluate'
            #! section.ste['parameters'] = OrderedDict()

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

    if section.section_title in ['Statement Rules', 'Expression Rules']:
        section.ste = section.parent.ste.copy()

    else:
        section.ste = {'op_name': sdo_name}

        # Parameters, if any, are stated in the section's first paragraph.
        parameters = OrderedDict()
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
                        else:
                            assert re.match(r'^_[a-zA-Z]+_$', param), param
                            param_name = param
                        assert param_name not in parameters
                        parameters[param_name] = part_punct
                section.block_children.pop(0)
                _set_bcen_attributes(section)
        section.ste['parameters'] = parameters

    # -----

    if section.section_title == 'Static Semantics: HasCallInTailPosition':
        assert len(section.block_children) == 1
        assert section.block_children[0].element_name == 'emu-note'
        assert len(section.section_children) == 2
        return True

    # ------------------------------------------------------------------------------

    if 'emu-grammar' in section.bcen_set:
        assert section.bcen_set <= set(['emu-grammar', 'emu-alg', 'emu-note', 'emu-table', 'p'])
        # Each <emu-grammar> + <emu-alg> pair in an SDO unit.

        used_indexes = set()
        for (i,c) in enumerate(section.block_children):
            if c.element_name == 'emu-alg':
                prev_c = section.block_children[i-1]
                handle_composite_sdo(sdo_name, prev_c, c, section)
                used_indexes.add(i)
                used_indexes.add(i-1)

        for i in range(len(section.block_children)):
            if i not in used_indexes:
                c = section.block_children[i]
                if c.element_name == 'emu-note':
                    # lots, ignore.
                    pass
                elif c.element_name == 'p':
                    # lots, ignore for now, but worth looking at.
                    pass
                elif c.element_name == 'emu-table':
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
                    # So I'll have to get that info eventually.
                    pass
                else:
                    stderr(f"\nERROR: {section.section_num} {section.section_title} has unexpected/unused <{c.element_name}> element")
                    sys.exit(1)


    elif 'ul' in section.bcen_set:
        handle_inline_sdo_section_body(section, sdo_name)

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
                    handle_composite_sdo(sdo_name, c, emu_alg, section)

                else:
                    # assert 0, p_text
                    # print('>', p_text)
                    pass
                    # skip it for now

    else:
        print(section.section_num, section.section_title, section.section_id)
        print(section.bcen_str)
        assert 0

    return True

# ------------------------------------------------------------------------------

def handle_composite_sdo(sdo_name, grammar_arg, code_hnode, section):
    assert isinstance(grammar_arg, HNode)
    assert isinstance(code_hnode, HNode)
    assert code_hnode.element_name == 'emu-alg'

    # ---------------------------
    # grammar_arg -> emu_grammar:

    if grammar_arg.element_name == 'emu-grammar':
        emu_grammar = grammar_arg

    elif grammar_arg.element_name == 'p':
        if grammar_arg.inner_source_text() == f"Every grammar production alternative in this specification which is not listed below implicitly has the following default definition of {sdo_name}:":
            # This is the default definition,
            # which isn't associated with a particular production.
            emu_grammar = None

        else:
            (emu_grammars, text) = extract_grammars(grammar_arg)
            assert len(emu_grammars) == 1
            [emu_grammar] = emu_grammars
            assert text == 'The production <G> evaluates as follows:'

    else:
        assert 0, grammar_arg.element_name

    # ----------

    Pseudocode.alg_add_defn('op: syntax-directed', sdo_name, emu_grammar, code_hnode, section)

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

# ------------------------------------------------------------------------------

def handle_inline_sdo_section_body(section, sdo_name):

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
                assert rule_sdo_name == sdo_name
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
                Pseudocode.alg_add_defn('op: syntax-directed', rule_sdo_name, rule_grammar, rule_expr, section)

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
        section.ste = {
            'op_name': op_name,
            'type': 'abstract operation',
            'parameters': {'_S_': ''},
        }

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
        section.ste = {
            'op_name': op_name,
            'parameters': {'_execution_': ''},
        }

    elif section.section_title in [
        'Races',
        'Data Races',
    ]:
        # 29.8, 29.9
        op_name = section.section_title
        assert section.block_children[0].source_text().startswith(
            "<p>For an execution _execution_, two events _E_ and _D_ in SharedDataBlockEventSet(_execution_) are in a "
        )
        parameters = {
            '_execution_': '',
            '_E_'        : '',
            '_D_'        : '',
        }
        section.ste = {
            'op_name': op_name,
            'parameters': parameters,
        }

    else:
        return False

    # --------------------------------------------

    section.section_kind = 'abstract_operation'

    emu_alg = section.block_children[1]
    assert emu_alg.element_name == 'emu-alg'
    Pseudocode.alg_add_defn('op: solo', op_name, None, emu_alg, section)

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
        _handle_structured_header(section)

    elif _handle_header_with_std_preamble(section):
        pass

    else:
        return False

    # --------------------------------------------------------------------------

    assert 'op_name' in section.ste
    op_name = section.ste['op_name']

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        # 13 cases

        if op_name in ['ToBoolean', 'ToNumber', 'ToString', 'ToObject', 'RequireObjectCoercible']:
            assert section.bcen_str == 'emu-table'
            emu_table = section.block_children[0]
            handle_op_table(emu_table, section, op_name)

        elif section.section_kind == 'env_rec_method_unused':
            pass

        elif op_name.startswith('Host'):
            # These are host-defined ops, so we expect no alg.
            Pseudocode.ensure_alg('op: host-defined', op_name)
            pass

        elif op_name == 'LocalTZA':
            Pseudocode.ensure_alg('op: implementation-defined', op_name)
            pass

        elif section.section_kind == 'numeric_method':
            # A mathematical operation that we merely constrain, via a bullet-list.
            Pseudocode.ensure_alg('op: numeric method', op_name)
            pass

        elif op_name == 'StringToBigInt':
            # Apply other alg with changes, ick.
            Pseudocode.ensure_alg('op: solo', op_name)

        else:
            assert 0, (section.section_num, section.section_title)

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        assert emu_alg.element_name == 'emu-alg'

        # The emu-alg is the 'body' of
        # (this definition of) the operation named by the section_title.

        if section.section_kind.endswith('abstract_operation'):
            Pseudocode.alg_add_defn('op: solo', op_name, None, emu_alg, section)

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

            op_species = {
                'numeric_method'   : 'op: numeric method',
                'env_rec_method'   : 'op: concrete method: env rec',
                'module_rec_method': 'op: concrete method: module rec',
                'internal_method'  : 'op: internal method',
            }[section.section_kind]

            Pseudocode.alg_add_defn(op_species, op_name, discriminator, emu_alg, section)

        else:
            assert 0, section.section_kind

    else:
        assert 0

    return True

# ------------------------------------------------------------------------------

def handle_op_table(emu_table, section, op_name):
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
            Pseudocode.alg_add_defn('op: solo', op_name, discriminator, b, section)

        elif x == '#LITERAL emu-note #LITERAL':
            # ToBoolean: row for 'Object' has a NOTE re [[IsHTMLDDA]]
            Pseudocode.alg_add_defn('op: solo', op_name, discriminator, b, section)

        elif x == '#LITERAL p #LITERAL p #LITERAL':
            (_, p1, _, p2, _) = b.children
            Pseudocode.alg_add_defn('op: solo', op_name, discriminator, b, section)
            pass

        elif x == '#LITERAL p #LITERAL emu-alg #LITERAL':
            (_, p, _, emu_alg, _) = b.children
            assert p.source_text() == '<p>Apply the following steps:</p>'
            Pseudocode.alg_add_defn('op: solo', op_name, discriminator, emu_alg, section)

        else:
            assert 0, x

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
        params_info = OrderedDict()
        param_nature_ = {}

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
        params_info = OrderedDict()
        param_nature_ = {}
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
                    is_optional = (optionality == 'optional ')
                    # params.append( (param_name, param_nature, is_optional) )
                    params_info[param_name] = '[]' if is_optional else ''
                    param_nature_[param_name] = 'TBD' if param_nature == 'unknown' else param_nature
                else:
                    assert mo.groups() == ()
            else:
                msg_at_posn(b, f"line doesn't match pattern /{expected_pattern}/")

        params = [* params_info.items() ]
        def brief_params(param_i):
            if param_i == len(params):
                return ''
            else:
                rest = brief_params(param_i + 1)
                (param_name, param_punct) = params[param_i]
                if param_punct == '[]':
                    comma = ' ' if param_i == 0 else ' , '
                    return f" [{comma}{param_name}{rest} ]"
                else:
                    comma = ' ' if param_i == 0 else ', '
                    return f"{comma}{param_name}{rest}"

        # overwrite section.section_title
        section.section_title = f"{which_semantics}{op_name} ({brief_params(0)} )"

    if '::' in op_name:
        (num_type, op_name) = re.fullmatch(r'(\w+)(::\w+)', op_name).groups()

    section.ste = {
        'op_name': op_name,
        'type': section_type,
        'parameters': params_info,
        'param_nature_': param_nature_,
    }

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
        section.ste['for_phrase'] = dl_dict['for']

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

        if retn: section.ste['return_nature_normal'] = ' or '.join(retn)
        if reta: section.ste['return_nature_abrupt'] = ' or '.join(reta)

    # --------------------------------------------------------------------------

    # Hack this for now:
    if section.ste['op_name'] == 'SortCompare':
        section.ste['also'] = [
            ('_comparefn_', 'from the current invocation of the `sort` method')
        ]
    elif section.ste['op_name'] in [
        'IsWordChar',
        'CharacterSetMatcher',
        'Canonicalize',
        'BackreferenceMatcher',
        'RegExpBuiltinExec',
        'CharacterRangeOrUnion',
    ]:
        section.ste['also'] = [
            ('_Input_'            , 'from somewhere'),
            ('_DotAll_'           , 'from somewhere'),
            ('_InputLength_'      , 'from somewhere'),
            ('_NcapturingParens_' , 'from somewhere'),
            ('_IgnoreCase_'       , 'from somewhere'),
            ('_Multiline_'        , 'from somewhere'),
            ('_Unicode_'          , 'from somewhere'),
            ('_WordCharacters_'   , 'from somewhere'),
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
        return False

    # -------------------------------
    # At this point, we're committed.

    if p_dict['kind'] == 'abstract operation':
        if '::' in p_dict['op_name']:
            section.section_kind = 'numeric_method'
            p_dict['op_name'] = re.sub(r'^\w+', '', p_dict['op_name'])
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

    parameters = convert_param_listing_to_dict(p_dict['params_str'])
    section.ste = {
        'op_name'   : p_dict['op_name'],
        'kind'      : p_dict['kind'],
        'parameters': parameters,
    }

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

        name_for_heading = p_dict['op_name']

        if section.section_title.startswith('Static Semantics:'):
            name_for_heading = 'Static Semantics: ' + name_for_heading

        if len(parameters) == 0:
            lines.append(f"{ind}  <h1>{name_for_heading} ( )</h1>")
        else:
            lines.append(f"{ind}  <h1>")
            lines.append(f"{ind}    {name_for_heading} (")
            for (param_name, param_punct) in parameters.items():
                optionality = 'optional ' if param_punct == '[]' else ''
                param_nature = 'unknown'
                lines.append(f"{ind}      {optionality}{param_name}: {param_nature},")
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

    return True

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

    p_dict = mo.groupdict()
    prop_path = p_dict['prop_path']
    section.ste = {
        'prop_path': prop_path,
        'parameters': (
            convert_param_listing_to_dict(p_dict['params_str'])
            if 'params_str' in p_dict
            else None
        ),
    }

    if section.section_title.startswith('get '):
        assert section.section_kind == 'accessor_property'
        # The spec leaves off the empty parameter list
        assert 'params_str' not in section.ste
        section.ste['params_str'] = ''
        section.ste['parameters'] = OrderedDict()

    n_emu_algs = section.bcen_list.count('emu-alg')

    if section.section_kind == 'function_property_xref':
        assert n_emu_algs == 0
        return True

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
        Pseudocode.alg_add_defn(bif_species, prop_path, None, None, section)

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        Pseudocode.alg_add_defn(bif_species, prop_path, None, emu_alg, section)

    else:
        assert prop_path in ['%TypedArray%.prototype.sort']
        # It's an odd combination of the emu-algs in the clause.
        # The first emu-alg is at least the *start* of the full algorithm.
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        Pseudocode.alg_add_defn(bif_species, prop_path, None, emu_alg, section)

        if True:
            assert n_emu_algs == 2
            # The second emu-alg defines the TypedArray SortCompare.
            emu_alg_posn = section.bcen_list.index('emu-alg', emu_alg_posn+1)
            emu_alg = section.block_children[emu_alg_posn]
            Pseudocode.alg_add_defn('op: solo', 'TypedArraySortCompare', None, emu_alg, section)

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
            Pseudocode.alg_add_defn('op: solo', 'initializer for @@unscopables', None, emu_alg, section)

        elif section.section_kind == 'properties_of_an_intrinsic_object':
            # In addition to telling you about the intrinsic object,
            # it also defines an abstract operation that is used
            # by the object's function properties.
            mo = re.fullmatch(r'Properties of the (\w+) Prototype Object', section.section_title)
            which = mo.group(1)
            op_name = f"this{'Time' if which == 'Date' else which}Value"

            preamble = section.block_children[emu_alg_posn-1]
            assert preamble.source_text() == f'<p>The abstract operation <dfn id="{op_name.lower()}" aoid="{op_name}" oldids="sec-{op_name.lower()}">{op_name}</dfn> takes argument _value_. It performs the following steps when called:</p>'

            Pseudocode.alg_add_defn('op: solo', op_name, None, emu_alg, section)

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
        Pseudocode.alg_add_defn('op: solo', aoid, None, body, section)

    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def convert_param_listing_to_dict(parameter_listing):
    params_info = OrderedDict()
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
            assert mo, section.section_title
            (opt_dots, param_name, rest) = mo.groups()

            assert param_name not in params_info

            assert not (opt_dots and subsequent_are_optional)

            if opt_dots:
                param_punct = '...'
            elif subsequent_are_optional:
                param_punct = '[]'
            else:
                param_punct = ''

            params_info[param_name] = param_punct

            if re.match(r'^( \])*$', rest):
                pass
            elif rest == ' [ ':
                subsequent_are_optional = True
            else:
                assert 0, (section.section_title, repr(param_str))

    return params_info

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_changes_section(section):

    # Assume this holds,
    # but be sure to undo it if we ultimately return False.
    section.section_kind = 'changes'

    if section.section_title == 'Pattern Semantics' and section.section_num.startswith('B.'):
        pass
    elif (mo := re.fullmatch('Changes to ([A-Z]\w+)', section.section_title)):
        pass
    elif (mo := re.fullmatch('Changes to (.+) Static Semantics: Early Errors', section.section_title)):
        pass
    elif section.section_title == 'VariableStatements in Catch Blocks':
        pass
    elif section.section_title == 'Initializers in ForIn Statement Heads':
        pass
    elif (mo := re.fullmatch('Changes to (.+)', section.section_title)):
        pass
    else:
        del section.section_kind
        return False

    # ==========================================================================

    section.ste = {}

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
                    f"During {op_name} the following steps are performed in place of step <emu-xref .+:",
                    f"The following steps replace step <emu-xref.+ of the {op_name} algorithm:",
                    f"The result column in .+ for an argument type of Object is replaced with the following algorithm:",
                ]
            ), p_ist

            emu_alg = section.block_children[i+1]
            assert emu_alg.element_name == 'emu-alg'
            Pseudocode.alg_add_defn('op: solo', op_name, None, emu_alg, section)
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
                re.fullmatch(fr'The rules for the following production in {emu_xref_re} are modified with the addition of the <ins>highlighted</ins> text:', p_ist)
                or
                re.fullmatch(fr'The content of subclause {emu_xref_re} is replaced with the following:', p_ist)
            ):
                emu_grammar = section.block_children[i]; i += 1
                ul = section.block_children[i]; i += 1
                handle_early_error(emu_grammar, ul, section)

            elif re.fullmatch(fr'The semantics of {emu_xref_re} is extended as follows:', p_ist):
                p2 = section.block_children[i]; i += 1
                assert p2.element_name == 'p'
                p2_ist = p2.inner_source_text()
                assert re.fullmatch(fr'Within {emu_xref_re} reference to &ldquo;{emu_grammar_re} &rdquo; are to be interpreted as meaning &ldquo;{emu_grammar_re} &rdquo; or &ldquo;{emu_grammar_re} &rdquo;\.', p2_ist)

            elif (
                re.fullmatch(r'.+ includes the following additional evaluation rules?:', p_ist)
                or 
                re.fullmatch(r'.+ The following evaluation rules(, with parameter _direction_,)? are also added:', p_ist)
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
                        handle_composite_sdo('regexp-Evaluate', emu_grammar, emu_alg, section)
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
                    assert re.fullmatch(r'Step <emu-xref.+></emu-xref> is replaced by:', p2_ist)

                    emu_alg = section.block_children[i]; i += 1
                    assert emu_alg.element_name == 'emu-alg'
                    Pseudocode.alg_add_defn('op: solo', 'EvalDeclarationInstantiation', None, emu_alg, section)

            elif re.fullmatch(fr'The following augments the \|\w+\| production in {emu_xref_re}:', p_ist):
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
                    re.fullmatch(fr'The (?:static|runtime) semantics of (\w+)( in {emu_xref_re})? are augmented with the following:', p_ist)
                )
                if mo:
                    op_name = mo.group(1)
                    emu_grammar = section.block_children[i]; i += 1
                    emu_alg = section.block_children[i]; i += 1
                    assert emu_grammar.element_name == 'emu-grammar'
                    assert emu_alg.element_name == 'emu-alg'
                    handle_composite_sdo(op_name, emu_grammar, emu_alg, section)

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

# vim: sw=4 ts=4 expandtab
