#!/usr/bin/python3

# ecmaspeak-py/Pseudocode.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, time, math, pdb, string, pprint
from collections import defaultdict

from HTML import HNode
from Pseudocode_Parser import Pseudocode_Parser, ANode
import emu_grammars
import shared
from shared import spec, stderr

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_stuff_with_pseudocode():
    check_step_references()

    create_all_parsers()
    analyze_sections()
    check_emu_alg_coverage()
    check_emu_eqn_coverage()
    report_all_parsers()

    analyze_static_dependencies()
    check_sdo_coverage()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_step_references():
    # This deals with the pseudocode in <emu-alg> elements,
    # though in a fairly superficial way.
    # (I.e., we don't need to have it parsed according to the emu-alg grammar.)

    f_step_refs = shared.open_for_output('step_refs')
    def put(*args): print(*args, file=f_step_refs)

    curr_referring_section = None
    for (referring_section, referring_line, step_ref, refd_line) in each_step_ref():
        if referring_section != curr_referring_section:
            put()
            put('-' * 40)
            put(referring_section.section_num)
            put(referring_section.section_title)
            curr_referring_section = referring_section
            curr_referring_line = None

        if referring_line != curr_referring_line:
            # This does the 'wrong' thing in EvalDeclarationInstantiation,
            # where there are two distinct referring lines with the exact same text
            put()
            put('    ' + referring_line)
            curr_referring_line = referring_line

        put()
        put(f"        step {step_ref}:")
        put(f"        {refd_line}")

    f_step_refs.close()

# ------------------------------------------------------------------------------

def each_step_ref():
    for mo in re.finditer(r'(?i)\bsteps* [0-9<]', spec.text):
        st = mo.start()

        referring_line = spec.text[spec.text.rindex('\n', 0, st)+1:spec.text.index('\n', st)].strip()

        text_n = find_deepest_node_covering_posn(st)
        assert text_n.parent.element_name in ['p', 'li', 'emu-alg', 'dd']

        referring_section = text_n.closest_containing_section()

        x = '<emu-xref href="#([-a-z0-9]+)"></emu-xref>'
        patterns = [
            fr'steps {x}, {x}, and {x}',
            fr'steps {x}-{x}',
             f'steps {x}\u2013{x}',
            fr'steps {x} and {x}',
            fr'step {x}',
        ]
        for pattern in patterns:
            mo = re.compile(pattern, re.IGNORECASE).match(spec.text, st)
            if mo:
                break
        else:
            assert 0, spec.text[st:st+200].replace('\n', '\\n')

        step_ids = mo.groups()
        ref_start_posn = mo.start()
        ref_end_posn = mo.end()

        def ref_is_preceded_by(s):
            return spec.text[ref_start_posn-len(s) : ref_start_posn] == s

        def ref_is_followed_by(s):
            return spec.text[ref_end_posn : ref_end_posn+len(s)] == s

        # -------------

        # Pin down which emu-alg is being referenced:

        if ref_is_followed_by(' in previous editions of this specification'):
            for step_id in step_ids:
                step_ref = step_id + ' in previous editions'
                refd_line = 'SKIP'
                yield (referring_section, referring_line, step_ref, refd_line)
            continue

        elif ref_is_followed_by(' of the IsLooselyEqual algorithm'):
            refd_alg_name = 'IsLooselyEqual'
            refd_section_id = 'sec-islooselyequal'
        elif ref_is_followed_by(' of the IsLessThan algorithm'):
            refd_alg_name = 'IsLessThan'
            refd_section_id = 'sec-islessthan'
        elif ref_is_followed_by(' in the algorithm for the addition operator `+`'):
            refd_alg_name = 'evaluation of the `+` operator'
            refd_section_id = 'sec-addition-operator-plus-runtime-semantics-evaluation'
        elif ref_is_followed_by(' in the algorithm that handles the addition operator `+`'): # compound_assignment branch
            refd_alg_name = 'ApplyStringOrNumericBinaryOperator'
            refd_section_id = 'sec-applystringornumericbinaryoperator'
        elif ref_is_followed_by(' in <emu-xref href="#sec-array.prototype.sort"></emu-xref>'):
            refd_alg_name = 'Array.prototype.sort'
            refd_section_id = 'sec-array.prototype.sort'
        elif ref_is_preceded_by('the same as [[Call]] (see <emu-xref href="#sec-built-in-function-objects-call-thisargument-argumentslist"></emu-xref>) except that '):
            refd_alg_name = '[[Call]] for built-in functions'
            refd_section_id = 'sec-built-in-function-objects-call-thisargument-argumentslist'
        elif ref_is_preceded_by('During FunctionDeclarationInstantiation the following steps are performed in place of '):
            refd_alg_name = 'FunctionDeclarationInstantiation'
            refd_section_id = 'sec-functiondeclarationinstantiation'
        elif ref_is_preceded_by('During GlobalDeclarationInstantiation the following steps are performed in place of '):
            refd_alg_name = 'GlobalDeclarationInstantiation'
            refd_section_id = 'sec-globaldeclarationinstantiation'
        elif ref_is_preceded_by('During EvalDeclarationInstantiation the following steps are performed in place of '):
            refd_alg_name = 'EvalDeclarationInstantiation'
            refd_section_id = 'sec-evaldeclarationinstantiation'
        elif ref_is_preceded_by('During BlockDeclarationInstantiation the following steps are performed in place of '):
            refd_alg_name = 'BlockDeclarationInstantiation'
            refd_section_id = 'sec-blockdeclarationinstantiation'
        elif referring_section.section_id == 'sec-variablestatements-in-catch-blocks':
            assert len(step_ids) == 1
            [step_id] = step_ids
            if 'throw' in step_id:
                refd_alg_name = 'EvalDeclarationInstantiation'
                refd_section_id = 'sec-evaldeclarationinstantiation'
            elif 'web-compat-bindingexists' in step_id:
                # super-kludge:
                # See https://github.com/tc39/ecma262/pull/1697#discussion_r411874379
                refd_alg_name = 'EvalDeclarationInstantiation as modified in B.3.3.3'
                refd_section_id = 'sec-web-compat-evaldeclarationinstantiation'
                # step_ids = [step_ids[0].replace('7.', '1.', 1)]
            else:
                assert 0, step_ids
        else:
            refd_alg_name = None
            refd_section_id = referring_section.section_id

        refd_section = spec.node_with_id_[refd_section_id]

        refd_section_algs = [
            node
            for node in refd_section.block_children
            if node.element_name == 'emu-alg'
        ]

        if len(refd_section_algs) == 0:
            assert 0
        elif len(refd_section_algs) == 1:
            [refd_alg] = refd_section_algs
        else:
            # somewhat kludgey:
            # (It would be more robust to know where the step-ref occurs
            # with respect to the algs, and then usually pick the preceding alg.)
            if refd_section.section_id == 'sec-algorithm-conventions-syntax-directed-operations':
                assert len(refd_section_algs) == 2
                refd_alg = refd_section_algs[0]
            elif refd_section.section_id == 'sec-function-calls-runtime-semantics-evaluation':
                assert len(refd_section_algs) == 2
                refd_alg = refd_section_algs[0]
            elif refd_section.section_id == 'sec-assignment-operators-runtime-semantics-evaluation':
                assert len(refd_section_algs) == 5
                if ref_is_followed_by(' of the first algorithm'):
                    refd_alg_name = "the first algorithm"
                    refd_alg = refd_section_algs[0]
                elif ref_is_followed_by(' of the second algorithm'):
                    refd_alg_name = "the second algorithm"
                    refd_alg = refd_section_algs[1]
                else:
                    continue # XXX PR 2030: I can't be bothered right now.
                    assert 0
            elif refd_section.section_id == 'sec-variable-statement-runtime-semantics-evaluation':
                assert len(refd_section_algs) == 5
                refd_alg = refd_section_algs[3]
            else:
                # Will create an error message in the step_refs file
                refd_alg = None

        # -------------

        for step_id in step_ids:

            if refd_alg is None:
                step_path = '???'
                refd_line = 'XXX: what should refd_alg be?'
            else:
                (step_path, refd_line) = get_step_line(refd_alg, step_id)

            extra = f" in {refd_alg_name}" if refd_alg_name else ''
            step_ref = step_path + extra

            yield (referring_section, referring_line, step_ref, refd_line)

# ------------------------------------------------------------------------------

def find_deepest_node_covering_posn(posn):
    def recurse(node):
        assert node.start_posn <= posn <= node.end_posn
        if node.children:
            for child in node.children:
                if child.start_posn <= posn <= child.end_posn:
                    return recurse(child)
            else:
                assert 0
        else:
            return node

    return recurse(spec.doc_node)

# ------------------------------------------------------------------------------

def get_step_line(emu_alg_n, step_id):

    # --------

    ist = emu_alg_n.inner_source_text().rstrip()
    alg_lines = [
        ( len(mo.group(1)), mo.group(2) )
        for mo in re.compile(r'\n( *)(.+)').finditer(ist)
    ]
    # pprint.pprint(alg_lines, stream=sys.stderr)

    def nestify(start_i, end_i):
        # Return a structure that captures the hierarchy
        # of alg_lines[start_i:end_i]

        if start_i == end_i: return []

        (indent_for_this_level, _) = alg_lines[start_i]
        i_of_lines_at_this_level = [
            i
            for i in range(start_i, end_i)
            if alg_lines[i][0] == indent_for_this_level
        ]
        assert i_of_lines_at_this_level[0] == start_i

        tups = []
        for (i, j) in zip(
            i_of_lines_at_this_level,
            i_of_lines_at_this_level[1:] + [end_i]
        ):
            # The lines that are subordinate to line `i`
            # run from `i+1` up to (but not including) line `j`.
            tup = (
                alg_lines[i][1],
                nestify(i+1, j)
            )
            tups.append(tup)

        return tups

    alg_tups = nestify(0, len(alg_lines))
    # pprint.pprint(alg_tups, stream=sys.stderr)

    # ----------

    level_formats = ['1', 'a', 'i', '1', 'a', 'i', 'i', 'i', 'i']

    level_formatters = {
        # arabic numerals:
        '1': lambda i: str(i+1),

        # lower-case alpha:
        'a': lambda i: string.ascii_lowercase[i],

        # lower-case roman:
        'i': lambda i: ['i', 'ii', 'iii', 'iv', 'v', 'vi'][i],
    }

    labelled_steps = {}

    def extract_labelled_steps(tups, path_to_parent):
        level = len(path_to_parent)
        level_format = level_formats[level]
        level_formatter = level_formatters[level_format]

        for (i, (line, subtups)) in enumerate(tups):
            path_piece = level_formatter(i)
            path_to_this_step = path_to_parent + [path_piece]
            mo = re.fullmatch(r'\d+\. \[id="([^"]+)"\] (.+)', line)
            if mo:
                (step_id, rest_of_line) = mo.groups()
                assert step_id not in labelled_steps
                labelled_steps[step_id] = (path_to_this_step, rest_of_line)

            extract_labelled_steps(subtups, path_to_this_step)

    extract_labelled_steps(alg_tups, [])

    # print(labelled_steps)

    # ----------

    if step_id not in labelled_steps:
        return (f"XXX index error: step_id {step_id} does not exist in this alg", 'xxx')

    (path_to_step, step_line) = labelled_steps[step_id]
    return ('.'.join(path_to_step), '1. ' + step_line)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def create_all_parsers():
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

        # # sneak this in...
        # n_lines = spec.text.count('\n', start_posn, end_posn)
        # if n_lines > 60:
        #     cc_section = hnode.closest_containing_section()
        #     print(f'\n    emu-alg with {n_lines} lines in {cc_section.section_num} "{cc_section.section_title}"')

    elif hnode.element_name == 'emu-eqn':
        assert what is None
        parser = emu_eqn_parser

    elif hnode.element_name == 'td':
        assert what is None
        parser = one_line_alg_parser

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
        return None

    connect_anodes_to_hnodes(hnode, tree)
    annotate_invocations(tree)
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

    sys.setrecursionlimit(2000)
    # This might not be necessary any more.

    for section in spec.root_section.each_descendant_that_is_a_section():
        assert hasattr(section, 'ste')

        # "progress bar"
        top_level_num = section.section_num.split('.')[0]
        if top_level_num != prev_top_level_num:
            stderr(f" {top_level_num}", end='', flush=True)
            prev_top_level_num = top_level_num

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
            'numeric_method',
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
                parse(emu_alg)
                # Most of these are involved in the definition of shorthands,
                # which I don't handle well.

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
            handle_early_error(curr_emu_grammar, child, section)
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
        assert len(section.block_children) == 1
        assert section.block_children[0].element_name == 'emu-note'
        assert len(section.section_children) == 2
        return

    sdo_name = section.ste['op_name']

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
                    handle_inline_sdo(child, sdo_name, section)
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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_other_op_section(section):
    assert 'op_name' in section.ste
    op_name = section.ste['op_name']

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        # 13 cases

        if op_name in ['ToBoolean', 'ToNumber', 'ToString', 'ToObject', 'RequireObjectCoercible']:
            assert section.bcen_str == 'emu-table'
            # The op is defined by a table that splits on argument type.
            # The second cell in each row is a little algorithm,
            # but it's generally not marked as an emu-alg.
            emu_table = section.block_children[0]
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

                handle_tabular_op_defn(op_name, a, b, section)

        elif op_name in ['CreateImmutableBinding', 'DeleteBinding']:
            assert section.section_id in [
                'sec-object-environment-records-createimmutablebinding-n-s',
                'sec-module-environment-records-deletebinding-n', # PR 1994
            ]
            # This is a bit odd.
            # The clause exists just to say that this definition doesn't exist.
            # discriminator = None # XXX get the discriminator!
            # emu_alg = None ?
            # handle_type_discriminated_op(op_name, section.section_kind, discriminator, emu_alg, section)
            pass

        elif op_name.startswith('Host'):
            # These are host-defined ops, so we expect no alg.
            ensure_alg('op: host-defined', op_name)
            pass

        elif op_name == 'LocalTZA':
            ensure_alg('op: implementation-defined', op_name)
            pass

        elif section.section_kind == 'numeric_method':
            # A mathematical operation that we merely constrain, via a bullet-list.
            ensure_alg('op: numeric method', op_name)
            pass

        elif op_name == 'StringToBigInt':
            # Apply other alg with changes, ick.
            ensure_alg('op: solo', op_name)

        else:
            assert 0, (section.section_num, section.section_title)

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        assert emu_alg.element_name == 'emu-alg'

        # The emu-alg is the 'body' of
        # (this definition of) the operation named by the section_title.

        if section.section_kind == 'abstract_operation':
            handle_solo_op(op_name, emu_alg, section)

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

            if op_name == 'DeleteBinding' and discriminator == 'module Environment Record':
                # "Assert: This method is never invoked"
                # So type-checking it will not confirm the signature.
                return

            handle_type_discriminated_op(op_name, op_species, discriminator, emu_alg, section)

        else:
            assert 0, section.section_kind


    else:
        assert section.section_kind == 'abstract_operation'

        assert re.fullmatch(r'p emu-alg( p emu-alg)+( emu-note)?', section.bcen_str)

        # The first emu-alg defines the operation.
        handle_solo_op(op_name, section.block_children[1], section)

        # Each subsequent emu-alg is (roughly) the [[Call]] alg for an anonymous built-in function.

        for i in range(2, len(section.block_children), 2):
            p = section.block_children[i]
            if p.element_name == 'emu-note': break
            emu_alg = section.block_children[i+1]

            assert p.element_name == 'p'
            assert emu_alg.element_name == 'emu-alg'

            ist = p.inner_source_text()
            mo = re.match(r'An? (\w+) function is an anonymous built-in function', ist)
            assert mo, ist
            name = mo.group(1)

            handle_function('bif: * per realm', name, emu_alg, section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_built_in_section(section):
    assert 'prop_path' in section.ste
    prop_path = section.ste['prop_path']

    n_emu_algs = section.bcen_list.count('emu-alg')

    if section.section_kind == 'function_property_xref':
        assert n_emu_algs == 0
        return

    bif_species = {
        'CallConstruct'               : 'bif: value of data property',
        'CallConstruct_overload'      : 'bif: value of data property: overload',
        'accessor_property'           : 'bif: accessor function',
        'anonymous_built_in_function' : 'bif: * per realm',
        'function_property'           : 'bif: value of data property',
        'function_property_overload'  : 'bif: value of data property: overload',
    }[section.section_kind]

    if n_emu_algs == 0:
        # Various possibilities:
        # - A Math function that we merely constrain, via a bullet-list.
        # - "This function is like that function" (except different, maybe).
        # - Other functions that we only define in prose.
        if prop_path == '%TypedArray%.prototype.set':
            # 22.2.3.23 contains 2 child clauses that define overloads for this function.
            return
        handle_function(bif_species, prop_path, None, section)

    elif n_emu_algs == 1:
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        handle_function(bif_species, prop_path, emu_alg, section)

    else:
        assert prop_path in ['Array.prototype.sort', '%TypedArray%.prototype.sort']
        # It's an odd combination of the emu-algs in the clause.
        # The first emu-alg is at least the *start* of the full algorithm.
        emu_alg_posn = section.bcen_list.index('emu-alg')
        emu_alg = section.block_children[emu_alg_posn]
        handle_function(bif_species, prop_path, emu_alg, section)

        if prop_path == '%TypedArray%.prototype.sort':
            assert n_emu_algs == 2
            # The second emu-alg defines the TypedArray SortCompare.
            emu_alg_posn = section.bcen_list.index('emu-alg', emu_alg_posn+1)
            emu_alg = section.block_children[emu_alg_posn]
            handle_solo_op('TypedArraySortCompare', emu_alg, section)

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
                    f"During {op_name} the following steps are performed in place of step <emu-xref .+:",
                    f"The following steps are inserted after step <emu-xref.+ of the {op_name} algorithm:",
                    f"The following steps replace step <emu-xref.+ of the {op_name} algorithm:",
                    f"The result column in .+ for an argument type of Object is replaced with the following algorithm:",
                ]
            ), p_ist

            emu_alg = section.block_children[i+1]
            assert emu_alg.element_name == 'emu-alg'
            handle_solo_op(op_name, emu_alg, section)
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

            if re.fullmatch(fr'The following Early Error rule is added to those in {emu_xref_re}\. .+', p_ist):
                ul_ex = section.block_children[i]; i += 1; assert ul_ex.element_name == 'ul'
                emu_grammar = section.block_children[i]; i += 1
                ul = section.block_children[i]; i += 1
                handle_early_error(emu_grammar, ul, section)

            elif (
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
                    handle_solo_op('EvalDeclarationInstantiation', emu_alg, section)

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
                    re.fullmatch(fr'In {emu_xref_re} the (PropertyDefinitionEvaluation) algorithm (.|\n)+ is replaced with the following definition:', p_ist)
                    or
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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_other_section(section):
    # The section_title doesn't declare an operation or a function-property,
    # so we don't expect an algorithm.
    # But sometimes there are some anyway.

    for child in section.block_children:
        if child.element_name == 'emu-eqn':
            handle_emu_eqn(child, section)

    n_emu_algs = section.bcen_list.count('emu-alg')

    if n_emu_algs == 0:
        if section.section_title == 'Mathematical Operations':
            ensure_alg('op: solo', 'abs')
            ensure_alg('op: solo', 'min')
            ensure_alg('op: solo', 'max')
            ensure_alg('op: solo', 'floor')
            ensure_alg('op: solo', '\U0001d53d')
            ensure_alg('op: solo', '\u211d')
            ensure_alg('op: solo', '\u2124')

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
            handle_solo_op('initializer for @@unscopables', emu_alg, section)

        elif section.section_kind == 'properties_of_an_intrinsic_object':
            # In addition to telling you about the intrinsic object,
            # it also defines an abstract operation that is used
            # by the object's function properties.
            mo = re.fullmatch(r'Properties of the (\w+) Prototype Object', section.section_title)
            which = mo.group(1)
            op_name = f"this{'Time' if which == 'Date' else which}Value"

            preamble = section.block_children[emu_alg_posn-1]
            assert preamble.source_text() == f'<p>The abstract operation <dfn id="{op_name.lower()}" aoid="{op_name}" oldids="sec-{op_name.lower()}">{op_name}</dfn> takes argument _value_. It performs the following steps when called:</p>'

            handle_solo_op(op_name, emu_alg, section)

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
                ensure_alg('shorthand', 'Completion')
            elif section.section_title in [
                'ReturnIfAbrupt',
                'Await',
                'NormalCompletion',
                'ThrowCompletion',
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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_solo_op(op_name, emu_alg, section):
    # "solo" in the sense of having a single definition,
    # in contrast to multiple definitions discriminated by type or syntax

    alg_add_defn('op: solo', op_name, None, emu_alg, section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_tabular_op_defn(op_name, tda, tdb, section):
    assert tda.element_name == 'td'
    assert tdb.element_name == 'td'

    at = tda.inner_source_text().strip()
    bt = tdb.inner_source_text().strip()

    discriminator = at

    x = ' '.join(c.element_name for c in tdb.children)

    if x in [
        '#LITERAL',
        '#LITERAL emu-xref #LITERAL',
        '#LITERAL sub #LITERAL',
        '#LITERAL sub #LITERAL sub #LITERAL',
    ]:
        alg_add_defn('op: solo', op_name, discriminator, tdb, section)

    elif x == '#LITERAL emu-note #LITERAL':
        # ToBoolean: row for 'Object' has a NOTE re [[IsHTMLDDA]]
        alg_add_defn('op: solo', op_name, discriminator, tdb, section)

    elif x == '#LITERAL p #LITERAL p #LITERAL':
        (_, p1, _, p2, _) = tdb.children
        alg_add_defn('op: solo', op_name, discriminator, tdb, section)
        pass

    elif x == '#LITERAL p #LITERAL emu-alg #LITERAL':
        (_, p, _, emu_alg, _) = tdb.children
        assert p.source_text() == '<p>Apply the following steps:</p>'
        alg_add_defn('op: solo', op_name, discriminator, emu_alg, section)

    else:
        assert 0, x

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_type_discriminated_op(op_name, op_species, discriminator, emu_alg, section):
    alg_add_defn(op_species, op_name, discriminator, emu_alg, section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_early_error(emu_grammar, ul, section):
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
            alg_add_defn('op: early error', 'Early Errors', emu_grammar, ee_rule, section)
        else:
            assert 0, li.element_name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

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

    alg_add_defn('op: syntax-directed', sdo_name, emu_grammar, code_hnode, section)

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

def handle_inline_sdo(li, section_sdo_name, section):
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
        elif cl in ['{NAMED_OPERATION_INVOCATION}', '{h_sub_fancy_f}']:
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
            alg_add_defn('op: syntax-directed', rule_sdo_name, rule_grammar, rule_expr, section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

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

    tree = parse(emu_eqn)
    if tree is None: return

    assert tree.prod.lhs_s == '{EMU_EQN_DEF}'
    [child] = tree.children
    if child.prod.lhs_s == '{CONSTANT_DEF}':
        [constant_name, dec_int_lit] = child.children[0:2]
        assert constant_name.source_text() == aoid
        # XXX alg_add_defn('constant', aoid, None, dec_int_lit, section)
    elif child.prod.lhs_s == '{OPERATION_DEF}':
        [op_name, parameter, body] = child.children
        assert op_name.source_text() == aoid
        parameter_name = parameter.source_text()
        alg_add_defn('op: solo', aoid, None, body, section)
    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def handle_function(bif_species, locater, emu_alg, section):

    alg_add_defn(bif_species, locater, None, emu_alg, section)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def connect_anodes_to_hnodes(base_hnode, base_anode):

    pairs = [
        ('emu-grammar', '{h_emu_grammar}'),
        ('emu-alg',     '{h_emu_alg}'    ),
        ('figure',      '{h_figure}'     ),
        ('a',           '{h_a}'          ),
        ('pre',         '{h_pre_code}'   ),
        # ('emu-xref',    '{h_emu_xref}'   ),
    ]

    # We could include <emu-xref> and {h_emu_xref}, but
    # - I don't think it'll be useful, and
    # - there are cases
    #       FunctionDeclarationInstantiation ( _func_, _argumentsList_ )
    #       Runtime Semantics: GlobalDeclarationInstantiation ( _script_, _env_ )
    #       Runtime Semantics: EvalDeclarationInstantiation ( _body_, _varEnv_, _lexEnv_, _strict_ )
    #       NewPromiseCapability ( _C_ )
    #   where an <emu-xref> appears in a NOTE-step
    #   (base_hnode.element_name == 'emu-alg' and re.search('NOTE: .+ <emu-xref ', base_hnode.source_text())):
    #   it'll show up as a connectable hnode, but not as a connectable anode.

    # ------------------------

    connectable_hnode_names = [ hnode_name for (hnode_name, _) in pairs ]
    connectable_hnodes = [
        child
        for child in base_hnode.children
        if child.element_name in connectable_hnode_names
    ]

    if base_hnode.element_name == 'li' and re.search('(?s)<p>.*<emu-grammar>', base_hnode.source_text()):
        assert connectable_hnodes == []
        (_, p, _) = base_hnode.children
        assert p.element_name == 'p'
        connectable_hnodes = [
            child
            for child in p.children
            if child.element_name in connectable_hnode_names
        ]

    # ------------------------

    connectable_anode_names = [ anode_name for (_, anode_name) in pairs ]
    connectable_anodes = [
        anode
        for anode in base_anode.each_descendant()
        if anode.prod.lhs_s in connectable_anode_names
    ]

    # ------------------------

    assert len(connectable_anodes) == len(connectable_hnodes)

    for (c_hnode, c_anode) in zip(connectable_hnodes, connectable_anodes):
        assert (c_hnode.element_name, c_anode.prod.lhs_s) in pairs
        c_anode._hnode = c_hnode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def annotate_invocations(anode):

    # For each node in `anode` that is an invocation of an operation,
    # annotate it with info about the invocation.
    for d in anode.each_descendant_or_self():
        op_names = None

        if d.prod.lhs_s == '{NAMED_OPERATION_INVOCATION}':
            rhs = d.prod.rhs_s

            if rhs == '{PREFIX_PAREN}':
                # Handled below, when '{PREFIX_PAREN}' is the lhs.
                pass

            elif rhs in [
                'the {ISDO_NAME} of {PROD_REF}',
                '{ISDO_NAME} of {PROD_REF}',
            ]:
                isdo_name = d.children[0]
                assert isdo_name.prod.rhs_s == '{cap_word}'
                op_names = [isdo_name.source_text()]
                args = [d.children[1]]

            elif rhs in [
                'the {cap_word} of {LOCAL_REF}',
                'the {cap_word} of {LOCAL_REF} (see {h_emu_xref})',
                'the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}',
                'the {cap_word} of {LOCAL_REF} {WITH_ARGS}',
                'the {cap_word} of {LOCAL_REF}; if {LOCAL_REF} is not present, use the numeric value zero',
                '{cap_word} for {LOCAL_REF} {WITH_ARGS}',
                '{cap_word} of {LOCAL_REF}',
                '{cap_word} of {LOCAL_REF} {WITH_ARGS}',
                '{cap_word}({PROD_REF})',
                '{cap_word}({var})',
                '{cap_word}({named_char})',
                'the result of performing {cap_word} on {EX}',
            ]:
                cap_word = d.children[0]
                op_names = [cap_word.source_text()]
                args = [d.children[1]]
                if '{WITH_ARGS}' in rhs:
                    with_args = d.children[2]
                    assert with_args.prod.lhs_s == '{WITH_ARGS}'
                    if '{PASSING}' in with_args.prod.rhs_s:
                        args.extend(with_args.children[1:])
                    else:
                        args.extend(with_args.children)

            elif rhs == 'evaluating {LOCAL_REF}':
                # 'Evaluation' or 'regexp-Evaluate',
                # depending on the argument.
                [local_ref] = d.children
                if local_ref.source_text() in [
                    '|Assertion|',
                    '|NonemptyClassRanges|',
                    '|ClassAtom|',
                    '|ClassAtomNoDash|',
                    '|ClassEscape|',
                    '|CharacterClassEscape|',
                ]:
                    # A better criterion would be the containing clause
                    op_names = ['regexp-Evaluate']
                else:
                    op_names = ['Evaluation']
                args = d.children

            elif rhs == 'the abstract operation named by {DOTTING} using the elements of {DOTTING} as its arguments':
                op_names = [ 'ScriptEvaluationJob', 'TopLevelModuleEvaluationJob']
                args = [d.children[1]] # XXX

            else:
                callee_name = {
                    'Abstract Equality Comparison {var} == {var}'      : 'Abstract Equality Comparison',
                    'Abstract Relational Comparison {var} &lt; {var} with {var} equal to {LITERAL}' :  'Abstract Relational Comparison',
                    'Abstract Relational Comparison {var} &lt; {var}'  : 'Abstract Relational Comparison',
                    'Strict Equality Comparison {var} === {EX}'        : 'Strict Equality Comparison',
                    'evaluating {LOCAL_REF} with argument {var}'       : 'regexp-Evaluate',
                    'evaluating {LOCAL_REF}. This may be of type Reference' : 'Evaluation',
                    'evaluating {nonterminal} {var}'                   : 'Evaluation',
                    "the Abstract Closure that evaluates the above parse by applying the semantics provided in {h_emu_xref} using {var} as the pattern's List of {nonterminal} values and {var} as the flag parameters": 'regexp-Evaluate',
                    "the Abstract Closure that evaluates {var} by applying the semantics provided in {h_emu_xref} using {var} as the pattern's List of {nonterminal} values and {var} as the flag parameters": 'regexp-Evaluate',
                    "the CharSet returned by {PROD_REF}"               : 'regexp-Evaluate',
                    "the CharSet returned by {h_emu_grammar} "         : 'regexp-Evaluate',
                    '{LOCAL_REF} Contains {nonterminal}'               : 'Contains',
                    '{LOCAL_REF} Contains {var}'                       : 'Contains',
                }[rhs]
                op_names = [callee_name]
                args = d.children # XXX incorrect for a few cases

        elif d.prod.lhs_s == '{PREFIX_PAREN}':
            [opn_before_paren, arg_list] = d.children[0:2]
            assert opn_before_paren.prod.lhs_s == '{OPN_BEFORE_PAREN}'

            if opn_before_paren.prod.rhs_s == '{SIMPLE_OPERATION_NAME}':
                op_names = [opn_before_paren.source_text()]
            elif opn_before_paren.prod.rhs_s == '{DOTTING}':
                [dotting] = opn_before_paren.children
                [lhs, dsbn] = dotting.children
                op_name = dsbn.source_text()
                # Usually, we are invoking an object's internal method.
                # But the memory model has 2 record-fields that are invocable
                # but not actually defined. (It's just weird.)
                # It's simpler if we skip those cases.
                if op_name in ['[[ModifyOp]]', '[[ReadsBytesFrom]]']:
                    op_names = []
                else:
                    op_names = [op_name]
            elif opn_before_paren.prod.rhs_s == '{var}.{cap_word}':
                [var, cap_word] = opn_before_paren.children
                op_names = [cap_word.source_text()]
            elif opn_before_paren.prod.rhs_s == '{var}':
                # can't do much
                if opn_before_paren.source_text() == '_convOp_':
                    # Should extract this from "The TypedArray Constructors" table
                    op_names = [
                        'ToInt8',
                        'ToUint8',
                        'ToUint8Clamp',
                        'ToInt16',
                        'ToUint16',
                        'ToInt32',
                        'ToUint32',
                        'ToBigInt64',
                        'ToBigUint64',
                    ]
                elif opn_before_paren.source_text() == '_operation_':
                    assert d.source_text() == '_operation_(_lnum_, _rnum_)'
                    # ApplyStringOrNumericBinaryOperator
                    op_names = [
                        '::exponentiate',
                        '::multiply',
                        '::divide',
                        '::remainder',
                        '::add',
                        '::subtract',
                        '::leftShift',
                        '::signedRightShift',
                        '::unsignedRightShift',
                        '::bitwiseAND',
                        '::bitwiseXOR',
                        '::bitwiseOR',
                    ]
                else:
                    # mostly closures created+invoked in RegExp semantics
                    # print('>>>', opn_before_paren.source_text())
                    pass
            elif opn_before_paren.prod.rhs_s == '{NUMERIC_TYPE_INDICATOR}::{low_word}':
                [_, low_word] = opn_before_paren.children
                op_names = ['::' + low_word.source_text()]
            else:
                assert 0, opn_before_paren.prod.rhs_s

            if arg_list.prod.lhs_s == '{EXLIST_OPT}':
                args = exes_in_exlist_opt(arg_list)
            elif arg_list.prod.lhs_s == '{EXPR}':
                args = [arg_list]
            else:
                assert 0, arg_list.prod.lhs_s

        elif str(d.prod) == '{CONDITION_1} : {var} and {var} are in a race in {var}':
            op_names = ['Races']
            args = [] # XXX

        elif str(d.prod) == '{COMMAND} : Set fields of {var} with the values listed in {h_emu_xref}. {the_field_names_are_the_names_listed_etc}':
            op_names = [ 'CreateBuiltinFunction', 'initializer for @@unscopables']
            args = [] # XXX

        elif str(d.prod) == '{COMMAND} : IfAbruptRejectPromise({var}, {var}).':
            op_names = ['IfAbruptRejectPromise']
            args = d.children[0:2]

        elif str(d.prod) in [
            '{COMMAND} : ReturnIfAbrupt({EX}).',
            '{SMALL_COMMAND} : ReturnIfAbrupt({var})',
        ]:
            op_names = ['ReturnIfAbrupt']
            args = [d.children[0]]

        elif d.prod.lhs_s == '{COMMAND}' and d.prod.rhs_s.startswith('Evaluate {PROD_REF}'):
            op_names = ['regexp-Evaluate']
            args = [d.children[0]]
            if d.prod.rhs_s.startswith('Evaluate {PROD_REF} with'):
                args.append(d.children[1])

        if op_names is not None:
            d._op_invocation = (op_names, args)

def exes_in_exlist_opt(exlist_opt):
    assert exlist_opt.prod.lhs_s == '{EXLIST_OPT}'
    if exlist_opt.prod.rhs_s == '{EPSILON}':
        return []
    elif exlist_opt.prod.rhs_s == '{EXLIST}':
        [exlist] = exlist_opt.children
        return exes_in_exlist(exlist)
    elif exlist_opt.prod.rhs_s == '{var}':
        return [exlist_opt.children[0]]
    else:
        assert 0, exlist_opt.prod.rhs_s

def exes_in_exlist(exlist):
    exes = []
    while True:
        assert exlist.prod.lhs_s == '{EXLIST}'
        if exlist.prod.rhs_s == '{EX}':
            [ex] = exlist.children
            exes.insert(0, ex)
            break
        elif exlist.prod.rhs_s == '{EXLIST}, {EX}':
            [inner_exlist, ex] = exlist.children
            exes.insert(0, ex)
            exlist = inner_exlist
        else:
            assert 0
    return exes

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

spec.alg_info_ = { 'bif': {}, 'op': {} }
# These need to be separate because Set() is both
# an abstract operation and a built-in function.

class Alg:
    # An operation (widely construed) or
    # the algorithmic aspect of a (built-in) function.
    def __init__(self, name, bif_or_op, species):
        self.name = name
        self.bif_or_op = bif_or_op
        self.species = species
        self.definitions = []
        self.invocations = []
        self.callees = set()
        self.callers = set()
        self.headers = []

    def __str__(self):
        return f"{self.bif_or_op}: {self.name}"

    def __lt__(self, other):
        return (
            self.bif_or_op < other.bif_or_op
            or
            self.bif_or_op == other.bif_or_op
            and
            self.name < other.name
        )

def ensure_alg(alg_species, alg_name):
    bif_or_op = 'bif' if alg_species.startswith('bif:') else 'op'
    iffn = spec.alg_info_[bif_or_op]

    if alg_name in iffn:
        alg_info = iffn[alg_name]
        assert alg_info.name == alg_name
        assert alg_info.species == alg_species
    else:
        alg_info = Alg(alg_name, bif_or_op, alg_species)
        iffn[alg_name] = alg_info

    return alg_info

# ------------------------------------------------

def alg_add_defn(alg_species, alg_name, discriminator, hnode_or_anode, section):
    assert type(alg_name) == str

    alg_info = ensure_alg(alg_species, alg_name)

    if hnode_or_anode is None:
        assert discriminator is None
        return

    AlgDefn(alg_info, discriminator, hnode_or_anode, section)

class AlgDefn:
    def __init__(self, alg_info, discriminator, hnode_or_anode, section):
        self.the_alg_to_which_this_belongs = alg_info
        self.discriminator = discriminator
        self.section = section
        self.header = None

        assert (
            discriminator is None
            or
            isinstance(discriminator, HNode) and discriminator.element_name == 'emu-grammar'
            or
            isinstance(discriminator, str) # type name
        )

        if isinstance(hnode_or_anode, HNode):
            hnode = hnode_or_anode
            assert hnode.element_name in ['emu-alg', 'td']
            self.anode = parse(hnode)
            if self.anode is None: return
            assert not hasattr(hnode, '_parent_algdefn')
            hnode._parent_algdefn = self

        elif isinstance(hnode_or_anode, ANode):
            self.anode = hnode_or_anode

        else:
            assert 0

        assert self.anode.prod.lhs_s in [
            '{EXPR}',
            '{NAMED_OPERATION_INVOCATION}',
            '{EMU_ALG_BODY}',
            '{EE_RULE}',
            '{RHSS}',
            '{ONE_LINE_ALG}',
        ]

        alg_info.definitions.append(self)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def analyze_static_dependencies():

    f_deps = shared.open_for_output('static_deps')
    def put(*args):
        print(*args, file=f_deps)

    def put_names(header, names):
        put()
        put(header + ':')
        if names:
            for name in sorted(names):
                put(f"    {name}")
        else:
            put("    (none)")

    # ----------------------------------------------------

    # Find and print all the static dependencies:

    for (alg_name, alg_info) in (
        sorted(spec.alg_info_['op'].items())
        +
        sorted(spec.alg_info_['bif'].items())
    ):
        for alg_defn in alg_info.definitions:
            alg_defn.callees = set()

            def recurse(anode):
                for d in anode.each_descendant_or_self():
                    if hasattr(d, '_op_invocation'):
                        (callee_names, args) = d._op_invocation
                        for callee_name in callee_names:
                            alg_defn.callees.add(callee_name)
                            if callee_name in spec.alg_info_['op']:
                                spec.alg_info_['op'][callee_name].invocations.append(d)
                            else:
                                stderr(f"spec.alg_info_['op'] has no entry for {callee_name!r} ({alg_name} calls it in {alg_defn.section.section_num})")
                    elif hasattr(d, '_hnode') and hasattr(d._hnode, '_syntax_tree'):
                        assert alg_name == 'Early Errors'
                        # "... and the following algorithm evaluates to *true*: ..."
                        recurse(d._hnode._syntax_tree)

            recurse(alg_defn.anode)
            alg_info.callees.update(alg_defn.callees)

        put()
        put(alg_name)
        put(f"[{alg_info.species}, {len(alg_info.definitions)} definitions]")
        for callee in sorted(alg_info.callees):
            put('  ', callee)

        for callee_name in alg_info.callees:
            if callee_name in spec.alg_info_['op']:
                spec.alg_info_['op'][callee_name].callers.add(alg_name)
            else:
                stderr(f"spec.alg_info_['op'] has no entry for {callee_name!r} ({alg_name} calls it)")

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
        if op_name not in spec.alg_info_['op']:
            op_names_with_no_info.add(op_name)
            return
        op_info = spec.alg_info_['op'][op_name]
        if hasattr(op_info, '_reached'): return
        op_info._reached = True
        for callee_name in sorted(list(op_info.callees)):
            reach_op(callee_name, level+1)

    reach_op('Early Errors', 0)
    if True: # PR #1597 has been merged
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

    for (bif_name, bif_info) in sorted(spec.alg_info_['bif'].items()):
        # put(bif_name)
        for callee in sorted(bif_info.callees):
            reach_op(callee, 1)

    # --------------

    # Print out dependency anomalies.

    put()
    put('X' * 40)

    put_names(
        'operations referenced but not declared',
        op_names_with_no_info
    )

    put()
    put('operations declared but not reached:')
    for (op_name, op_info) in sorted(spec.alg_info_['op'].items()):
        if not hasattr(op_info, '_reached'):
            put(f"    {op_name}")

    # ===================================================================

    # Static Semantics

    put()
    put('X' * 40)

    op_names_labelled_ss = set()
    op_names_labelled_rs = set()
    op_names_not_labelled = set()
    for section in spec.root_section.each_descendant_that_is_a_section():
        if 'op_name' not in section.ste: continue
        op_name = section.ste['op_name']

        if section.section_title.startswith('Static Semantics:'):
            if op_name == 'TV and TRV':
                op_names_labelled_ss.add('TV')
                op_names_labelled_ss.add('TRV')
            else:
                op_names_labelled_ss.add(op_name)

        elif section.section_title in ['Statement Rules', 'Expression Rules']:
            assert op_name == 'HasCallInTailPosition'
            # Without this special case, the code would add 'HasCallInTailPosition'
            # to op_names_not_labelled, but that doesn't really make sense,
            # because it's labelled by the parent section:
            assert op_name in op_names_labelled_ss

        elif section.section_title.startswith('Runtime Semantics:'):
            op_name = section.ste['op_name']
            op_names_labelled_rs.add(op_name)

        else:
            op_names_not_labelled.add(op_name)

    ss_and_rs = op_names_labelled_ss & op_names_labelled_rs
    ss_and_un = op_names_labelled_ss & op_names_not_labelled
    rs_and_un = op_names_labelled_rs & op_names_not_labelled

    put_names(
        "ops labelled both 'Static Semantics' and 'Runtime Semantics'",
        ss_and_rs
    )

    put_names(
        "ops labelled 'Static Semantics' and also unlabelled",
        ss_and_un
    )

    put_names(
        "ops labelled 'Runtime Semantics' and also unlabelled",
        rs_and_un
    )

    # ------

    put()
    put('-' * 40)

    if 1:
        op_names_reached_from_ss_starting_points = set()

        def ss_reach_op(op_name, level):
            if op_name in op_names_with_no_info:
                # No point in continuing.
                return
            if op_name in op_names_reached_from_ss_starting_points:
                return
            op_names_reached_from_ss_starting_points.add(op_name)
            op_info = spec.alg_info_['op'][op_name]
            for callee_name in sorted(list(op_info.callees)):
                if op_name == 'ToString' and callee_name in ['ToPrimitive', 'ToString']:
                    # These calls only happen for an Object argument,
                    # which we'll assume doesn't occur during Static Semantics.
                    # (ToPrimitive leads to lots of Runtime stuff.)
                    continue

                # put(f"{'  '*level}{level}. {op_name} -> {callee_name}")
                ss_reach_op(callee_name, level+1)

        ss_reach_op('Early Errors', 0)
        ss_reach_op('ParseScript', 0)
        ss_reach_op('ParseModule', 0)
        # ParseModule is unlabelled, suggesting that it's 'Runtime Semantics'
        # (see https://github.com/tc39/ecma262/pull/1664#issuecomment-522620263 and allemwb's reply)
        # but if you treat it as such, you get more anomalies.
        # (And presumably, parsing a module should be Static.)
        # Ditto ParseScript, except that treating it as Runtime doesn't create more anomalies.

        # ----

        put_names(
            "ops labelled 'Static Semantics' but not reachable from SS starting points [probably okay]",
            op_names_labelled_ss - op_names_reached_from_ss_starting_points
        )
        # The idea of "SS starting points" is probably not worth much.

        put_names(
            "ops reachable from SS starting points but not labelled 'Static Semantics' [shouldn't happen?]",
            op_names_reached_from_ss_starting_points - op_names_labelled_ss
        )
        # These should probably be labelled "Static Semantics"?

    # ------

    put()
    put('-' * 40)

    ss_calls_non = []
    non_calls_ss = []

    for (op_name, op_info) in sorted(spec.alg_info_['op'].items()):
        caller_is_ss = op_name in op_names_labelled_ss
        for callee_name in sorted(op_info.callees):
            callee_is_ss = callee_name in op_names_labelled_ss
            if caller_is_ss and not callee_is_ss:
                ss_calls_non.append((op_name, callee_name))
            elif not caller_is_ss and callee_is_ss:
                non_calls_ss.append((op_name, callee_name))
    
    put()
    put("op labelled 'Static Semantics' calls one that isn't [shouldn't happen?]:")
    for (caller, callee) in ss_calls_non:
        put(f"    {caller} -> {callee}")

    put()
    put("op not labelled 'Static Semantics' calls one that is [probably fine]:")
    for (caller, callee) in non_calls_ss:
        put(f"    {caller} -> {callee}")

    # ===================================================================

    # "runtimey" ops
    # (Does non-runtimey-ness approximate Static Semantics?
    # Doesn't seem so.)

    def looks_runtimey(anode):
        return (
            any(
                phrase in anode.prod.rhs_s
                for phrase in [
                    'execution context',
                    '{EXECUTION_CONTEXT_COMPONENT}',

                    'a newly created object',
                    'a new built-in function object',
                    'an ECMAScript function object',
                    'an Iterator object',
                    'internal slot',
                    'own property',
                    'the property named',

                    'Data Block',
                    'Environment Record',
                    'Realm Record',
                    'the thisValue component',
                    'Throw a',
                ]
            )
            or
            any(
                phrase in anode.source_text()
                for phrase in [
                    '[[Prototype]]',
                    '[[Extensible]]',
                ]
            )
        )

    # First, find the ops that directly look runtimey.
    ops_that_look_runtimey = set()
    for (op_name, op_info) in sorted(spec.alg_info_['op'].items()):
        for op_defn in op_info.definitions:
            def recurse(anode):
                for d in anode.each_descendant_or_self():
                    if looks_runtimey(d):
                        ops_that_look_runtimey.add(op_name)
                        break
                    if hasattr(d, '_hnode') and hasattr(d._hnode, '_syntax_tree'):
                        assert op_name == 'Early Errors'
                        recurse(d._hnode._syntax_tree)
            recurse(op_defn.anode)

    # Then propagate to callers.
    while True:
        next_ops_that_look_runtimey = ops_that_look_runtimey.copy()
        for op_name in ops_that_look_runtimey:
            op_info = spec.alg_info_['op'][op_name]
            for caller in op_info.callers:
                if caller in spec.alg_info_['op']:
                    next_ops_that_look_runtimey.add(caller)
        if next_ops_that_look_runtimey == ops_that_look_runtimey:
            # fixed point
            break
        ops_that_look_runtimey = next_ops_that_look_runtimey

    ops_that_dont_look_runtimey = (
        set(spec.alg_info_['op'].keys())
        -
        ops_that_look_runtimey
    )

    put()
    put('-' * 40)

    put_names(
        "ops labelled 'Static Semantics' but that look runtimey [shouldn't happen?]",
        op_names_labelled_ss - ops_that_dont_look_runtimey
    )

    put_names(
        "ops that don't look runtimey, but aren't labelled 'Static Semantics' [okay, but should be relabelled?]",
        ops_that_dont_look_runtimey - op_names_labelled_ss
    )

    # ===================================================================

    f_deps.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

ops_with_implicit_defns = ['Contains', 'AllPrivateIdentifiersValid', 'ContainsArguments']

def check_sdo_coverage():
    stderr('check_sdo_coverage...')
    spec.sdo_coverage_map = {}

    # collect sdo_coverage_info:
    for (op_name, op_info) in spec.alg_info_['op'].items():
        if op_info.species in ['op: syntax-directed', 'op: early error']:

            assert op_name not in spec.sdo_coverage_map
            spec.sdo_coverage_map[op_name] = {}

            for alg_defn in op_info.definitions:
                # XXX Exclude Annex B definitions from sdo_coverage analysis:
                if alg_defn.section.section_num.startswith('B'): continue

                discriminator = alg_defn.discriminator

                if discriminator is None:
                    assert op_name in ops_with_implicit_defns
                    puk = ('*default*', '', '')
                    puk_set = set([puk])
                else:
                    puk_set = discriminator.puk_set
                    if not puk_set:
                        stderr(f"! sdo_coverage may be broken because no puk_set for {discriminator.source_text()}")

                for puk in puk_set:
                    if puk not in spec.sdo_coverage_map[op_name]:
                        spec.sdo_coverage_map[op_name][puk] = []
                    spec.sdo_coverage_map[op_name][puk].append(alg_defn)

    analyze_sdo_coverage_info()

# ------------------------------------------------------------------------------

def analyze_sdo_coverage_info():
    coverage_f = shared.open_for_output('sdo_coverage')
    def put(*args): print(*args, file=coverage_f)

    # -------------

    sdos_defined_for_key_ = defaultdict(set)
    for (sdo_name, coverage_info_for_this_sdo) in sorted(spec.sdo_coverage_map.items()):
        for key in coverage_info_for_this_sdo.keys():
            sdos_defined_for_key_[key].add(sdo_name)
    max_n_sdos = max(
        len(sdo_names)
        for (_, sdo_names) in sdos_defined_for_key_.items()
    )
    put(f"max number of SDOs defined for a given key: {max_n_sdos}")
    put("e.g.:")
    for (key, sdo_names) in sorted(sdos_defined_for_key_.items()):
        if len(sdo_names) == max_n_sdos:
            put(f"    {key} has definitions for:")
            for sdo_name in sorted(sdo_names):
                put(f"        {sdo_name}")
    put()

    # -------------

    for (sdo_name, coverage_info_for_this_sdo) in sorted(spec.sdo_coverage_map.items()):

        if sdo_name in ops_with_implicit_defns:
            # XXX can we do anything useful here?
            # we could check for conflicting defs
            continue

        if sdo_name == 'Early Errors':
            # Early Error rules are not invoked explicitly (for the most part).
            continue

        # print()
        # print(sdo_name)

        if 0:
            # old scheme:
            # We look at the productions that the SDO is defined on,
            # and ensure that the coverage of the LHS non-terminals is complete.
            # But that doesn't catch places where the SDO *should* be defined
            # on a nonterminal but isn't at all.
            # (E.g. ContainsUseStrict on AsyncConciseBody, see PR #1745.)

            nt_queue = sorted(coverage_info_for_this_sdo.keys())

        else:

            # Look at the SDO's invocations.
            # For each invocation, figure out the nonterminal
            # of the parse node that is the 'target'? (primary argument) of the invocation.
            # Make sure those nonterminals are covered.

            nt_set = set()
            for opcall in spec.alg_info_['op'][sdo_name].invocations:
                # opcall.printTree()
                (callee_names, args) = opcall._op_invocation
                assert sdo_name in callee_names
                assert args
                primary = args[0]
                uprimary = descend_via_unit_derivations(primary)
                u_st = uprimary.source_text()
                u_lhs = uprimary.prod.lhs_s
                nts = None

                if u_lhs == '{nonterminal}':
                    nt = u_st[1:-1]
                    nts = [nt]

                    if nt == 'Statement':
                        opcall_st = opcall.source_text()
                        if opcall_st == 'LabelledEvaluation of |Statement| with argument _labelSet_':
                            # 1. If |Statement| is either a |LabelledStatement| or a |BreakableStatement|, then
                            #   1. Return LabelledEvaluation of |Statement| with argument _labelSet_.
                            nts = ['LabelledStatement', 'BreakableStatement']
                        elif opcall_st == 'TopLevelVarDeclaredNames of |Statement|':
                            # 1. If |Statement| is <emu-grammar>Statement : LabelledStatement</emu-grammar> ,
                            #    return TopLevelVarDeclaredNames of |Statement|.
                            nts = ['LabelledStatement']
                        elif opcall_st == 'TopLevelVarScopedDeclarations of |Statement|':
                            # 1. If |Statement| is <emu-grammar>Statement : LabelledStatement</emu-grammar> ,
                            #    return TopLevelVarScopedDeclarations of |Statement|.
                            nts = ['LabelledStatement']

                elif u_lhs == '{PROD_REF}':
                    u_rhs = uprimary.prod.rhs_s
                    if u_rhs in [
                        'this {nonterminal}',
                        'the {nonterminal} contained in {PROD_REF}',
                        'the {nonterminal} containing this {nonterminal}',
                        'the {nonterminal} of {PROD_REF}',
                        'the {nonterminal} that is that single code point',
                        'the {nonterminal} that is that {nonterminal}',
                        'the corresponding {nonterminal}',
                    ]:
                        nonterminal = uprimary.children[0]
                    elif u_rhs == 'the {ORDINAL} {nonterminal}':
                        nonterminal = uprimary.children[1]
                    else:
                        assert 0, u_rhs
                    nts = [nonterminal.source_text()[1:-1]]

                elif u_lhs == '{LOCAL_REF}':
                    u_rhs = uprimary.prod.rhs_s
                    # print('>>', u_rhs, '###', u_st, file=sys.stderr)
                    if u_rhs == 'the {nonterminal} of {var}':
                        nonterminal = uprimary.children[0]
                        nts = [nonterminal.source_text()[1:-1]]
                    elif u_st == 'the parsed code that is _F_.[[ECMAScriptCode]]':
                        nts = all_possibilities_for_func_ECMAScriptCode
                    else:
                        assert 0

                elif u_lhs in ['{var}', '{DOTTING}']:
                    # {var} or {DOTTING} results in a Parse Node.
                    # What *kind* of Parse Node should properly be determined via static type analysis.
                    nts = nts_behind_var_in_sdo_call.get((sdo_name, u_st), [])
                    if nts == []:
                        put(f"nts_etc missing entry for ({sdo_name!r}, {u_st!r})")

                elif u_lhs == '{h_emu_grammar}':
                    # "the CharSet returned by <emu-grammar>CharacterClassEscape :: ...</emu-grammar>"
                    assert u_st.startswith('<emu-grammar>CharacterClassEscape :: ')
                    nts = ['CharacterClassEscape']

                else:
                    assert 0, (u_lhs, opcall.source_text())

                if nts:
                    for nt in nts:
                        nt_set.add(nt)
                        # print(f" ++ {nt:36} from {opcall.source_text()}")
                else:
                    pass
                    # print(f" ?? {' ':36} from {opcall.source_text()}")

            nt_queue = sorted(nt_set)

        # for nt in nt_queue: print('   ', nt)

        def queue_ensure(nt):
            if nt not in nt_queue: nt_queue.append(nt)

        used_keys = set()

        debug = False # (sdo_name == 'HasName')
        # {debug} creates a lot of output, but it's really useful
        # when you're trying to figure out why "needs a rule" messages appear.

        for lhs_nt in nt_queue:
            # print('    ', lhs_nt)

            nt_info = emu_grammars.info_for_nt_[lhs_nt]
            # assert 'A' in nt_info.def_occs
            if 'A' not in nt_info.def_occs: continue
            d_production_n = nt_info.def_occs['A']

            for def_rhs_n in d_production_n._rhss:
                GNTs = [r for r in def_rhs_n._rhs_items if r.kind in ['GNT', 'NT_BUT_NOT']]
                oGNTs = [gnt for gnt in GNTs if gnt._is_optional]
                nGNTs = [gnt for gnt in GNTs if not gnt._is_optional]

                reduced_prod_string = f"{lhs_nt} -> {def_rhs_n._reduced}"

                for opt_combo in each_opt_combo(oGNTs):
                    opt_combo_str = ''.join(omreq[0] for (nt, omreq) in opt_combo)
                    optbits = ''.join(
                        {
                            'omitted': '0',
                            'required': '1'
                        } [optionality]
                        for (_, optionality) in opt_combo
                    )

                    puk = (lhs_nt, def_rhs_n._reduced, optbits)
                    used_keys.add(puk)
                    rules = coverage_info_for_this_sdo.get(puk, [])

                    if len(rules) == 1:
                        # great
                        if debug:
                            put(f"{sdo_name} for {reduced_prod_string} has an explicit rule")
                        pass
                    elif len(rules) > 1:
                        put(f"{sdo_name} for {reduced_prod_string} {opt_combo_str} is handled by {len(rules)} rules!")
                    elif is_sdo_coverage_exception(sdo_name, lhs_nt, def_rhs_n._reduced):
                        # okay
                        if debug:
                            put(f"{sdo_name} for {reduced_prod_string} is a coverage exception")
                        pass
                    else:
                        nts = [gnt._nt_name for gnt in nGNTs] + required_nts_in(opt_combo)
                        if len(nts) == 1:
                            # The rule for chain productions applies.
                            # So recurse on the rhs non-terminal.
                            [nt] = nts

                            if debug:
                                put(f"{sdo_name} for {reduced_prod_string} chains to {nt}")

                            queue_ensure(nt)
                        else:
                            put(f"{sdo_name} for {reduced_prod_string} {opt_combo_str} needs a rule")

        unused_keys = coverage_info_for_this_sdo.keys() - used_keys
        for unused_key in sorted(unused_keys):
            put(f"{sdo_name} has unused rule for: {unused_key}")

    coverage_f.close()

# -------------------------------

def each_opt_combo(oGNTs):
    N = len(oGNTs)
    if N == 0:
        yield []
    elif N == 1:
        [a] = oGNTs
        yield [(a._nt_name, 'omitted' )]
        yield [(a._nt_name, 'required')]
    elif N == 2:
        [a, b] = oGNTs
        yield [(a._nt_name, 'omitted' ), (b._nt_name, 'omitted' )]
        yield [(a._nt_name, 'omitted' ), (b._nt_name, 'required')]
        yield [(a._nt_name, 'required'), (b._nt_name, 'omitted' )]
        yield [(a._nt_name, 'required'), (b._nt_name, 'required')]
    elif N == 3:
        [a, b, c] = oGNTs
        yield [(a._nt_name, 'omitted' ), (b._nt_name, 'omitted' ), (c._nt_name, 'omitted' )]
        yield [(a._nt_name, 'omitted' ), (b._nt_name, 'omitted' ), (c._nt_name, 'required')]
        yield [(a._nt_name, 'omitted' ), (b._nt_name, 'required'), (c._nt_name, 'omitted' )]
        yield [(a._nt_name, 'omitted' ), (b._nt_name, 'required'), (c._nt_name, 'required')]
        yield [(a._nt_name, 'required'), (b._nt_name, 'omitted' ), (c._nt_name, 'omitted' )]
        yield [(a._nt_name, 'required'), (b._nt_name, 'omitted' ), (c._nt_name, 'required')]
        yield [(a._nt_name, 'required'), (b._nt_name, 'required'), (c._nt_name, 'omitted' )]
        yield [(a._nt_name, 'required'), (b._nt_name, 'required'), (c._nt_name, 'required')]
    else:
        assert 0

def required_nts_in(opt_combo):
    return [nt for (nt, omreq) in opt_combo if omreq == 'required']

# a function object's [[ECMAScriptCode]] internal slot

# The ones where FunctionDeclarationInstantiation is called:
FDI_possibilities_for_func_ECMAScriptCode = [
    'FunctionBody',       # FDI called from EvaluateFunctionBody
    'ConciseBody',        # FDI called from EvaluateConciseBody
    'GeneratorBody',      # FDI called from EvaluateGeneratorBody
    'AsyncGeneratorBody', # FDI called from EvaluateAsyncGeneratorBody
    'AsyncFunctionBody',  # FDI called from EvaluateAsyncFunctionBody
    'AsyncConciseBody',   # FDI called from EvaluateAsyncConciseBody
]
all_possibilities_for_func_ECMAScriptCode = FDI_possibilities_for_func_ECMAScriptCode + [
    'Initializer',
]

nts_behind_var_in_sdo_call = {

    # 4529 StringToNumber
    ('StringNumericValue', '_literal_'): ['StringNumericLiteral'],

    # 5715 BoundNames
    ('BoundNames', '_head_'): ['AsyncArrowHead'],
    # 11005 FunctionDeclarationInstantiation
    # 21588 GlobalDeclarationInstantiation
    # 23713 EvalDeclarationInstantiation
    ('BoundNames', '_f_'): [
        'FunctionDeclaration',
        'GeneratorDeclaration',
        'AsyncFunctionDeclaration',
        'AsyncGeneratorDeclaration',
    ],
    # 11005 FunctionDeclarationInstantiation +
    # 17667 BlockDeclarationInstantiation
    # 21588 GlobalDeclarationInstantiation
    # 22788 InitializeEnvironment
    # 23713 EvalDeclarationInstantiation
    ('BoundNames', '_d_'): [
        'FunctionDeclaration',
        'GeneratorDeclaration',
        'AsyncFunctionDeclaration',
        'AsyncGeneratorDeclaration',
        #
        'VariableDeclaration',
        'ForBinding',
        'BindingIdentifier',
        #
        'ClassDeclaration',
        'LexicalDeclaration',
    ],
    # 18548 ForIn/OfBodyEvaluation
    ('BoundNames', '_lhs_'): ['ForDeclaration'],

    # 7333 HasName
    # 7386 IsFunctionDefinition
    # 7522 IsAnonymousFunctionDefinition
    ('IsFunctionDefinition', '_expr_'): [
        'ParenthesizedExpression',
        'Expression',
        'Initializer',
        'AssignmentExpression',
    ],
    # 7333 HasName
    # 7522 IsAnonymousFunctionDefinition
    ('HasName', '_expr_'): [
        'ParenthesizedExpression',
        'Expression',
        'Initializer',
        'AssignmentExpression',
    ],

    # 7574 NamedEvaluation
    ('NamedEvaluation', '_expr_'): ['ParenthesizedExpression'],

    # 7913 IteratorBindingInitialization
    # 11005 FunctionDeclarationInstantiation
    ('IteratorBindingInitialization', '_formals_'): [
        'FormalParameters',
        'ArrowParameters',
        'UniqueFormalParameters',
        'PropertySetParameterList',
        'AsyncArrowBindingIdentifier',
        'ArrowFormalParameters',
    ],
    ('BoundNames',            '_formals_'): [
        'FormalParameters',
        'ArrowParameters',
        'UniqueFormalParameters',
        'PropertySetParameterList',
        'AsyncArrowBindingIdentifier',
        'ArrowFormalParameters',
    ],
    ('IsSimpleParameterList', '_formals_'): [
        'FormalParameters',
        'ArrowParameters',
        'UniqueFormalParameters',
        'PropertySetParameterList',
        'AsyncArrowBindingIdentifier',
        'ArrowFormalParameters',
    ],
    ('ContainsExpression',    '_formals_'): [
        'FormalParameters',
        'ArrowParameters',
        'UniqueFormalParameters',
        'PropertySetParameterList',
        'AsyncArrowBindingIdentifier',
        'ArrowFormalParameters',
    ],

    # 8084 AssignmentTargetType
    ('AssignmentTargetType', '_expr_'): ['ParenthesizedExpression'],

    # 10885 OrdinaryFunctionCreate
    ('ExpectedArgumentCount', '_ParameterList_'): [
        'FormalParameters',
        'ArrowParameters',
        'UniqueFormalParameters',
        'PropertySetParameterList',
        'AsyncArrowBindingIdentifier',
        'ArrowFormalParameters',
    ],
    # 19718 ExpectedArgumentCount
    ('ExpectedArgumentCount', '_formals_'): ['ArrowFormalParameters'],

    # 11005 FunctionDeclarationInstantiation
    # 17667 BlockDeclarationInstantiation
    # 21588 GlobalDeclarationInstantiation
    # 22788 InitializeEnvironment
    # 23713 EvalDeclarationInstantiation
    ('IsConstantDeclaration', '_d_'): [
        'FunctionDeclaration',
        'ClassDeclaration',
        'ExportDeclaration',
        'GeneratorDeclaration',
        'AsyncFunctionDeclaration',
        'AsyncGeneratorDeclaration',
        'LexicalDeclaration',
    ],

    # 11005 FunctionDeclarationInstantiation
    # 21746 GlobalDeclarationInstantiation
    # 23865 EvalDeclarationInstantiation
    ('InstantiateFunctionObject', '_f_'): [
        'FunctionDeclaration',
        'GeneratorDeclaration',
        'AsyncFunctionDeclaration',
        'AsyncGeneratorDeclaration',
    ],
    # 17813 BlockDeclarationInstantiation
    # 22946 InitializeEnvironment
    ('InstantiateFunctionObject', '_d_'): [
        'FunctionDeclaration',
        'GeneratorDeclaration',
        'AsyncFunctionDeclaration',
        'AsyncGeneratorDeclaration',
    ],

    # 11005 FunctionDeclarationInstantiation
    ('VarDeclaredNames', '_code_'): FDI_possibilities_for_func_ECMAScriptCode,
    # 11005 FunctionDeclarationInstantiation
    # 22946 InitializeEnvironment
    ('VarScopedDeclarations', '_code_'  ): FDI_possibilities_for_func_ECMAScriptCode + ['Module'],
    # 11005 FunctionDeclarationInstantiation
    ('LexicallyDeclaredNames', '_code_'): FDI_possibilities_for_func_ECMAScriptCode,
    # 11005 FunctionDeclarationInstantiation
    # 17813 BlockDeclarationInstantiation
    # 22946 InitializeEnvironment
    ('LexicallyScopedDeclarations', '_code_'): FDI_possibilities_for_func_ECMAScriptCode + [
        'StatementList',
        'CaseBlock',
        'Module',
    ],

    # 15190 IsValidRegularExpressionLiteral
    ('FlagText', '_literal_'): ['RegularExpressionLiteral'],
    ('BodyText', '_literal_'): ['RegularExpressionLiteral'],

    # 15344 GetTemplateObject
    ('TemplateStrings', '_templateLiteral_'): ['TemplateLiteral'],

    # 15483 Evaluation
    # 18519 ForIn/OfHeadEvaluation
    ('Evaluation', '_expr_'): ['ParenthesizedExpression', 'Expression', 'AssignmentExpression'],
    # 15697 EvaluatePropertyAccessWithExpressionKey
    ('Evaluation', '_expression_'): ['Expression'],
    # 15733 EvaluateNew
    ('Evaluation', '_constructExpr_'): ['NewExpression', 'MemberExpression'],
    # 15754 Evaluation
    ('Evaluation', '_memberExpr_'): ['MemberExpression'],
    # 17157 EvaluateStringOrNumericBinaryExpression
    ('Evaluation', '_leftOperand_'): [
        'UpdateExpression',
        'MultiplicativeExpression',
        'AdditiveExpression',
        'ShiftExpression',
        'BitwiseANDExpression',
        'BitwiseXORExpression',
        'BitwiseORExpression',
    ],
    ('Evaluation', '_rightOperand_'): [
        'ExponentiationExpression',
        'MultiplicativeExpression',
        'AdditiveExpression',
        'EqualityExpression',
        'BitwiseANDExpression',
        'BitwiseXORExpression',
    ],
    # 18263 ForBodyEvaluation
    ('Evaluation', '_test_'): ['Expression'],
    ('Evaluation', '_increment_'): ['Expression'],
    # 18263 ForBodyEvaluation
    # 18548 ForIn/OfBodyEvaluation
    ('Evaluation', '_stmt_'): ['Statement'],
    # 18548 ForIn/OfBodyEvaluation
    ('Evaluation', '_lhs_'): [
        'LeftHandSideExpression',
        'ForBinding',
        # 'ForDeclaration', always invoked with _lhsKind_ = ~lexicalBinding~
        # 'BindingIdentifier', only in Annex B, which we're not handling yet.
    ],
    # 18965 CaseBlockEvaluation
    ('Evaluation', '_C_'): ['CaseClause'],
    # 23648 PerformEval
    ('Evaluation', '_body_'): ['ScriptBody'],
    # 38884 GeneratorStart
    # 39144 AsyncGeneratorStart
    ('Evaluation', '_generatorBody_'): ['FunctionBody'],
    # 39454 AsyncFunctionStart
    ('Evaluation', '_asyncFunctionBody_'): ['FunctionBody', 'ExpressionBody'],

    # 15708 EvaluatePropertyAccessWithIdentifierKey
    ('StringValue', '_identifierName_'): ['IdentifierName'],
    # 23175 Early Errors
    ('StringValue', '_n_'): ['IdentifierName'],

    # 15879 EvaluateNew
    # 15900 Evaluation
    # 15932 EvaluateCall
    ('ArgumentListEvaluation', '_arguments_'): ['Arguments', 'TemplateLiteral'],

    # 15986 ChainEvaluation
    ('ChainEvaluation', '_optionalChain_'): ['OptionalChain'],

    # 17157 Evaluation
    # 17627 KeyedDestructuringAssignmentEvaluation
    # 18694 ForIn/OfBodyEvaluation
    ('DestructuringAssignmentEvaluation', '_assignmentPattern_'): ['AssignmentPattern'],
    # 17532 IteratorDestructuringAssignmentEvaluation
    ('DestructuringAssignmentEvaluation', '_nestedAssignmentPattern_'): ['AssignmentPattern'],

    # 18548 ForIn/OfBodyEvaluation
    ('BindingInitialization', '_lhs_'): ['ForBinding'],

    # 18694 ForIn/OfBodyEvaluation
    ('IsDestructuring', '_lhs_'): [
        'LeftHandSideExpression',
        'ForBinding',
        'ForDeclaration',
        # 'BindingIdentifier', Annex B
    ],
    ('ForDeclarationBindingInstantiation',  '_lhs_'): ['ForDeclaration'],
    ('ForDeclarationBindingInitialization', '_lhs_'): ['ForDeclaration'],

    # 19484 IsSimpleParameterList
    ('IsSimpleParameterList', '_head_'): ['AsyncArrowHead'],

    # 20531 Early Errors
    ('HasDirectSuper', '_constructor_'): ['ClassElement'],

    # 20657 ClassDefinitionEvaluation
    ('DefineMethod', '_constructor_'): ['ClassElement'],

    # 20657 ClassDefinitionEvaluation
    ('IsStatic', '_e_'): ['ClassElement'],

    # 20657 ClassDefinitionEvaluation
    ('ClassElementEvaluation', '_e_'): ['ClassElement'],

    # 21229 IsInTailPosition
    ('HasCallInTailPosition', '_body_'): ['FunctionBody', 'ConciseBody'],
    ('HasCallInTailPosition', '_expr_'): ['ParenthesizedExpression'],

    # 15629 Evaluation
    # 18665 ForIn/OfHeadEvaluation
    ('Evaluation', '_expr_'): ['ParenthesizedExpression', 'Expression', 'AssignmentExpression'],
    # 21719 ScriptEvaluation
    ('Evaluation', '_scriptBody_'): ['Script'],

    # 21746 GlobalDeclarationInstantiation
    ('LexicallyDeclaredNames',      '_script_'): ['Script'],
    ('VarDeclaredNames',            '_script_'): ['Script'],
    ('VarScopedDeclarations',       '_script_'): ['Script'],
    ('LexicallyScopedDeclarations', '_script_'): ['Script'],

    # 22831 ParseModule
    ('ModuleRequests', '_body_'): ['Module'],
    ('ImportEntries',  '_body_'): ['Module'],
    ('ExportEntries',  '_body_'): ['Module'],

    # 23009 ExecuteModule
    ('Evaluation', '_module_.[[ECMAScriptCode]]'): ['Module'],

    # 23800 PerformEval
    ('IsStrict', '_script_'): ['Script'],

    # 23865 EvalDeclarationInstantiation
    ('VarDeclaredNames',            '_body_'): ['ScriptBody'],
    ('VarScopedDeclarations',       '_body_'): ['ScriptBody'],
    ('LexicallyScopedDeclarations', '_body_'): ['ScriptBody'],

    # 23979
    ('StringNumericValue', '_parsedNumber_') : ['StrDecimalLiteral'],

    # 30931 RegExpInitialize
    ('regexp-Evaluate', '_parseResult_'): ['Pattern'],
}

def is_sdo_coverage_exception(sdo_name, lhs_nt, rhs_reduced):
    # Looking at the productions that share a LHS
    # (or equivalently, the RHSs of a multi-production),
    # it's typically the case that if an SDO can be invoked on one,
    # then it can be invoked on all.
    # And thus, if you see an SDO defined on one,
    # you should expect to see it defined on all,
    # either explicitly, or implicitly via chain productions.
    #
    # This function identifies exceptions to that rule of thumb.

    if sdo_name == 'CharacterValue' and lhs_nt == 'ClassEscape' and rhs_reduced == 'CharacterClassEscape':
        # Invocations of this SDO on ClassAtom and ClassAtomNoDash
        # are guarded by `IsCharacterClass ... is *false*`.
        # This excludes the `ClassEscape :: CharacterClassEscape` production.
        return True

    if (
        sdo_name == 'CoveredParenthesizedExpression'
        and
        lhs_nt == 'CoverParenthesizedExpressionAndArrowParameterList'
        and
        rhs_reduced != "`(` Expression `)`"
    ):
        # For this SDO, we're guaranteed (by early error) that rhs must be `(` Expression `)`
        # so the SDO doesn't need to be defined for any other RHS.
        return True

    if sdo_name == 'DefineMethod' and lhs_nt == 'MethodDefinition' and not rhs_reduced.startswith('ClassElementName'):
        # "Early Error rules ensure that there is only one method definition named `"constructor"`
        # and that it is not an accessor property or generator definition."
        # (or AsyncMethod)
        # See SpecialMethod.
        return True

    if sdo_name == 'Evaluation' and lhs_nt == 'ClassDeclaration' and rhs_reduced == "`class` ClassTail":
        # "ClassDeclaration : `class` ClassTail
        # only occurs as part of an |ExportDeclaration| and is never directly evaluated."
        return True

    if sdo_name == 'Evaluation' and lhs_nt == 'ForBinding' and rhs_reduced == 'BindingPattern':
        # ForIn/OfBodyEvaluation invokes Evaluation on ForBinding,
        # but only if IsDestructuring of it is *false*,
        # which is only the case for `ForBinding : BindingIdentifier`.
        # So `ForBinding : BindingPattern` is an exception.
        return True

    if sdo_name == 'HasDirectSuper' and lhs_nt == 'ClassElement' and rhs_reduced != 'MethodDefinition':
        # HasDirectSuper is only invoked on ConstructorMethod of |ClassBody|,
        # which is a |ClassElement| for which ClassElementKind is ~ConstructorMethod~,
        # which can only be `ClassElement : MethodDefinition`
        return True

    if sdo_name == 'DefineMethod' and lhs_nt == 'ClassElement' and rhs_reduced != 'MethodDefinition':
        # DefineMethod is invoked on |ClassElement| only if
        # it's ConstructorMethod of |ClassBody| ...
        return True

    if sdo_name == 'IsConstantDeclaration' and lhs_nt == 'ExportDeclaration' and not rhs_reduced.startswith("`export` `default`"):
        # LexicallyScopedDeclarations skips these, so IsConstantDeclaration won't be invoked on them.
        return True

    if (
        sdo_name in ['PropName', 'PropertyDefinitionEvaluation']
        and 
        lhs_nt == 'PropertyDefinition'
        and
        rhs_reduced == "CoverInitializedName"
    ):
        # "Use of |CoverInitializedName| results in an early Syntax Error in normal contexts..."
        return True

    if sdo_name in ['HasSourceTextAvailable', 'PresentInStackTraces'] and lhs_nt == 'CallExpression' and rhs_reduced != 'CoverCallExpressionAndAsyncArrowHead':
        # When invoked on a CallExpression, can only be one whose evaluation is a direct eval,
        # which can only be an instance of CallExpression : CoverCallExpressionAndAsyncArrowHead
        return True

    if sdo_name == 'TRV' and lhs_nt == 'HexDigits' and rhs_reduced == "HexDigits NumericLiteralSeparator HexDigit":
        # TRV applies to Template stuff,
        # which derives HexDigits only via [Not]CodePoint,
        # which passes ~Sep to HexDigits,
        # which suppresses its 3rd RHS.
        return True

    if lhs_nt == 'OptionalChain' and 'TemplateLiteral' in rhs_reduced:
        # OptionalChain :
        #   `?.` TemplateLiteral
        #   OptionalChain TemplateLiteral
        # "It is a Syntax Error if any code matches this production."
        # So no SDO will be invoked on them.
        return True

    if sdo_name == 'EvaluateConciseBody' and lhs_nt == 'ConciseBody' and rhs_reduced != 'ExpressionBody':
        # EvaluateConciseBody is invoked on ConciseBody *only* when it's of the form
        # `ConciseBody : ExpressionBody`
        return True

    if sdo_name == 'EvaluateAsyncConciseBody' and lhs_nt == 'AsyncConciseBody' and rhs_reduced != 'ExpressionBody':
        # EvaluateAsyncConciseBody is invoked on AsyncConciseBody *only* when it's of the form
        # `AsyncConciseBody : ExpressionBody`
        return True

    # ----------

    if sdo_name in ['AllPrivateIdentifiersValid', 'ContainsArguments']:
        # PR 1668 private fields:
        # "For all other grammatical productions, ..."
        return True

    if sdo_name in ['HasName', 'NamedEvaluation']:
        # Invocations of HasName are guarded by `IsFunctionDefinition of _expr_ is *true*`,
        # so the SDO doesn't need to be defined for most kinds of expr.

        # NamedEvaluation is invoked on |Initializer| and |AssignmentExpression|,
        # which are fairly general, except that it's only invoked on nodes
        # for which IsAnonymousFunctionDefinition() is true,
        # which implies that IsFunctionDefinition is true (and HasName is false).

        if (
            # These are the cases where it *does* need to be defined (explicitly or implicitly):
            lhs_nt in [
                'ParenthesizedExpression', # chain to Expression
                'Initializer',             # chain to AssignmentExpression
            ]
            or
            (lhs_nt, rhs_reduced) in [
                    ('Expression',               'AssignmentExpression'    ),
                    #
                    ('AssignmentExpression',     'ConditionalExpression'   ),
                    ('AssignmentExpression',     'ArrowFunction'           ),
                    ('AssignmentExpression',     'AsyncArrowFunction'      ),
                    #
                    ('ConditionalExpression',    'ShortCircuitExpression'  ),
                    ('ShortCircuitExpression',   'LogicalORExpression'     ),
                    ('LogicalORExpression',      'LogicalANDExpression'    ),
                    ('LogicalANDExpression',     'BitwiseORExpression'     ),
                    ('BitwiseORExpression',      'BitwiseXORExpression'    ),
                    ('BitwiseXORExpression',     'BitwiseANDExpression'    ),
                    ('BitwiseANDExpression',     'EqualityExpression'      ),
                    ('EqualityExpression',       'RelationalExpression'    ),
                    ('RelationalExpression',     'ShiftExpression'         ),
                    ('ShiftExpression',          'AdditiveExpression'      ),
                    ('AdditiveExpression',       'MultiplicativeExpression'),
                    ('MultiplicativeExpression', 'ExponentiationExpression'),
                    ('ExponentiationExpression', 'UnaryExpression'         ),
                    ('UnaryExpression',          'UpdateExpression'        ),
                    ('UpdateExpression',         'LeftHandSideExpression'  ),
                    ('LeftHandSideExpression',   'NewExpression'           ),
                    ('NewExpression',            'MemberExpression'        ),
                    ('MemberExpression',         'PrimaryExpression'       ),
                    #
                    ('PrimaryExpression',        'FunctionExpression'      ),
                    ('PrimaryExpression',        'ClassExpression'         ),
                    ('PrimaryExpression',        'GeneratorExpression'     ),
                    ('PrimaryExpression',        'AsyncFunctionExpression' ),
                    ('PrimaryExpression',        'AsyncGeneratorExpression'),
                ]
        ):
            return False
        else:
            return True

    return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def descend_via_unit_derivations(anode):
    if anode.prod.is_token_prod:
        return anode
    elif len(anode.prod.rhs_pieces) == 1 and anode.prod.rhs_pieces[0].startswith('{'):
        return descend_via_unit_derivations(anode.children[0])
    else:
        return anode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# import cProfile
# cProfile.run('main()', '_prof')

# vim: sw=4 ts=4 expandtab
