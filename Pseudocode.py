#!/usr/bin/python3

# ecmaspeak-py/Pseudocode.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, math, pdb, string, pprint
from collections import defaultdict

from HTML import HNode
from Pseudocode_Parser import Pseudocode_Parser, ANode
import emu_grammars
import shared
from shared import spec, stderr

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_stuff_with_pseudocode():
    check_step_references()

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
        elif ref_is_followed_by(' of <emu-xref href="#sec-json.parse">JSON.parse</emu-xref>'):
            refd_alg_name = 'JSON.parse'
            refd_section_id = 'sec-json.parse'
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
    global pseudocode_parser
    pseudocode_parser = Pseudocode_Parser('pseudocode')

def report_all_parsers():
    pseudocode_parser.report()

def parse(hnode, what=None):
    assert isinstance(hnode, HNode)
    assert not hasattr(hnode, '_syntax_tree')

    # In most case, we parse the element's inner text.
    start_posn = hnode.inner_start_posn
    end_posn   = hnode.inner_end_posn

    if hnode.element_name == 'emu-alg':
        assert what is None
        goal = 'EMU_ALG_BODY'

        # # sneak this in...
        # n_lines = spec.text.count('\n', start_posn, end_posn)
        # if n_lines > 60:
        #     cc_section = hnode.closest_containing_section()
        #     print(f'\n    emu-alg with {n_lines} lines in {cc_section.section_num} "{cc_section.section_title}"')

    elif hnode.element_name == 'emu-eqn':
        assert what is None
        goal = 'EMU_EQN_DEF'

    elif hnode.element_name == 'td':
        if what == 'one_line_alg':
            goal = 'ONE_LINE_ALG'
        elif what == 'field_value_type':
            goal = 'FIELD_VALUE_TYPE'
        else:
            assert 0, what

    elif hnode.element_name == 'dd':
        assert what is None
        goal = 'FOR_PHRASE'

    elif hnode.element_name == 'h1':
        goal = 'H1_BODY'

    elif hnode.element_name == 'li':
        if what == 'early_error':
            goal = 'EARLY_ERROR_RULE'
        elif what == 'inline_sdo':
            goal = 'INLINE_SDO_RULE'
        else:
            assert 0, what

    else:
        assert 0, hnode.element_name

    tree = pseudocode_parser.parse_and_handle_errors(start_posn, end_posn, goal)
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

            if rhs == '{h_emu_meta_start}{NAMED_OPERATION_INVOCATION}{h_emu_meta_end}':
                # This will be handled when `d` is set to the inner NOI.
                pass

            elif rhs in [
                '{PREFIX_PAREN}',
                '{PREFIX_PAREN} (see {h_emu_xref})',
            ]:
                # This will be handled below, when `d` is set to the {PREFIX_PAREN}.
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
                '{cap_word} of {LOCAL_REF}',
                '{cap_word} of {LOCAL_REF} {WITH_ARGS}',
                '{cap_word}({EX})',
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
                [local_ref] = d.children
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
                    'evaluating {LOCAL_REF}. This may be of type Reference' : 'Evaluation',
                    'evaluating {nonterminal} {var}'                   : 'Evaluation',
                    "the CharSet returned by {h_emu_grammar} "         : 'CompileToCharSet',
                    '{LOCAL_REF} Contains {G_SYM}'                     : 'Contains',
                    '{LOCAL_REF} Contains {var}'                       : 'Contains',
                }[rhs]
                op_names = [callee_name]
                args = d.children # XXX incorrect for a few cases

        elif d.prod.lhs_s == '{PREFIX_PAREN}':
            assert d.prod.rhs_s in ['{OPN_BEFORE_PAREN}({EXLIST_OPT})', '{OPN_BEFORE_PAREN}({EXPR})']
            [opn_before_paren, arg_list] = d.children
            assert opn_before_paren.prod.lhs_s == '{OPN_BEFORE_PAREN}'

            if opn_before_paren.prod.rhs_s == '{h_emu_meta_start}{OPN_BEFORE_PAREN}{h_emu_meta_end}':
                (_, opn_before_paren, _) = opn_before_paren.children

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
                        'Number::exponentiate',
                        'BigInt::exponentiate',
                        'Number::multiply',
                        'BigInt::multiply',
                        'Number::divide',
                        'BigInt::divide',
                        'Number::remainder',
                        'BigInt::remainder',
                        'Number::add',
                        'BigInt::add',
                        'Number::subtract',
                        'BigInt::subtract',
                        'Number::leftShift',
                        'BigInt::leftShift',
                        'Number::signedRightShift',
                        'BigInt::signedRightShift',
                        'Number::unsignedRightShift',
                        'BigInt::unsignedRightShift',
                        'Number::bitwiseAND',
                        'BigInt::bitwiseAND',
                        'Number::bitwiseXOR',
                        'BigInt::bitwiseXOR',
                        'Number::bitwiseOR',
                        'BigInt::bitwiseOR',
                    ]
                else:
                    # mostly closures created+invoked in RegExp semantics
                    # print('>>>', opn_before_paren.source_text())
                    pass
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

    def all_definitions(self):
        return [
            alg_defn
            for alg_header in self.headers
            for alg_defn in alg_header.u_defns
        ]

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
        for alg_defn in alg_info.all_definitions():
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
                                stderr(f"spec.alg_info_['op'] has no entry for {callee_name!r} ({alg_name} calls it in {alg_defn.header.section.section_num})")
                    elif hasattr(d, '_hnode') and hasattr(d._hnode, '_syntax_tree'):
                        assert alg_name == 'Early Errors'
                        # "... and the following algorithm evaluates to *true*: ..."
                        recurse(d._hnode._syntax_tree)

            if alg_defn.anode: recurse(alg_defn.anode)
            alg_info.callees.update(alg_defn.callees)

        put()
        put(alg_name)
        put(f"[{alg_info.species}, {len(alg_info.all_definitions())} definitions]")
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
        if section.alg_headers == []: continue
        op_name = section.alg_headers[0].name

        if section.section_title.startswith('Static Semantics:'):
            op_names_labelled_ss.add(op_name)

        elif section.section_title in ['Statement Rules', 'Expression Rules']:
            assert op_name == 'HasCallInTailPosition'
            # Without this special case, the code would add 'HasCallInTailPosition'
            # to op_names_not_labelled, but that doesn't really make sense,
            # because it's labelled by the parent section:
            assert op_name in op_names_labelled_ss

        elif section.section_title.startswith('Runtime Semantics:'):
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
        for op_defn in op_info.all_definitions():
            def recurse(anode):
                for d in anode.each_descendant_or_self():
                    if looks_runtimey(d):
                        ops_that_look_runtimey.add(op_name)
                        break
                    if hasattr(d, '_hnode') and hasattr(d._hnode, '_syntax_tree'):
                        assert op_name == 'Early Errors'
                        recurse(d._hnode._syntax_tree)
            if op_defn.anode: recurse(op_defn.anode)

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
        if op_info.species.startswith('op: discriminated by syntax'):

            assert op_name not in spec.sdo_coverage_map
            spec.sdo_coverage_map[op_name] = {}

            for alg_defn in op_info.all_definitions():
                # XXX Exclude Annex B definitions from sdo_coverage analysis:
                if alg_defn.header.section.section_num.startswith('B'): continue

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
                        'the {nonterminal} of {LOCAL_REF}',
                        'the {nonterminal} that is that single code point',
                        'the {nonterminal} that is that {nonterminal}',
                        'the corresponding {nonterminal}',
                        'the derived {nonterminal}',
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
    'ClassStaticBlockBody', # FDI called from EvaluateClassStaticBlockBody
]
all_possibilities_for_func_ECMAScriptCode = FDI_possibilities_for_func_ECMAScriptCode + [
    'Initializer',
]

nts_behind_var_in_sdo_call = {

    # 4529 StringToNumber
    ('StringNumericValue', '_literal_'): ['StringNumericLiteral'],

    # 5344
    ('MV', '_literal_'): ['StringIntegerLiteral'],

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

    # 13349 OrdinaryCallEvaluateBody
    ('EvaluateBody', '_F_.[[ECMAScriptCode]]'): all_possibilities_for_func_ECMAScriptCode,

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
    # 40958 AsyncBlockStart
    ('Evaluation', '_asyncBody_'): ['FunctionBody', 'ExpressionBody', 'Module'],

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
    ('Evaluation', '_script_'): ['Script'],

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
    ('CompilePattern', '_parseResult_'): ['Pattern'],

    # 37399 JSON.parse
    ('Evaluation', '_script_'): ['Script'],
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

    if sdo_name == 'HasCallInTailPosition' and lhs_nt == 'ForInOfStatement' and rhs_reduced.startswith("`for` `await` `(`"):
        # "These branches are never invoked, because async functions and top-level async modules
        # are never inspected for tail calls."
        # See issues #2279 and #2544, and PR #2545.
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
