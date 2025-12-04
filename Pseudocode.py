#!/usr/bin/python3

# ecmaspeak-py/Pseudocode.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, math, pdb, string, pprint, os
from collections import defaultdict

from HTML import HNode
from Pseudocode_Parser import Pseudocode_Parser, ANode
import emu_grammars
import shared
from shared import spec, stderr, msg_at_node

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_stuff_with_pseudocode():
    check_step_references()

    check_vars()

    check_for_unbalanced_ifs()

    check_value_descriptions()

    analyze_static_dependencies()
    check_the_sdo_name()
    check_optional_parameters()
    check_sdo_coverage()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_step_references():
    # This deals with the pseudocode in <emu-alg> elements,
    # though in a fairly superficial way.
    # (I.e., we don't need to have it parsed according to the emu-alg grammar.)

    f_step_refs = shared.open_for_output('step_refs')
    def put(*args): print(*args, file=f_step_refs)

    curr_referring_section = None
    for (referring_section, referring_line, refd_section, refd_line) in each_step_ref():
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
        if refd_section is referring_section:
            put(f"        (same section):")
        else:
            put(f"        {refd_section.section_num} {refd_section.section_title}:")
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
            # kludgey for 13.15.2:
            fr'step {x}, {x}, {x}, {x}, {x}',
            fr'step {x}, {x}, {x}, {x}',
            fr'step {x}',
        ]
        for pattern in patterns:
            mo = re.compile(pattern, re.IGNORECASE).match(spec.text, st)
            if mo:
                break
        else:
            assert 0, spec.text[st:st+200].replace('\n', '\\n')

        step_ids = mo.groups()

        for step_id in step_ids:

            refd_emu_alg = spec.node_with_id_[step_id]
            assert refd_emu_alg.element_name == 'emu-alg'

            refd_section = refd_emu_alg.closest_containing_section()

            mo = re.search(rf'.*id="{step_id}".*', refd_emu_alg.source_text())
            assert mo
            refd_line = mo.group(0).lstrip()

            yield (referring_section, referring_line, refd_section, refd_line)

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
        if what == 'field_value_type':
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
        cc_section = hnode.closest_containing_section()
        if hasattr(cc_section, 'section_num'):
            identification = f"{cc_section.section_num} {cc_section.section_title}"
        else:
            identification = f"{cc_section.element_name} id={cc_section.attrs['id']!r}"
        stderr(f"\nFailed to parse <{hnode.element_name}> in {identification}")
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
        hnode
        for hnode in base_hnode.each_descendant()
        if hnode.element_name in connectable_hnode_names
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
                '{cap_word} of {LOCAL_REF}',
                '{cap_word} of {LOCAL_REF} {WITH_ARGS}',
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

            elif rhs == 'the abstract operation named by {DOTTING} using the elements of {DOTTING} as its arguments':
                op_names = [ 'ScriptEvaluationJob', 'TopLevelModuleEvaluationJob']
                args = [d.children[1]] # XXX

            else:
                callee_name = {
                    "the CharSet returned by {h_emu_grammar}"          : 'CompileToCharSet',
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
                if opn_before_paren.source_text() == '_conversionOperation_':
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
                    assert d.source_text() == '_operation_(_lNum_, _rNum_)'
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

def check_vars():
    stderr('check_vars ...')

    # Check algorithms for used-but-not-defined
    # and defined-but-not-used.
    #
    # The approach here is fairly simplistic,
    # not caring about scope or use-before-def
    # or whether a var is defined on all possible paths
    # that reach a particular use.

    for (alg_name, alg_info) in (
        sorted(spec.alg_info_['op'].items())
        +
        sorted(spec.alg_info_['bif'].items())
    ):
        for alg_defn in alg_info.all_definitions():
            for anode in alg_defn.anodes:
                check_vars_in_anode(anode, alg_defn.parent_header)

def check_vars_in_anode(anode, alg_header):

    # If an algorithm is incomplete in some way,
    # it's pointless to check the vars in an algorithm.
    # Detect those cases and do an early return.
    #
    # (This way of checking is fairly kludgey.)

    if anode is None: return

    s = anode.start_posn
    preceding_text = shared.spec_text[s-100:s].replace('\n', r'\n')

    if ' replaces-step=' in preceding_text:
        # This is a chunk of pseudocode
        # that replaces a step in some other algorithm.
        # So it probably refers to vars that are defined there,
        # and might define vars that are referenced only there.
        return

    if 'this method performs the following steps to prepare the Strings:' in preceding_text:
        # String.prototype.localeCompare
        # It's the start of an algorithm,
        # so we'd expect unused vars.
        # (Though not undefined vars, so we could just check for those.)
        return

    # -------------

    class Thing:
        def __init__(self):
            self.defs = []
            self.uses = []
            self.okay_if_unused = False

    things = defaultdict(Thing)

    for param in alg_header.params:
        if param.decl_node:
            d = param.decl_node.children[0]
        else:
            d = None
        d_thing = things[param.name]
        d_thing.defs.append(d)
        d_thing.okay_if_unused = alg_header.species.startswith('op: discriminated by')
        # It's okay if some of the defns in a discriminated union
        # don't use all the parameters

    fp = alg_header.for_phrase_node
    if fp and '{var}' in fp.prod.rhs_s:
        d = fp.children[1]
        d_thing = things[d.source_text()]
        d_thing.defs.append(d)
        d_thing.okay_if_unused = alg_header.species.startswith('op: discriminated by')

    for d in anode.each_descendant_or_self():
        if d.prod.lhs_s == '{var}':
            d_thing = things[d.source_text()]
            p = d.parent
            pp = str(p.prod)
            if pp == '{DEFVAR} : {var}':
                d_thing.defs.append(d)

            elif pp == '{EXPR} : a List whose elements are the elements of {var} ordered as if an Array of the same values had been sorted using {percent_word} using {LITERAL} as {var}' and d is p.children[3]:
                # In ModuleNamespaceCreate,
                # `_comparefn_` refers to a parameter of %Array.prototype.sort%,
                # so it's neither a declaration nor a use.
                pass

            else:
                d_thing.uses.append(d)

    for (varname, thing) in sorted(things.items()):

        if thing.defs and not thing.uses:
            # Defined but not used
            if thing.okay_if_unused:
                pass
            else:
                msg_node = thing.defs[0]
                if msg_node is None:
                    msg_node = anode
                msg_at_node(
                    msg_node,
                    f"{varname} is not used in this algorithm"
                )

        if thing.uses and not thing.defs:
            # Used but not defined
            msg_at_node(
                thing.uses[0],
                f"{varname} is not defined in this algorithm"
            )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_for_unbalanced_ifs():
    stderr('check_for_unbalanced_ifs ...')

    # Check algorithms for 'unbalanced' If-commands:
    # arms should either be all-indented or all-inline.

    for (alg_name, alg_info) in (
        sorted(spec.alg_info_['op'].items())
        +
        sorted(spec.alg_info_['bif'].items())
    ):
        for alg_defn in alg_info.all_definitions():
            for anode in alg_defn.anodes:
                if anode is None: continue
                for d in anode.each_descendant_or_self():
                    if d.prod.lhs_s == '{IF_OTHER}':
                        arms = [* each_if_arm(d)]
                        assert len(arms) > 0
                        if len(arms) == 1:
                            continue
                            # because there's nothing to 'balance'

                        arm_nts = set(
                            str(arm.prod.lhs_s)
                            for arm in arms
                        )
                        if len(arm_nts) == 1: continue
                        arm_nts_str = ' '.join(
                            str(arm.prod.lhs_s)
                            for arm in arms
                        )
                        msg_at_node(d, f"If-command has 'unbalanced' arms: {arm_nts_str}")

                    elif d.prod.lhs_s == '{IF_CLOSED}':
                        # Editorial-Conventions says:
                        # > in a collapsed (single-line) if/else,
                        # > all branches should "do the same thing",
                        # > e.g. set the same alias, return, perform, etc."

                        arms = [* each_if_arm(d)]
                        assert len(arms) > 1
                        pre = os.path.commonprefix(
                            [arm.source_text() for arm in arms]
                        )
                        if re.match(r'return |let _\w+_ be |set _\w+_ to ', pre):
                            pass
                        else:
                            msg_at_node(d, f"If-command branches don't all 'do the same thing'")

def each_if_arm(anode):
    if anode.prod.lhs_s == '{IF_CLOSED}':
        for child in anode.children:
            assert child.prod.lhs_s in ['{SMALL_COMMAND}', '{CONDITION}']
            if child.prod.lhs_s == '{SMALL_COMMAND}':
                yield child
    elif anode.prod.lhs_s == '{IF_OTHER}':
        assert anode.prod.rhs_s == '{IF_OPEN}{IF_TAIL}'
        [if_open, if_tail] = anode.children
        yield from each_if_arm(if_open)
        yield from each_if_arm(if_tail)
    elif anode.prod.lhs_s in ['{IF_OPEN}', '{ELSEIF_PART}']:
        [condition, commands] = anode.children
        assert commands.prod.lhs_s in ['{IND_COMMANDS}', '{SMALL_COMMAND}']
        yield commands
    elif anode.prod.lhs_s == '{IF_TAIL}':
        if anode.prod.rhs_s == '{EPSILON}':
            [] = anode.children
        elif anode.prod.rhs_s == '{_NL_N} {ELSEIF_PART}{IF_TAIL}':
            [elseif_part, if_tail] = anode.children
            yield from each_if_arm(elseif_part)
            yield from each_if_arm(if_tail)
        elif anode.prod.rhs_s == '{_NL_N} {ELSE_PART}':
            [else_part] = anode.children
            yield from each_if_arm(else_part)
        else:
            assert 0, str(anode.prod)
    elif anode.prod.lhs_s == '{ELSE_PART}':
        commands = anode.children[-1]
        assert commands.prod.lhs_s in ['{IND_COMMANDS}', '{SMALL_COMMAND}', '{COMMAND}']
        yield commands
    else:
        assert 0, anode.prod.lhs_s

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_value_descriptions():
    stderr('check_value_descriptions ...')

    def visit(n):
        if hasattr(n, '_syntax_tree'):
            stree = n._syntax_tree
            if stree is not None:
                for anode in stree.each_descendant_or_self():
                    if anode.prod.lhs_s == '{VAL_DESC_DISJUNCTION}':
                        check_val_desc_disjunction(anode)

    spec.doc_node.preorder_traversal(visit)

def check_val_desc_disjunction(val_desc_disjunction):
    # Enforce on the rules set out in
    # https://github.com/tc39/ecma262/pull/2972#issuecomment-1379579896
    # and following.

    assert val_desc_disjunction.prod.lhs_s == '{VAL_DESC_DISJUNCTION}'

    sm_string = ''.join(
        single_or_multi(val_desc)
        for val_desc in val_desc_disjunction.children
    )

    # If a disjunction combines multi-valued terms (types)
    # with single-valued terms (constants/literals),
    # all the multis should come before all the singles.
    if re.fullmatch(r'(M*)(S*)', sm_string):
        pass
    else:
        msg_at_node(
            val_desc_disjunction,
            f"In a VAL_DESC_DISJUNCTION, the multi-valued terms should come before the single-valued terms, but here the terms are '{sm_string}'"
        )

    # -----------------
    # And then there are rules about whether the disjunction
    # should be preceded by 'either', 'one of', or nothing.

    value_description = val_desc_disjunction.parent
    assert value_description.prod.lhs_s == '{VALUE_DESCRIPTION}'
    assert value_description.prod.rhs_s.endswith('{VAL_DESC_DISJUNCTION}')
    prefix = value_description.prod.rhs_s.removesuffix('{VAL_DESC_DISJUNCTION}').rstrip()

    # See https://github.com/tc39/ecma262/pull/2972#issuecomment-1372894434

    gparent_prod = value_description.parent.prod
    if str(gparent_prod) in [
        '{CONDITION_1} : {EX} is {VALUE_DESCRIPTION}',
        '{CONDITION_1} : {EX} is not {VALUE_DESCRIPTION}',
        '{VAL_DESC} : a normal completion containing {VALUE_DESCRIPTION}',
        '{VAL_DESC} : an Abstract Closure that takes {VAL_DESC} and {VAL_DESC} and returns {VALUE_DESCRIPTION}',
    ]:
        # This is a 'prose' context.
        # The prefix should be "one of" only in the case where
        # there are 3+ disjuncts and all are single-valued.
        # Otherwise, it should be "either".
        preferred_prefix = 'one of' if re.fullmatch(r'SSS+', sm_string) else 'either'

    elif (
        gparent_prod.lhs_s in ['{H1_BODY}', '{PARAMETER_DECL}', '{FIELD_VALUE_TYPE}']
        or
        str(gparent_prod).startswith('{VAL_DESC} : a Record with fields')
        or
        str(gparent_prod) == '{VALUE_DESCRIPTION} : {VAL_DESC}, but not {VALUE_DESCRIPTION}'
    ):
        # This is a 'declaration' context.
        # It doesn't need a prefix, unless the result would be ambiguous.
        vd0 = val_desc_disjunction.children[0]
        if vd0.prod.rhs_s == 'a normal completion containing {VALUE_DESCRIPTION}':
            # would be ambiguous without a prefix
            preferred_prefix = 'either'
        else:
            preferred_prefix = ''

    else:
        assert 0, str(gparent_prod)

    if prefix != preferred_prefix:
        msg_at_node(
            val_desc_disjunction,
            f"this VAL_DESC_DISJUNCTION should be preceded by '{preferred_prefix}' rather than '{prefix}'"
        )

    # The other way to accomplish the discrimination
    # between 'prose' contexts and 'declaration' contexts
    # would be to change pseudocode.grammar, splitting {VALUE_DESCRIPTION}
    # (into, say, {PROSE_VALUE_DESCRIPTION} and {DECL_VALUE_DESCRIPTION}),
    # and changing each occurrence of {VALUE_DESCRIPTION} to one of those
    # as appropriate.
    # Then here, just look at val_desc_disjunction.parent.prod.lhs_s.

def single_or_multi(val_desc):
    assert val_desc.prod.lhs_s == '{VAL_DESC}'
    # Return 'M' if {val_desc} is a multi-valued description (type),
    # or 'S' if it is a single-valued description (constant/literal).

    r = val_desc.prod.rhs_s

    if r.startswith(('a ', 'an ', 'an? ', 'any', 'some ')):
        return 'M'

    if r in [
        'ECMAScript source text',
        'source text',
        'the Environment Record for a |Catch| clause',
        'the execution context of a generator',
        'the single code point {code_point_lit} or {code_point_lit}',
        'the {nonterminal} of an? {nonterminal}',
    ]:
        return 'M'

    if r in [
        '-1',
        '{LITERAL_ISH}',
        '{LITERAL}',
        '{nonterminal}',
    ]:
        return 'S'

    assert 0, r

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
                                stderr(f"spec.alg_info_['op'] has no entry for {callee_name!r} ({alg_name} calls it in {alg_defn.parent_header.section.section_num})")
                    elif hasattr(d, '_hnode') and hasattr(d._hnode, '_syntax_tree'):
                        assert alg_name == 'Early Errors'
                        # "... and the following algorithm evaluates to *true*: ..."
                        recurse(d._hnode._syntax_tree)

            for anode in alg_defn.anodes:
                if anode: recurse(anode)
            alg_info.callees.update(alg_defn.callees)

        if alg_name == 'HostLoadImportedModule':
            assert len(alg_info.all_definitions()) == 0
            # There's just a list of requirements
            # that the implementation must conform to.
            # But one of those is that it has to invoke FinishLoadingImportedModule.
            alg_info.callees.add('FinishLoadingImportedModule')

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
                    'an iterator object',
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
            for anode in op_defn.anodes:
                if anode: recurse(anode)

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

def check_the_sdo_name():
    stderr("check_the_sdo_name ...")

    # https://github.com/tc39/ecma262/pull/3309#issuecomment-2067296673:
    # In an SDO-invocation, use "the" before the SDO name iff:
    # - the SDO name is a noun phrase,
    # - the SDO does not return a completion record, and
    # - the SDO-invocation does not occur within an AO-invocation.

    for (op_name, op_info) in sorted(spec.alg_info_['op'].items()):
        if op_info.species.startswith('op: discriminated by syntax'):
            if len(op_info.invocations) == 0:
                assert op_name == 'Early Errors'
                continue

            rnn = op_info.headers[0].return_nature_node
            if rnn is None:
                assert op_name == 'MV'
                r = 'a mathematical value'
            else:
                r = rnn.source_text()
            if (
                r in ['a Boolean', '~unused~', 'either a normal completion containing ~unused~ or an abrupt completion']
                or
                op_name.startswith(('Compile', 'Instantiate', 'Define', 'Evaluate'))
                or
                op_name == 'WithClauseToAttributes'
                or 
                re.fullmatch(r'either a normal completion containing .+ or an abrupt completion', r)
                or
                r in ['a Completion Record', 'a return completion', 'a throw completion or a return completion']
            ):
                this_sdo_accepts_the = False
            else:
                this_sdo_accepts_the = True

            for invocation in op_info.invocations:
                assert invocation.prod.lhs_s == '{NAMED_OPERATION_INVOCATION}'

                # For an SDO that 'accepts' "the",
                # we nevertheless suppress 'the' when the SDO-invocation is within an AO-invocation.
                should_be_the = (
                    this_sdo_accepts_the
                    and
                    invocation.closest_containing('{PREFIX_PAREN}') is None
                )

                is_the = 'the {cap_word}' in invocation.prod.rhs_s

                if is_the and not should_be_the:
                    msg_at_node(
                        invocation,
                        "For this SDO, there shouldn't be a 'the' before the SDO name"
                    )
                elif not is_the and should_be_the:
                    msg_at_node(
                        invocation,
                        "For this SDO, there should be a 'the' before the SDO name"
                    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_optional_parameters():
    stderr("check_optional_parameters ...")

    f_opa = shared.open_for_output('optional_param_anomalies')
    def put(*args): print(*args, file=f_opa)

    # Built-in functions can have 'optional' parameters too, but:
    # (a) they have a different meaning from optional parameters in operations, and
    # (b) we're not free to make them non-optional or eliminate them.
    # So we only look at optional parameters in operations.

    for (op_name, op_info) in sorted(spec.alg_info_['op'].items()):
        if not hasattr(op_info, 'params'): continue

        for (param_i, param) in enumerate(op_info.params, start=1):
            assert param.punct in ['', '[]']
            if param.punct == '[]':
                # optional parameter

                context_line = f"{op_name}'s parameter #{param_i} ({param.name}) is optional"
                n_invocations = len(op_info.invocations)

                if n_invocations == 0:
                    put()
                    put(context_line)
                    put(f"  but {op_name} has no invocations!")
                    continue

                n_invs_that_supply_an_arg = 0
                n_invs_that_dont_supply_an_arg = 0
                for inv in op_info.invocations:
                    p = str(inv.prod)
                    if p == '{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})':
                        (opn_before_paren, exlist_opt) = inv.children
                        # assert opn_before_paren.source_text() == op_name
                        # Not necessarily, e.g. _module_.LoadRequestedModules
                        args = exes_in_exlist_opt(exlist_opt)

                    elif p == '{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}':
                        args = []

                    elif p == '{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}':
                        (cap_word, local_ref, with_args) = inv.children
                        assert cap_word.source_text() == op_name
                        # ignore local_ref
                        args = with_args.children

                    else:
                        assert 0, p

                    if len(args) >= param_i:
                        # this invocation supplies an arg for the parameter
                        n_invs_that_supply_an_arg += 1
                    else:
                        # this invocation doesn't supply an arg for the parameter
                        n_invs_that_dont_supply_an_arg += 1

                assert n_invs_that_supply_an_arg + n_invs_that_dont_supply_an_arg == n_invocations
                if n_invs_that_dont_supply_an_arg == 0:
                    put()
                    put(context_line)
                    put(f"  Of {n_invocations} invocations, all supply an arg for that parameter, so make it non-optional?")
                if n_invs_that_supply_an_arg == 0:
                    put()
                    put(context_line)
                    put(f"  Of {n_invocations} invocations, none supplies an arg for that parameter, so eliminate it?")

    f_opa.close()

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
                if alg_defn.parent_header.section.section_num.startswith('B'): continue

                puk_set = alg_defn.get_puk_set()
                if not puk_set:
                    stderr(f"! sdo_coverage may be broken because puk_set is empty")
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
                        elif opcall_st == 'the TopLevelVarDeclaredNames of |Statement|':
                            # 1. If |Statement| is <emu-grammar>Statement : LabelledStatement</emu-grammar> ,
                            #    return the TopLevelVarDeclaredNames of |Statement|.
                            nts = ['LabelledStatement']
                        elif opcall_st == 'the TopLevelVarScopedDeclarations of |Statement|':
                            # 1. If |Statement| is <emu-grammar>Statement : LabelledStatement</emu-grammar> ,
                            #    return the TopLevelVarScopedDeclarations of |Statement|.
                            nts = ['LabelledStatement']

                elif u_lhs == '{PROD_REF}':
                    u_rhs = uprimary.prod.rhs_s
                    if u_rhs in [
                        "that {nonterminal}",
                        'this {nonterminal}',
                        'the {nonterminal}',
                        'the {nonterminal} containing {LOCAL_REF}',
                        'the {nonterminal} of {LOCAL_REF}',
                        'the {nonterminal} that is that single code point',
                        'the {nonterminal} that is that {nonterminal}',
                        'the derived {nonterminal}',
                        '{nonterminal} {var}',
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
                RSQs = [r.children[0] for r in def_rhs_n._rhs_items if r.kind == 'RHS_SYMBOL_QM']

                nGNTs = [r for r in def_rhs_n._rhs_items if r.kind == 'GNT']

                reduced_prod_string = f"{lhs_nt} -> {def_rhs_n._reduced}"

                for opt_combo in each_opt_combo(RSQs):
                    optbits = ''.join(
                        {
                            'omitted': '0',
                            'required': '1'
                        } [optionality]
                        for (_, optionality) in opt_combo
                    )

                    puk = (lhs_nt, def_rhs_n._reduced, optbits)
                    puk_str = f"{reduced_prod_string} [{optbits}]"
                    used_keys.add(puk)
                    rules = coverage_info_for_this_sdo.get(puk, [])

                    if len(rules) == 1:
                        # great
                        if debug:
                            put(f"{sdo_name} for {puk_str} has an explicit rule")
                        pass
                    elif len(rules) > 1:
                        put(f"{sdo_name} for {puk_str} is handled by {len(rules)} rules!")
                    elif is_sdo_coverage_exception(sdo_name, lhs_nt, def_rhs_n._reduced):
                        # okay
                        if debug:
                            put(f"{sdo_name} for {reduced_prod_string} is a coverage exception")
                        pass
                    else:
                        # {puk_str} is not handled by any explicit rule,
                        # and isn't a coverage exception.
                        # So check if the chain rule applies.

                        nts = [gnt._nt_name for gnt in nGNTs] + required_nts_in(opt_combo)
                        if len(nts) == 1:
                            # The rule for chain productions applies.
                            # So recurse on the rhs non-terminal.
                            [nt] = nts

                            if debug:
                                put(f"{sdo_name} for {puk_str} chains to {nt}")

                            queue_ensure(nt)
                        else:
                            put(f"{sdo_name} for {puk_str} needs a rule")

        unused_keys = coverage_info_for_this_sdo.keys() - used_keys
        for unused_key in sorted(unused_keys):
            put(f"{sdo_name} has unused rule for: {unused_key}")

    coverage_f.close()

# -------------------------------

def each_opt_combo(RSQs):
    N = len(RSQs)
    if N == 0:
        yield []
    elif N == 1:
        [a] = RSQs
        yield [(a, 'omitted' )]
        yield [(a, 'required')]
    elif N == 2:
        [a, b] = RSQs
        yield [(a, 'omitted' ), (b, 'omitted' )]
        yield [(a, 'omitted' ), (b, 'required')]
        yield [(a, 'required'), (b, 'omitted' )]
        yield [(a, 'required'), (b, 'required')]
    elif N == 3:
        [a, b, c] = RSQs
        yield [(a, 'omitted' ), (b, 'omitted' ), (c, 'omitted' )]
        yield [(a, 'omitted' ), (b, 'omitted' ), (c, 'required')]
        yield [(a, 'omitted' ), (b, 'required'), (c, 'omitted' )]
        yield [(a, 'omitted' ), (b, 'required'), (c, 'required')]
        yield [(a, 'required'), (b, 'omitted' ), (c, 'omitted' )]
        yield [(a, 'required'), (b, 'omitted' ), (c, 'required')]
        yield [(a, 'required'), (b, 'required'), (c, 'omitted' )]
        yield [(a, 'required'), (b, 'required'), (c, 'required')]
    else:
        assert 0

def required_nts_in(opt_combo):
    return [symbol._nt_name for (symbol, omreq) in opt_combo if omreq == 'required' and symbol.kind == 'GNT']

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

    # 18632 TemplateString
    ('TRV', '_templateToken_'): ['NoSubstitutionTemplate', 'TemplateHead', 'TemplateMiddle', 'TemplateTail'],
    ('TV',  '_templateToken_'): ['NoSubstitutionTemplate', 'TemplateHead', 'TemplateMiddle', 'TemplateTail'],

    # 18694 ForIn/OfBodyEvaluation
    ('IsDestructuring', '_lhs_'): [
        'LeftHandSideExpression',
        'ForBinding',
        'ForDeclaration',
        # 'BindingIdentifier', Annex B
    ],
    ('AssignmentTargetType',                '_lhs_'): ['LeftHandSideExpression'],
    ('ForDeclarationBindingInstantiation',  '_lhs_'): ['ForDeclaration'],
    ('ForDeclarationBindingInitialization', '_lhs_'): ['ForDeclaration'],

    # 19365
    ( 'Evaluation', '_specifierExpression_'): ['AssignmentExpression'],
    ( 'Evaluation', '_optionsExpression_'  ): ['AssignmentExpression'],

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
    ('ScriptIsStrict', '_script_'): ['Script'],

    # 23865 EvalDeclarationInstantiation
    ('VarDeclaredNames',            '_body_'): ['ScriptBody'],
    ('VarScopedDeclarations',       '_body_'): ['ScriptBody'],
    ('LexicallyScopedDeclarations', '_body_'): ['ScriptBody'],

    # 23979
    ('StringNumericValue', '_parsedNumber_') : ['StrDecimalLiteral'],

    # 29052 ParseHexOctet
    ('MV', '_parseResult_'): ['HexDigits'],

    # 30931 RegExpInitialize
    ('CompilePattern', '_parseResult_'): ['Pattern'],

    # 34988 GroupSpecifiersThatMatch
    ('CapturingGroupName', '_thisGroupName_'): [
        'GroupName',
    ],
    ('CapturingGroupName', '_gs_'): [
        'GroupSpecifier',
    ],

    # 35989
    ('CapturingGroupName', '_x_'): ['GroupSpecifier'],
    ('CapturingGroupName', '_y_'): ['GroupSpecifier'],

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

    if sdo_name == 'StringValue' and (
        lhs_nt == 'LeftHandSideExpression' and rhs_reduced != 'NewExpression'
        or
        lhs_nt == 'MemberExpression' and rhs_reduced != 'PrimaryExpression'
        or
        lhs_nt == 'PrimaryExpression' and rhs_reduced != 'IdentifierReference'
    ):
        # StringValue is applied to a |LeftHandSideExpression|
        # only when IsIdentifierRef of |LeftHandSideExpression| is *true*.
        # This excludes all derivations from |LeftHandSideExpression| except for 
        # LeftHandSideExpression -> NewExpression -> MemberExpression -> PrimaryExpression -> IdentifierReference
        #
        # Likewise for StringValue applied to |DestructuringAssignmentTarget|.
        # (DestructuringAssignmentTarget's only RHS is LeftHandSideExpression,
        # so it doesn't involve more coverage exceptions.)
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
