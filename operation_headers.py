#!/usr/bin/python3

# ecmaspeak-py/operation_headers.py:
# Insert <emu-operation-header> elements into the spec.
# 
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

'''
branch name: operation_headers
PR #545:
https://github.com/tc39/ecma262/pull/545
'''

import sys, re, io, pdb
from collections import OrderedDict

import shared
from shared import stderr, spec, RE
from pprint import pprint

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

shared.register_output_dir(sys.argv[1])

def main():
    spec.restore()
    add_line_info()

    stderr("collecting info...")
    convert_nature_init()

    for s in spec.doc_node.each_descendant_that_is_a_section():
        create_operation_info_for_section(s)

    write_spec_with_eoh()

    spec.save()
    stderr("done!")

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def add_line_info():
    # This (or something like it) should maybe be pushed down to shared.py
    # and used earlier/more.
    stderr('add_line_info ...')
    ln = 0
    spec.info_for_line_ = [None] # "line #0"
    for mo in re.finditer('(?m)^( *).*$', spec.text):
        (s,e) = mo.span()

        # If `spec.text` ends with a newline,
        # then the pattern will match immediately after that newline,
        # but we don't want a line for that.
        if s == e and s == len(spec.text):
            break

        i = len(mo.group(1))
        ln += 1
        spec.info_for_line_.append(LineInfo(ln, s, e, i))

class LineInfo:
    def __init__(self, line_num, start_posn, end_posn, indentation):
        self.line_num = line_num
        self.start_posn = start_posn
        self.end_posn = end_posn
        self.indentation = indentation
        self.suppress = False
        self.afters = []

def write_spec_with_eoh():
    stderr("write_spec_with_eoh ...")

    f = shared.open_for_output('spec_w_eoh')

    for line_info in spec.info_for_line_[1:]:
        if not line_info.suppress:
            print(spec.text[line_info.start_posn:line_info.end_posn], file=f)

        if line_info.afters:
            if line_info.indentation == 0:
                # somewhat kludgey
                indentation = spec.info_for_line_[line_info.line_num-1].indentation
            else:
                indentation = line_info.indentation

            ind = ' ' * indentation

            for after_thing in line_info.afters:
                for line in after_thing.lines(ind):
                    print(line, file=f)

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def should_create_op_info_for_algoless_section(s):

    # It depends on what we intend to do with the op_info.
    # From the point of view of static type analysis,
    # there's no reason to generate op_info for an algoless section.

    # -----------------------------

    # It's the kind of section that we never want to create op info for:

    if s.section_kind in [
        'properties_of_an_intrinsic_object',
        'catchall',
        'other_property',
        'shorthand',
        #
        'Call_and_Construct_ims_of_an_intrinsic_object',
        'abstract_operations',
        'early_errors',
        'group_of_properties1',
        'group_of_properties2',
        'loop',
        'properties_of_instances',
        'function_property_xref',
        'other_property_xref',
    ]:
        return False

    # ----------------

    # It's the kind of section that we might want to create op info for,
    # but not if it's algoless?

    if s.section_kind == 'changes':
        assert s.section_title in [
                "Changes to Block Static Semantics: Early Errors",
                "Changes to `switch` Statement Static Semantics: Early Errors",
                "Changes to the `typeof` Operator",
        ]
        return False

    # -----------------------------

    # It's the kind of section that we always want to create op info for:

    if s.section_kind == 'abstract_operation':
        assert (
            s.section_id.startswith('sec-host')
            or
            s.section_id == 'sec-local-time-zone-adjustment' # Should LocalTZA be HostLocalTZA?
            or
            s.section_title == 'StringToBigInt ( _argument_ )'
        )
        return True

    if s.section_kind == 'env_rec_method':
        assert s.section_id == 'sec-object-environment-records-createimmutablebinding-n-s'
        return True

    if s.section_kind == 'numeric_method':
        return True

    # -----------------------------

    # It's the kind of section that we usually want to create op info for,
    # but with some exceptions:

    if s.section_kind == 'accessor_property':
        if s.section_title == 'Object.prototype.__proto__':
            # The section is just a holder for subsections
            # that define the 'get' and 'set' functions.
            return False
        else:
            assert 0, s.section_title
            return True

    if s.section_kind == 'function_property':
        if s.section_title in [
            '%TypedArray%.prototype.set ( _overloaded_ [ , _offset_ ] )',
            # This section is (mostly) just a holder for the two subsections
            # that define the overloads
        ]:
            return False

        # There are various reasons why the spec doesn't provide
        # an algorithmic specification for a function property.
        if (
            s.section_title.startswith('Math.')
            or
            s.section_title.startswith('%TypedArray%.prototype.')
            # A lot of these just say it implements the same algorithm
            # as the corresponding Array.prototype.foo function.
            # or
            # 'Host' in s.section_title
            or
            '.prototype.toLocale' in s.section_title
            or
            '.prototype [ @@iterator ]' in s.section_title
            or
            s.section_title in [
                # same function object as something else:
                'Number.parseFloat ( _string_ )',
                'Number.parseInt ( _string_, _radix_ )',
                'Set.prototype.keys ( )',
                'String.prototype.trimLeft ( )',
                'String.prototype.trimRight ( )',
                'Date.prototype.toGMTString ( )',

                # similar alg to something else:
                'String.prototype.toUpperCase ( )',

                # implementation-defined/dependent:
                # 'LocalTZA ( _t_, _isUTC_ )',
                'Date.now ( )',
                'Date.parse ( _string_ )',
                'Date.prototype.toISOString ( )',
            ]
        ):
            return True

        else:
            assert 0, s.section_title
            return True

    # ----------------

    print('> Should I create an eoh for this?', s.section_kind, s.section_num, s.section_title)
    return False

# ------------------------------------------------------------------------------

def create_operation_info_for_section(s):

    # There are a few cases where a section contains <emu-alg> elements,
    # but we don't want to create emu-operation-header elements for any of them,
    # because we can't really apply STA to them.

    if s.section_title in ['Algorithm Conventions', 'Syntax-Directed Operations']:
        # Its emu-algs are just examples.
        return
    elif s.section_kind == 'shorthand':
        # Its emu-algs are only in shorthand definitions.
        return
    elif s.section_title in [
        'Changes to FunctionDeclarationInstantiation',
        'Changes to GlobalDeclarationInstantiation',
        'Changes to EvalDeclarationInstantiation',
        'Changes to BlockDeclarationInstantiation',
        'VariableStatements in Catch Blocks',
        'Changes to Abstract Equality Comparison',
    ]:
        # Its emu-algs aren't complete, they just replace a step in another emu-alg.
        # XXX: We could analyze them if we made the replacement.
        return
    elif s.section_id == 'sec-module-environment-records-deletebinding-n':
        # "Assert: This method is never invoked."
        # So there's no point type-checking it.
        # (It shouldn't even be there, really.)
        return

    # if s.section_title.startswith('String.prototype.localeCompare'):
        # The emu-alg in the section isn't the (full) alg for the function,
        # so don't connect them.
        # return


    # ------------------------------------------------------

    if s.section_kind == 'syntax_directed_operation':
        # Rather than putting an EOH here
        # (one for every defn of the SDO),
        # we put one at the end, in annex C.
        something_sdo(s)
        return

    elif s.section_num == 'C':
        (ln, _) = shared.convert_posn_to_linecol(s.end_posn)

        spec.info_for_line_[ln].afters.append(AnnexForSDOs())

    # ------------------------------------------------------

    algo_child_posns = [
        i
        for (i, child) in enumerate(s.block_children)
        if (
            child.element_name == 'emu-alg'
            or
            (
                # Conversions are often prsented in a table
                # broken down by type.
                # The <emu-table> is roughly equivalent to an <emu-alg>
                # (or several of them).
                child.element_name == 'emu-table'
                and
                re.fullmatch(
                    r'(To(Boolean|Number|String|Object)|RequireObjectCoercible) \( _argument_ \)',
                    s.section_title
                )
            )
            or
            (
                # For most Math functions,
                # a <ul> plays roughly the role of an <emu-alg>.
                s.parent.section_title == 'Function Properties of the Math Object'
                and
                child.element_name == 'ul'
            )
        )
    ]

    n_algos = len(algo_child_posns)
    if n_algos == 0:
        # Even though the section has no algos,
        # we might want to create an <emu-operation-header>.
        if should_create_op_info_for_algoless_section(s):
            pre_algo_spans = [(0, len(s.block_children))]
        else:
            return

    else:
        pre_algo_spans = [
            (x+1, y)
            for (x,y) in zip([-1] + algo_child_posns, algo_child_posns)
        ]

    # ------------

    if s.section_title == 'Date.parse ( _string_ )':
        # None of the paragraphs are preamble,
        # and it's easier to say that here than later.
        pre_algo_spans = [(0, 0)]

    elif s.section_title == 'Array.prototype.sort ( _comparefn_ )':
        assert n_algos == 3
        # but they're really 3 pieces of one algorithm,
        # so only use the first span
        pre_algo_spans = pre_algo_spans[0:1]
    elif s.section_title == '%TypedArray%.prototype.sort ( _comparefn_ )':
        assert n_algos == 2
        # The first algo is just a variant of the first piece from Array.p.sort,
        # but we still want an eoh for the function.
        # And the second is an alternative defn of SortCompare,
        # so use both pre_algo_spans.
        pass

    # ------------

    if len(pre_algo_spans) > 1:
        assert (
            s.section_kind == 'syntax_directed_operation'
            or
            s.section_title in [
                'MakeArgGetter ( _name_, _env_ )',
                'MakeArgSetter ( _name_, _env_ )',
                'MakeArgGetter ( _name_, _scope_ )', # PR 1477 scope-records
                'MakeArgSetter ( _name_, _scope_ )', # PR 1477 scope-records
                '%TypedArray%.prototype.sort ( _comparefn_ )',
            ]
            or
            s.section_id in [
                'sec-regular-expression-patterns-semantics',
                'sec-initializers-in-forin-statement-heads',
            ] # in annex B
        ), s.section_title

    # ----------------------------------------------------------------

    def isnt_preamble(child):
        if child.element_name == 'emu-note':
            # Sometimes an 'emu-note' should be part of the preamble?
            # FunctionDeclarationInstantiation:
            #     The note is not really part of the preamble.
            #     The next child is the preamble.
            # String.prototype.* and Array.prototype.*:
            #     The note kind of *is* part of the preamble.
            #     XXX ignore for now.
            return True
        elif child.element_name in ['ul', 'pre']:
            return True

        # ?
        elif child.element_name == 'emu-table':
            # e.g. ControlEscape Code Point Values
            return True
        elif child.element_name in ['emu-grammar', 'emu-see-also-para']:
            return True

        assert child.element_name == 'p', child.element_name

        t = child.inner_source_text()
        for x in [
            'Context-free grammars are not sufficiently powerful', # 5.2.4 Static Seantics
            'Static Semantic Rules have names and typically are defined',

            'The `*` |MultiplicativeOperator| performs multiplication', # 6.1.6.1.4
            'The `+` operator performs addition',                       # 6.1.6.1.7
            'Addition is a commutative operation',
            'The `-` operator performs subtraction',                    # 6.1.6.1.8
            # 'The result of `-` operator is then',

            'The implementation of',                        # 15.2.1.17 Runtime Semantics: HostResolveImportedModule

            'An implementation of Host',                    # 16.1 HostReportErrors
                                                            # 18.2.1.2 HostEnsureCanCompileStrings
                                                            # 25.6.1.9 HostPromiseRejectionTracker

            'The Boolean prototype object:',
            'The Symbol prototype object:',
            'The Number prototype object:',
            'The BigInt prototype object:',
            'The Date prototype object:',
            'The String prototype object:',

            'Unless explicitly stated otherwise, the methods of the',
            'Unless explicitly defined otherwise, the methods of the',

            'An ECMAScript implementation that includes',   # 20.1.3.4 Number.prototype.toLocaleString
                                                            # 20.3.4.38 Date.prototype.toLocaleDateString
                                                            # 20.3.4.39 Date.prototype.toLocaleString
                                                            # 20.3.4.40 Date.prototype.toLocaleTimeString
                                                            # 21.1.3.10 String.prototype.localeCompare
                                                            # 21.1.3.22 String.prototype.toLocaleLowerCase
                                                            # 21.1.3.23 String.prototype.toLocaleUpperCase
                                                            # 22.1.3.27 Array.prototype.toLocaleString

            'The meanings of the optional parameters',      # 20.1.3.4 Number.prototype.toLocaleString
                                                            # 22.1.3.27 Array.prototype.toLocaleString
            'The meaning of the optional parameters',       # 20.3.4.38 Date.prototype.toLocaleDateString
                                                            # 20.3.4.39 Date.prototype.toLocaleString
                                                            # 20.3.4.40 Date.prototype.toLocaleTimeString
                                                            # 21.1.3.22 String.prototype.toLocaleLowerCase
                                                            # 21.1.3.23 String.prototype.toLocaleUpperCase

            'When _isUTC_ is true',                         # 20.3.1.7 LocalTZA

            'Before performing the comparisons, the following steps are performed to prepare the Strings:',
                # 21.1.3.10 String.prototype.localeCompare

            'Upon entry, the following steps are performed to initialize evaluation of the `sort` function',
                # 22.1.3.25 Array.prototype.sort
                # 22.2.3.26 %TypedArray%.prototype.sort
            'The implementation-defined sort order condition',
                # 22.2.3.26 %TypedArray%.prototype.sort
            'The following version of SortCompare',
                # 22.2.3.26 %TypedArray%.prototype.sort

            # 22.1.3.34:
            'The initial value of the @@unscopables data property',

            # 24.4.1.3 GetWaiterList:
            'A <dfn>WaiterList</dfn>',
            'Initially a WaiterList object has',            
            'The agent cluster has',
            'Each WaiterList has',

            'Let `',
                # 24.4.2 Atomics.add
                # 24.4.3 Atomics.and
                # 24.4.5 Atomics.exchange
                # 24.4.8 Atomics.or
                # 24.4.10 Atomics.sub
                # 24.4.13 Atomics.xor
        ]:
            if t.startswith(x):
                # print(x, s.section_num, s.section_title)
                return True

        return False

    for (span_start_i, span_end_i) in pre_algo_spans:
        if s.section_title == 'Date.parse ( _string_ )':
            # kludge
            algo = None
        elif span_end_i < len(s.block_children):
            algo = s.block_children[span_end_i]
            assert algo.element_name in ['emu-alg', 'emu-table', 'ul']
        else:
            algo = None


        # Within the span, find the preamble, if any.
        p_start_i = span_start_i
        p_end_i   = span_end_i
        if p_start_i == p_end_i:
            pass
        else:
            while p_start_i < p_end_i:
                if isnt_preamble(s.block_children[p_start_i]):
                    p_start_i += 1
                else:
                    break
            if p_start_i < p_end_i:
                assert s.block_children[p_start_i].element_name == 'p'
            for i in range(p_start_i, p_end_i):
                if isnt_preamble(s.block_children[i]):
                    p_end_i = i
                    break

        n_children_in_preamble = p_end_i - p_start_i
        if n_children_in_preamble == 0:
            # No preamble
            # So no lines to suppress when writing spec_w_eoh.
            lns_to_suppress = []
            (p_end_ln, _) = shared.convert_posn_to_linecol(s.block_children[p_end_i].start_posn)
            op_info_ln = p_end_ln - 1
            preamble_text = ''
        else:
            preamble_children = s.block_children[p_start_i:p_end_i]

            if False and n_children_in_preamble > 1:
                print()
                print('--------', s.section_num, s.section_title)
                print(f"{n_children_in_preamble} children in preamble:")
                for c in preamble_children:
                    print(c.source_text())


            r_start_posn = preamble_children[0].start_posn
            r_end_posn   = preamble_children[-1].end_posn
            (r_start_ln, _) = shared.convert_posn_to_linecol(r_start_posn)
            (r_end_ln,   _) = shared.convert_posn_to_linecol(r_end_posn)
            lns_to_suppress = range(r_start_ln, r_end_ln+1)

            op_info_ln = r_start_ln

            preamble_text = ' '.join(
                child.inner_source_text()
                for child in preamble_children
            )

        if (
            span_start_i == 0 and not (
                s.section_title.startswith('Properties of the')
                or
                s.section_title == 'Array.prototype [ @@unscopables ]'
            )
            or
            s.section_kind == 'syntax_directed_operation'
        ):
            # The op is the one indicated by the section heading.
            # print(s.section_num, s.section_kind, 'is', span_end_i)
            hoi = get_info_from_heading(s)
            op_kind = s.section_kind
        else:
            # The op is *not* the one indicated by the section heading.
            # print(s.section_num, s.section_kind, 'isnt', span_end_i)
            hoi = OperationInfo()
            if s.section_title.startswith('MakeArgGetter'):
                op_kind = 'anonymous_built_in_function'
            elif s.section_title.startswith('MakeArgSetter'):
                op_kind = 'anonymous_built_in_function'
            elif s.section_title.startswith('%TypedArray%.prototype.sort'):
                op_kind = 'abstract_operation'
            elif s.section_title.startswith('Properties of the'):
                op_kind = 'abstract_operation'
            elif s.section_title == 'Array.prototype [ @@unscopables ]':
                op_kind = 'abstract_operation'
                hoi.name = 'initializer for @@unscopables'
                hoi.param_names = []
            elif s.section_id in [
                'sec-regular-expression-patterns-semantics',
                'sec-initializers-in-forin-statement-heads',
            ]:
                # print('347', op_kind, s.section_num, s.section_title)
                continue # XXX
            else:
                assert 0, s.section_title

        if op_kind == 'abstract_operation':
            oi = get_info_for_ao(s, hoi, preamble_text)
        elif op_kind == 'numeric_method': # PR 1515 BigInt
            oi = get_info_for_nm(s, hoi, preamble_text)
        elif op_kind.endswith('_rec_method'):
            oi = get_info_for_cm(s, hoi, preamble_text)
        elif op_kind == 'internal_method':
            oi = get_info_for_im(s, hoi, preamble_text)

        elif op_kind in [
            'function_property',
            'function_property_overload',
            'accessor_property',
            'CallConstruct',
            'CallConstruct_overload',
            'anonymous_built_in_function',
        ]:
            oi = get_info_for_builtin_function(s, op_kind, hoi, preamble_text)

        elif op_kind == 'syntax_directed_operation':
            # print('370', op_kind, s.section_num, s.section_title)
            continue # XXX

        else:
            # 5 cases
            # print('374', op_kind, s.section_num, s.section_title)
            continue
            # assert 0, op_kind

        # ------------------------------------------------------------------
        # Okay, so at this point we're finally committed to creating an eoh.

        if algo: oi.definitions.append(algo)

        if 0:
            def each_piece_of_preamble_thing():
                if span_start_i == span_end_i:
                    assert p_start_i == p_end_i
                    yield '['
                    yield ']'
                else:
                    for i in range(span_start_i, span_end_i):
                        if i == p_start_i: yield '['
                        if i == p_end_i: yield ']'
                        yield s.block_children[i].element_name
                    if span_end_i == p_end_i: yield ']'
                if span_end_i == len(s.block_children): yield '.'
            preamble_thing = ' '.join( x for x in each_piece_of_preamble_thing() )

            if p_start_i != span_start_i or p_end_i != span_end_i:
                print(preamble_thing.ljust(30), s.section_kind, s.section_num, s.section_title)

        oi.finalize()

        for ln in lns_to_suppress:
            spec.info_for_line_[ln].suppress = True

        spec.info_for_line_[op_info_ln].afters.append(oi)

        oi.line_num = op_info_ln

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def something_sdo(s):
    assert s.section_kind == 'syntax_directed_operation'

    # get parameters
    param_dict = OrderedDict()
    for (param_name, param_punct) in s.ste['parameters'].items():
        if param_name == '_argumentsList_':
            param_type = 'List'
        else:
            param_type = 'TBD'

        if param_punct == '[]':
            param_type = '(optional) ' + param_type
        else:
            assert param_punct == '', param_punct

        param_dict[param_name] = param_type

    op_name = s.ste['op_name']

    if op_name == 'TV and TRV':
        # defines two sdo's in the same section, hrm
        declare_sdo('TV', param_dict)
        declare_sdo('TRV', param_dict)
    elif op_name == 'regexp-Evaluate':
        declare_sdo(op_name, param_dict, regexp_also)
    else:
        declare_sdo(op_name, param_dict)

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
]

# ----------------------------

spec.oi_for_sdo_ = {}

def declare_sdo(op_name, param_dict, also=[]):
    oi = OperationInfo()
    oi.kind = 'syntax-directed operation'
    oi.name = op_name
    oi.for_phrase = 'Parse Node'
    oi.param_names = list(param_dict.keys())
    oi.param_nature_ = param_dict
    oi.also = also

    if op_name == 'regexp-Evaluate':
        assert oi.param_names == [] or oi.param_names == ['_direction_']
        oi.param_names = ['_direction_']
        oi.param_nature_ = OrderedDict( [('_direction_', 'integer')] )
        # oi.optional_params.add('_direction_') no, because then get (Integer_ | not_passed) when expect Integer_

    if op_name in spec.oi_for_sdo_:
        pre_oi = spec.oi_for_sdo_[op_name]
        assert pre_oi.param_names == oi.param_names
        assert pre_oi.param_nature_ == oi.param_nature_
        assert pre_oi.also == oi.also
    else:
        spec.oi_for_sdo_[op_name] = oi

class AnnexForSDOs:

    def lines(self, ind):
        # ignore `ind`
        yield ''
        yield '<emu-annex id="sec-headers-for-sdos">'
        yield '  <h1>Headers for Syntax-Directed Operations</h1>'
        yield '  <p>blah</p>'
        for (_, oi) in sorted(spec.oi_for_sdo_.items()):
            oi.finalize()
            for line in oi.lines('  '):
                yield line
        yield '</emu-annex>'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_for_im(s, hoi, preamble_text):
    oi = hoi
    oi.kind = 'internal method'

    pst = s.parent.section_title
    oi.for_phrase = {
        'Ordinary Object Internal Methods and Internal Slots' : 'ordinary object',
        'ECMAScript Function Objects'                         : 'ECMAScript function object',
        'Built-in Function Objects'                           : 'built-in function object',
        'Bound Function Exotic Objects'                       : 'bound function exotic object',
        'Array Exotic Objects'                                : 'Array exotic object',
        'String Exotic Objects'                               : 'String exotic object',
        'Arguments Exotic Objects'                            : 'arguments exotic object',
        'Integer-Indexed Exotic Objects'                      : 'Integer-Indexed exotic object',
        'Module Namespace Exotic Objects'                     : 'module namespace exotic object',
        'Immutable Prototype Exotic Objects'                  : 'immutable prototype exotic object',
        'Proxy Object Internal Methods and Internal Slots'    : 'Proxy exotic object',
    }[pst]

    assert preamble_text

    ptext = preamble_text

    patterns = [
        r'the (?P<name>\[\[\w+\]\]) internal method of a (?P<thing>bound function exotic object), (?P<thing_var>_F_),? (?:that|which) was created using the bind function\b',
        r'The (?P<name>\[\[\w+\]\]) internal method (?:for|of) an (?P<thing>arguments exotic object)\b',
        r'the (?P<name>\[\[\w+\]\]) internal method of (?P<thing_var>_\w+_)\b',
        r'[Tt]he (?P<name>\[\[\w+\]\]) internal method (?:for|of) (?:an? )?(?P<thing>[^_]+ object) (?P<thing_var>_\w+_)\b',
        # r'^the (\[\[\w+\]\]) internal method of an? ([^_]+) (_\w+_)\b',
    ]
    for pattern in patterns:
        mo = re.search(pattern, ptext)
        if mo:
            d = mo.groupdict()

            assert d['name'] == oi.name

            if 'thing' in d:
                assert d['thing'] == oi.for_phrase
            else:
                assert oi.for_phrase == 'ordinary object'

            if 'thing_var' in d:
                thing_var = d['thing_var']
            else:
                assert d['thing'] == 'arguments exotic object'
                thing_var = '_args_'
            oi.for_phrase += ' ' + thing_var
            #
            ptext = preamble_text[0:mo.start()] + 'OP' + preamble_text[mo.end():]
            break
    else:
        assert 0, ptext

    # -----------

    patterns = [
        r'^When OP is called, the following steps are taken:$',
        r'^When OP is called with (?P<pl>.+), the following steps are taken:$',
        r'^OP when called with (?P<pl>.+) performs the following steps:$',
        r'^OP is called with parameters (?P<pl>.+)\. The following steps are taken:$',
        r'^OP is called with parameters (?P<pl>_argumentsList_ and _newTarget_). (?=The steps performed)'
    ]
    for pattern in patterns:
        mo = re.match(pattern, ptext)
        if mo:
            d = mo.groupdict()
            if 'pl' in d:
                get_im_params(oi, d['pl'])
            else:
                assert oi.param_names == []
            ptext = ptext[0:mo.start()] + ptext[mo.end():]
            break

    oi.description = ptext

    return oi

def get_im_params(oi, listing):
    listing = sub_many(listing, [
        (r'(_argumentsList_), (a List)', r'\1 \2'),
        (r'(_argumentsList_) and (_newTarget_)\. _argumentsList_ is (a possibly empty List of ECMAScript language values)', r'\1 which is \3 and \2'),
    ])

    assert oi.param_nature_  == {}

    param_names = []
    for piece in re.split(', and |, | and ', listing):
        (param_name, param_nature) = im_param_map[piece]
        param_names.append(param_name)
        oi.param_nature_[param_name] = param_nature

    assert param_names == oi.param_names

im_param_map = {
    'ECMAScript language value _Receiver_' : ('_Receiver_',      'Tangible_'),
    'Property Descriptor _Desc_'           : ('_Desc_',          'Property Descriptor'),
    '_newTarget_'                          : ('_newTarget_',     'TBD'),
    '_thisArgument_'                       : ('_thisArgument_',  'TBD'),
    '_argumentsList_'                      : ('_argumentsList_', 'List of Tangible_'),
    'a list of arguments _argumentsList_'  : ('_argumentsList_', 'List of Tangible_'),
    'argument _V_'                         : ('_V_',             'TBD'),
    'parameters _thisArgument_'            : ('_thisArgument_',  'TBD'),
    'property key _P_'                     : ('_P_',             'property key'),
    'a property key _P_'                   : ('_P_',             'property key'),
    'value _V_'                            : ('_V_',             'Tangible_'),
    '_argumentsList_ a List of ECMAScript language values' :
        ('_argumentsList_', 'List of Tangible_'),
    '_argumentsList_ which is a possibly empty List of ECMAScript language values':
        ('_argumentsList_', 'List of Tangible_'),
}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_for_nm(s, hoi, preamble_text):
    if preamble_text == '':
        oi = hoi
        oi.kind = 'numeric_method'
    else:
        poi = OperationInfo()
        poi.kind = 'numeric_method'

        if RE.fullmatch(r'The abstract operation (Number|BigInt)(::\w+) (.+)', preamble_text):
            (poi.for_phrase, poi.name, rest) = RE.groups()

            if RE.fullmatch(r'converts a (Number|BigInt) (_x_) to String format as follows:', rest):
                poi.param_names = ['_x_']
                poi.param_nature_['_x_'] = RE.group(1)
                poi.description = 'converts _x_ to String format'

            elif RE.fullmatch(r"with an argument _x_ of type (BigInt) (returns the one's complement of _x_; that is, -_x_ - 1).", rest):
                poi.param_names = ['_x_']
                poi.param_nature_['_x_'] = RE.group(1)
                poi.description = RE.group(2)

            elif RE.fullmatch(r'with( two)? arguments _x_ and _y_ of type (Number|BigInt) performs the following steps:', rest):
                poi.param_names = ['_x_', '_y_']
                poi.param_nature_['_x_'] = RE.group(2)
                poi.param_nature_['_y_'] = RE.group(2)

            elif RE.fullmatch(r"with two arguments _x_ and _y_ of type (BigInt) (returns (a|the) BigInt (value that represents|representing) .+)\.", rest):
                poi.param_names = ['_x_', '_y_']
                poi.param_nature_['_x_'] = RE.group(1)
                poi.param_nature_['_y_'] = RE.group(1)
                poi.returns_normal = 'BigInt'
                poi.description = RE.group(2)

            elif RE.fullmatch(r"with two arguments _x_ and _y_ of type (BigInt) (returns \*true\* .+)\.", rest):
                poi.param_names = ['_x_', '_y_']
                poi.param_nature_['_x_'] = RE.group(1)
                poi.param_nature_['_y_'] = RE.group(1)
                poi.returns_normal = 'Boolean'
                poi.description = RE.group(2)

            else:
                assert 0, rest

        else:
            poi.description = preamble_text.strip()

        oi = resolve_oi(hoi, poi)

    return oi

# ------------------------------------------------------------------------------

def get_info_for_cm(s, hoi, preamble_text):

    oi = hoi
    oi.kind = 'concrete method'

    pst = s.parent.section_title
    if pst.endswith((' Environment Records', ' Scope Records')): # PR 1477 scope-records
        oi.for_phrase = pst[0].lower() + pst[1:-1]
    elif pst in ['Source Text Module Records', 'Cyclic Module Records']:
        oi.for_phrase = pst[0:-1]
    else:
        assert 0, pst

    # A CM's preamble needn't be that detailed about its parameters,
    # because the interface is declared elsewhere.
    #
    # While the 'elsewhere' info should properly be extracted from the spec,
    # I've hardcoded it below.

    # pd = predeclared
    (pd_param_names, pd_param_nature_, return_type) = predeclared_rec_method_info[oi.name]

    assert oi.param_names == pd_param_names
    oi.param_nature_ = pd_param_nature_

    for subtype in return_type.split(' | '):
        if subtype.startswith('throw'):
            assert oi.returns_abrupt is None
            oi.returns_abrupt = subtype
        else:
            if oi.returns_normal is None:
                oi.returns_normal = ''
            else:
                oi.returns_normal += ' | '
            oi.returns_normal += subtype

    if preamble_text:

        patterns = [
            r'^The (\w+) concrete method of a ((?:Cyclic|Source Text) Module Record) ',
            r'^The concrete Environment Record method (\w+) for (\w+ Environment Record)s ',
        ]
        for pattern in patterns:
            mo = re.search(pattern, preamble_text)
            if mo:
                (name, for_phrase) = mo.groups()
                assert name == oi.name
                assert for_phrase == oi.for_phrase
                ptext = re.sub(pattern, '', preamble_text)
                break
        else:
            ptext = preamble_text

        ptext = sub_many(ptext, [
            (r'(?:the )?Boolean argument (_D_|_S_)', r'\1'),
            (r'_M_ is a Module Record, and ', r''),
            (r'^with arguments _exportName_, and _resolveSet_ ', ''),
            (r'^implements the corresponding (Module Record|Cyclic Module Record) abstract method\. ', ''),
            (r'^performs the following steps:$', r''),
            (r'^It performs the following steps.$', ''),
            (r' ?This abstract method performs the following steps.$', ''),
            (r' This abstract method performs the following steps \(most of the work (.+)\):$',
                r' (Most of the work \1.)'),
            (':$', '.'),
        ])

        oi.description = ptext

    return oi

# ------------------------------------------------------------------------------

rec_method_declarations = '''
    BindThisValue(V) -> TBD
    CanDeclareGlobalFunction(N) -> Boolean
    CanDeclareGlobalVar(N) -> Boolean
    CreateGlobalFunctionBinding(N, V, D) -> TBD
    CreateGlobalVarBinding(N, D) -> TBD
    CreateImmutableBinding(N, S) -> TBD
    CreateImportBinding(N, M, N2) -> TBD
    CreateMutableBinding(N, D) -> TBD
    DeleteBinding(N) -> Boolean
    GetBindingValue(N, S) -> throw_ *ReferenceError*
    GetSuperBase() -> Object | Null | Undefined
    GetThisBinding() -> Tangible_ | throw_ *ReferenceError*
    HasBinding(N) -> Boolean
    HasLexicalDeclaration(N) -> Boolean
    HasRestrictedGlobalProperty(N) -> Boolean
    HasSuperBinding() -> Boolean
    HasThisBinding() -> Boolean
    HasVarDeclaration(N) -> Boolean
    InitializeBinding(N, V) -> TBD
    SetMutableBinding(N, V, S) -> throw_ *TypeError*
    WithBaseObject() -> Object | Undefined
    GetExportedNames(exportStarSet) -> List of String
    ResolveExport(exportName, resolveSet) -> ResolvedBinding Record | Null | String
    Link() -> TBD
    Evaluate() -> TBD
    InitializeEnvironment() -> TBD
    ExecuteModule() -> TBD
'''

rec_method_parameter_types = {
    '_D_' : 'Boolean',
    '_M_' : 'Module Record',
    '_N_' : 'String',
    '_N2_': 'String',
    '_S_' : 'Boolean',
    '_V_' : 'Tangible_',
    '_exportStarSet_' : 'TBD',
    '_exportName_'    : 'String',
    '_resolveSet_'    : 'TBD',
}

predeclared_rec_method_info = {}
for line in re.split(r'\n +', rec_method_declarations.strip()):
    mo = re.match(r'^(\w+)\(([^()]*)\) -> (.+)$', line)
    assert mo, line
    (name, params_str, return_type) = (mo.groups())
    if params_str == '':
        param_names = []
    else:
        param_names = [
            ('_' + name + '_')
            for name in params_str.split(', ')
        ]
    param_nature_ = dict(
        (param_name, rec_method_parameter_types[param_name])
        for param_name in param_names
    )
    predeclared_rec_method_info[name] = (param_names, param_nature_, return_type)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_for_ao(s, hoi, preamble_text):
    if preamble_text == '':
        oi = hoi
        oi.kind = 'abstract operation'
    else:
        poi = get_info_from_ao_preamble(preamble_text)
        oi = resolve_oi(hoi, poi)
    return oi

# ------------------------------------------------------------------------------

def get_info_from_ao_preamble(preamble_text):

    # if 'thisBooleanValue' in preamble_text: pdb.set_trace()

    oi = OperationInfo()
    oi.kind = 'abstract operation'

    # ----------------------------------------------------------------
    # Handle the Memory Model abstract operations first,
    # because they're so different.

    mo = re.fullmatch(r'A candidate execution (_execution_) has (.+) if the following abstract operation returns \*true\*.', preamble_text)
    if mo:
        oi.name = mo.group(2)
        oi.param_names = ['_execution_']
        oi.param_nature_['_execution_'] = 'a candidate execution'
        oi.description = preamble_text
        return oi

    mo = re.fullmatch(r'For an execution (_execution_), two events (_E_) and (_D_) in SharedDataBlockEventSet\(_execution_\) are in a (.+) if the following abstract operation returns \*true\*.', preamble_text)
    if mo:
        oi.name = mo.group(4)
        oi.param_names = ['_execution_', '_E_', '_D_']
        oi.param_nature_['_execution_'] = 'a candidate execution'
        oi.param_nature_['_E_'] = 'a Shared Data Block event'
        oi.param_nature_['_D_'] = 'a Shared Data Block event'
        oi.description = preamble_text
        return oi

    # ----------------------------------------------------------------

    mo = re.fullmatch(r'The abstract operation (<dfn [^<>]+>(this\w+Value)</dfn>)\(_value_\) performs the following steps:', preamble_text)
    if mo:
        (dfn_element, ao_name) = mo.groups()
        oi.name = ao_name
        oi.param_names = ['_value_']
        oi.description = dfn_element
        return oi

    # ----------------------------------------------------------------
    # Ascertain the name of the operation.

    namers = [
        r'[Tt]he (\w+) abstract operation',
        r'[Tt]he abstract operation ([\w/:]+)',
        r'The internal comparison abstract operation (\w+)',
        r'The job (\w+)',
        r'^(\w+DeclarationInstantiation)',
        r'The (UTF16Encoding)',
        r'A (TopLevelModuleEvaluationJob)',
        r'(?<=When )(CreateResolvingFunctions)',
        r'^(Host\w+)',
        r'^(IsSharedArrayBuffer)\b',
        r'^(LocalTZA)\([^()]*\)',
        r'the (TypedArray SortCompare) abstract operation',
    ]
    for pattern in namers:
        mo = re.search(pattern, preamble_text)
        if mo:
            oi.name = mo.group(1)
            ptext = re.sub(pattern, 'OP', preamble_text)

            # occasionally the op_name is repeated later in the preamble:
            ptext = re.sub(' (?!UTC)' + oi.name + r'\b', ' OP', ptext)
            # Require the preceding space because:
            #    when oi.name is 'Call', we don't want to change "[[Call]]";
            #    ditto 'Construct'
            # Avoid 'UTC' because it's the name of an op and also
            # an acronym used in the description of that op.

            break
    else:
        ptext = preamble_text

    # ----------------------------------------------------------------
    # Before we split the preamble into sentences,
    # deal with some things that wouldn't be handled well by that.

    ptext = sub_many(ptext, [

        # 7.2.11 Abstract Relational Comparison
        # split a sentence:
        ('(The comparison .+ or \*undefined\*) \(which (indicates .+)\).',
            r'\1. Returning *undefined* \2.'),

        # 7.2.11 Abstract Relational Comparison
        # copy param name from one sentence to the next
        ('(In addition) to _x_ and _y_ (the algorithm takes a Boolean flag named _LeftFirst_ as a parameter.) The (flag is used to .+)',
            r'\1 \2 The _LeftFirst_ \3'),

        # 15.2.1.18 HostResolveImportedModule
        # 15.2.1.19 HostImportModuleDynamically
        (r'(the Script Record or Module Record) (_referencingScriptOrModule_)\. (\(?\2 may also be \*null\*)',
            r'\1 or *null* \2. \3'),

    ])

    # ----------------------------------------------------------------
    # Split the preamble text into sentences.
    # Attempt to extract different kinds of info from each sentence.

    for sentence in re.split('(?<=\.) ', ptext):
        # if sentence == 'Otherwise, it returns *undefined*.': pdb.set_trace()
        s = sentence
        for extractor in [
            extract_parameter_info_from_ao_preamble,
            extract_also_info_from_ao_preamble,
            extract_returns_info_from_ao_preamble,
            skip_uninformative_from_ao_preamble,
        ]:
            s = extractor(oi, s)
            if s == '': break

        if s:
            add_to_description(oi, s)

    # ----------------------------------------------------------------
    # Cheat: Add some 'also' info that doesn't appear in the preamble.

    if oi.name in [
        'WordCharacters',
        'IsWordChar',
        'CharacterSetMatcher',
        'Canonicalize',
        'RegExpBuiltinExec',
        'CharacterRangeOrUnion',
        'BackreferenceMatcher',
    ]:
        # 21.2.2.1 Notation says:
        # "The descriptions below use the following variables:"
        assert oi.also is None
        oi.also = regexp_also

    if oi.name == 'TypedArray SortCompare':
        # "SortCompare has access to the _comparefn_ and _buffer_ values
        # of the current invocation of the `sort` method."
        # The sentence appears at the end of the preceding para,
        # but I don't want to include that whole para in the preamble.
        assert oi.also is None
        oi.also = [
            ('_comparefn_', 'from the `sort` method'),
            ('_buffer_',    'from the `sort` method'),
        ]

    return oi

# ------------------------------------------------------------------------------

def extract_parameter_info_from_ao_preamble(oi, sentence):

    # First, handle cases where the sentence has both parameter info
    # and other useful content.
    # We need to disentangle those, and return the non-parameter info.

    if '_i_ a byte offset' in sentence: stderr('epi', sentence)

    for (pattern, r1, r2) in [

        # 7.1.12.1 NumberToString
        (r'OP converts (a Number _m_) (to String format as follows:)',
            r'OP takes \1.',
            r'OP converts a Number \2'),

        # 7.2.2 IsArray
        # 21.1.3.17.1 SplitMatch
        # 21.2.2.5.1 RepeatMatcher
        (r'(OP takes .+), and (performs.+)',
            r'\1.',
            r'OP \2'),

        # 7.2.3 IsCallable
        # 7.2.4 IsConstructor
        # 7.2.7 IsPropertyKey
        ('(OP determines if _argument_), which must be (an ECMAScript language value), (is .+)',
            r'OP takes \2 _argument_.',
            r'\1 \3'),

        # 7.2.5 IsExtensible
        (r'(OP is used to .+ to) the object that is _O_.',
            r'_O_ is an object.',
            r'\1 an object.'),

        # 7.2.9 IsStringPrefix
        (r'OP determines if (String _p_) is a prefix of String _q_.',
            r'OP is called with String _p_ and String _q_.',
            r'OP determines if _p_ is a prefix of _q_.'),

        # 7.2.9 SameValue
        # 7.2.10 SameValueZero
        # SameValueNonNumber
        (r'OP\((.+)\), where (.+), (produces .+)',
            r'OP is called with \1, where \2.',
            r'OP \3'),

        # 7.2.11 Abstract Relational Comparison
        # 7.2.12 Abstract Equality Comparison
        # 7.2.13 Strict Equality Comparison
        (r'The (comparison _x_ \S+ _y_), (where _x_ and _y_ are values), (produces .+)',
            r'OP is called with _x_ and _y_, \2.',
            r'OP implements the \1, and \3'),

        # 7.3.13 Construct
        (r'((_argumentsList_) and (_newTarget_) are the values to be passed as the corresponding arguments of the internal method.)',
            r'\2 is a List of values and \3 is a value.',
            r'\1'),

        # 7.3.17 CreateListFromArrayLike
        ('(OP is used to .+ of an array-like object), _obj_.',
            r'OP takes object _obj_.',
            r'\1.'),
        (r'((The optional argument _elementTypes_ is a List) containing the names of ECMAScript Language Types that are allowed for element values of the List that is created.)',
            r'\2 of ECMAScript Language Type names.',
            r'\1'),

        # 7.3.19 OrdinaryHasInstance
        (r'(OP implements .+ if an object _O_ inherits from the instance object inheritance path provided by constructor _C_.)',
            r'OP takes a constructor _C_ and an object _O_.',
            r'\1'),

        # 7.3.20 SpeciesConstructor
        (r'(OP is used to .+ from the) argument object _O_\.',
            r'OP takes an argument object _O_.',
            r'\1 object _O_.'),
        (r'(The _defaultConstructor_ argument is the constructor to use .+)',
            r'_defaultConstructor_ is a constructor.',
            r'\1'),

        # 8.3.1 ResolveBinding
        (r'(OP is used to determine the binding of _name_) passed as a String value.',
            r'_name_ is a String value.',
            r'\1.'),
        (r'(The optional argument _env_ can be used to explicitly provide the Lexical Environment .+\.)',
            r'_env_ is an optional Lexical Environment.',
            r'\1'),

        # 9.1.13 ObjectCreate
        # 9.1.14 OrdinaryCreateFromConstructor
        # 9.3.3 CreateBuiltinFunction
        # 9.4.5.7 IntegerIndexedObjectCreate
        (r'(The((?: optional)?)(?: argument)? (_\w+SlotsList_) is a List of the names of additional internal slots that .+)',
            r'\3 is a\2 List of slot-names.',
            r'\1'),

        # 9.4.2.2

        # 9.4.4.7.1 MakeArgGetter
        # 9.4.4.7.2 MakeArgSetter
        (r'OP (called with String _name_ and Environment Record _env_) (creates .+)',
            r'OP is \1.',
            r'OP \2'),

        # 10.1.1
        (r'OP of a numeric code point value, _cp_, is determined as follows:',
            r'OP takes a numeric code point value _cp_.',
            r'_cp_ is a numeric code point value.'),

        # 10.1.2 UTF16Decode
        (r'(Two code units), (_lead_) and (_trail_), (that form a UTF-16 .+) by performing the following steps:',
            r'OP takes a code unit \2 and a code unit \3.',
            r'\1 \4.'),

        # 10.1.3 CodePointAt
        (r'OP interprets (a String _string_) (as .+ at index _position_)\.',
            r'OP takes \1 and an index _position_.',
            r'OP interprets _string_ \2.'),

        # 12.9.4 InstanceofOperator
        (r'OP\((.+)\) (implements .+ ECMAScript value _V_ .+ object _target_ .+.)',
            r'OP is called with \1 where _V_ is an ECMAScript value and _target_ is an object.',
            r'OP \2'),

        # 13.12.9 CaseClauseIsSelected
        (r'OP, given (.+), (determines .+)',
            r'OP is called with \1.',
            r'OP \2'),

        # 15.2.1.16.4.1 InnerModuleInstantiation
        (r'(OP is used by Instantiate to perform the actual instantiation process for the Source Text Module Record _module_, as well as recursively on all other modules in the dependency graph.)',
            r'OP is called with Module Record _module_',
            r'\1'),

        # 15.2.1.18 HostResolveImportedModule
        # 15.2.1.19 HostImportModuleDynamically
        (r'(OP is .+ to the \|ModuleSpecifier\| String, _specifier_, .+ by) the (Script Record or Module Record or \*null\*) (_referencingScriptOrModule_)\.',
            r'OP is called with a \2 \3 and a String _specifier_.',
            r'\1 \3.'),

        # 18.2.6.1.1 Encode
        # 18.2.6.1.2 Decode
        (r'The (.+ process) is described by OP taking (.+)',
            r'OP takes \2.',
            r'OP describes the \1.'),

        # 20.3.1.12
        (r'(OP calculates a number of milliseconds from its four arguments), which must be ECMAScript Number values.',
            r'OP takes an ECMAScript Number value _hour_, an ECMAScript Number value _min_, an ECMAScript Number value _sec_, and an ECMAScript Number value _ms_.', # assumed param names
            r'\1.'),

        # 20.3.1.13
        (r'(OP calculates a number of days from its three arguments), which must be ECMAScript Number values.',
            r'OP takes an ECMAScript Number value _year_, an ECMAScript Number value _month_, and an ECMAScript Number value _date_.', # assumed param names
            r'\1.'),

        # 20.3.1.14
        (r'(OP calculates a number of milliseconds from its two arguments), which must be ECMAScript Number values.',
            r'OP takes an ECMAScript Number value _day_, and an ECMAScript Number value _time_.', # assumed param names
            r'\1.'),

        # 20.3.1.15
        (r'(OP calculates a number of milliseconds from its argument), which must be an ECMAScript Number value.',
            r'OP takes an ECMAScript Number value _time_.', # assumed param name
            r'\1.'),

        # 21.1.3.27.1 TrimString
        (r'(OP is called with arguments .+), and interprets the String value (_string_ as .+)',
            r'\1, where _string_ is a String value.',
            r'OP interprets \2'),

        # 24.??? UnicodeEscape
        (r'(OP takes a code unit argument _C_) and represents it (as a Unicode escape sequence.)',
            r'\1.',
            r'OP represents _C_ \2'),

        # 23.4.1.3 GetWaiterList

        # AllocateTypedArrayBuffer
        (r'OP with arguments _O_ and _length_ (allocates and associates an ArrayBuffer with) the (TypedArray instance) _O_.',
            r'OP takes a TypedArray instance _O_ and _length_.',
            r'OP \1 a \2.'),

        # 25.4.1.5 NewPromiseCapability
        (r'(OP takes a constructor function, and attempts .+)',
            r'OP takes a constructor function _C_.', # assumed param name
            r'\1'),

        # 25.4.1.8 TriggerPromiseReactions
        (r'(OP takes a collection of PromiseReactionRecords) and (enqueues a new Job for each record)\.',
            r'\1 _reactions_.',
            r'OP \2 in _reactions_.'),

        # general
        (r'OP with (.+?) ((allocates|applies|creates|configures|converts|has access to|is a job that|is used|parses,|requests|serializes|wraps) .+)',
            r'OP takes \1.',
            r'OP \2'),

        # -------------------------------
        # concrete methods

        (r'If(?: the)? (Boolean argument) (_\w+_) has (.+)',
            r'OP takes \1 \2.',
            r'If \2 has \3'),

        (r'(.+ the value of) the (Boolean argument) (_\w+_)\.',
            r'OP takes \2 \3.',
            r'\1 \3.'),

        # (r'(.+ whose name is the value of the argument _N_\.)',
        #     r'OP takes String _N_.', # a bit klugey
        #     r'\1'),

    ]:
        fullmatch_pattern = '^(?:' + pattern + ')$'
        mo = re.match(fullmatch_pattern, sentence)
        if mo:
            s = extract_parameter_info_from_ao_preamble(oi, mo.expand(r1))
            assert s == '', s
            return mo.expand(r2)

    # ----------------

    # At this point, we assume that the sentence contains
    # either *no* parameter info, or *only* parameter info.

    mo = fullmatch_any(sentence, [

        r'OP with (?P<pl>.*arguments.*of type BigInt):', # syntactically odd
        r'OP called with (?P<pl>.+) performs the following steps:',
        r'OP is a recursive abstract operation that takes (?P<pl>.+)',
        r'OP is called with (?P<pl>.+?),? where (?P<ps>.+)',
        r'OP is called with (?P<pl>.+)',
        r'OP is performed as follows using arguments (?P<pl>.+)',
        r'OP requires (?P<pl>.+)',
        r'OP takes (?P<pl>.+?),? and performs the following steps:',
        r'OP takes (?P<pl>.+)\.',
        r'OP accepts (?P<pl>.+), with _target_ as the receiver\.', # AddEntriesFromIterable
        r'OP with (?P<pl>.+) (performs the following steps|is performed as follows|is defined by the following steps):',
        r'The operation is called with arguments (?P<pl>.+) where (?P<ps>.+)',
        r'When OP is called with (?P<pl>.+?),? the following steps are (performed|taken):',
        r'When OP is called, the following steps are taken:',
        r'When OP is performed with (?P<pl>.+), the following steps are taken:',
        r'When OP with (?P<pl>.+) is called, the following (occurs|steps are taken):',
        r'When called with (?P<pl>.+), the following steps are taken:',
        r'Conversion occurs according to the following algorithm:',
        #
        # r'(?P<ps>If (?!_LeftFirst_)_\w+_ .+)',
        r'(?P<ps>In addition the algorithm takes .+)',
        r'(?P<ps>The argument _\w+_ is .+)',
        r'(?P<ps>The arguments _\w+_ and _\w+_ must be .+)',
        r'(?P<ps>The optional( argument)? _\w+_ is .+)',
        r'(?P<ps>The value of _\w+_ .+)',
        r'(?P<ps>_\w+_ (is|must be) .+)',

    ])
    if mo:
        gd = mo.groupdict()
        get_info_from_parameter_listing_in_preamble(oi, gd.get('pl', ''))
        get_info_from_parameter_sentence_in_ao_preamble(oi, gd.get('ps', ''))
        return ''
    else:
        return sentence

# ------------------------------------------------------------------------------

def get_info_from_parameter_sentence_in_ao_preamble(oi, parameter_sentence):
    # if '_C_' in parameter_sentence: stderr('gifps', parameter_sentence)

    if parameter_sentence == '': return

    if parameter_sentence in [
        'neither _x_ nor _y_ are Number values.',
        'neither _x_ nor _y_ are numeric type values.',
    ]:
        add_to_description(oi, parameter_sentence)
        oi.param_nature_['_x_'] = 'a value'
        oi.param_nature_['_y_'] = 'a value'
        return

    # tweak things that would react poorly to the subsequent split
    param_sentence2 = sub_many(parameter_sentence, [
        # Case where we don't want to split on comma:
        ('present, _F_',
            'present,  _F_'), # inserting an extra space is a bit subtle

        # Cases where we don't want to split on "and":
        ('The arguments _tag_ and _attribute_ must be String values',
            '_tag_ is a String value and _attribute_ is a String value'),
        ('_x_ and _y_ are values',
            r'_x_ is a value and _y_ is a value'),
        ('_x_ and _y_ are (ECMAScript language value)s',
            r'_x_ is an \1 and _y_ is an \1'),

        (r'\.$', ''),
    ])

    var_pattern = r'\b_\w+_\b'

    for clause in re.split(r'(?:, and|,| and) (?=_\w+_)', param_sentence2):
        mo = re.search(var_pattern, clause)
        assert mo, clause
        param_name = mo.group(0)

        vclause = re.sub(r'\b' + param_name + r'\b', 'VAR', clause)

        if 'optional' in vclause:
            oi.optional_params.add(param_name)
            # vclause = re.sub(' optional ', ' ', vclause)

        for (pattern, param_nature_clause) in [

            (  r'VAR is a List containing the actual argument values that ',
                'VAR is a List of values'),
            (  r'VAR is an ECMAScript language value that ',
                'VAR is an ECMAScript language value'),
            (  r'VAR is the Lexical Environment in which ',
                'VAR is a Lexical Environment'),
            (  r'VAR is the Property Descriptor for ',
                'VAR is a Property Descriptor'),
            (  r'VAR is the constructor function that ',
                'VAR is a constructor'),
            (  r'VAR is the constructor that ',
                'VAR is a constructor'),
            (  r'VAR is the function object for which ',
                'VAR is a function object'),
            (  r'VAR is the global lexical environment in which ',
                'VAR is a global lexical environment'),
            (  r'VAR is the Parse Node corresponding to ',
                'VAR is a Parse Node'),
            (  r'VAR is the list of arguments values passed to ',
                'VAR is a List of values'),
            (  r'VAR is the new value for the property',
                'VAR is a value'),
            (  r'VAR is the value for the property',
                'VAR is a value'),
            (  r'VAR is the value passed to the corresponding argument of the internal method',
                'VAR is a List of values'), # Call()
            (  r'VAR is the value to be passed as ',
                'VAR is a value'),
            (  r'VAR is the \|ScriptBody\| for which the execution context is being established',
                'VAR is a |ScriptBody|'),
            (  r'VAR serves as both the lookup point for the property and ',
                'VAR is a value'),
            (  r'VAR is required to be the name of a TypedArray constructor in <emu-xref href="#table-[^"]+"></emu-xref>',
                'VAR is a String'),

        ]:
            mo = re.match(pattern, vclause)
            if mo:
                add_to_description(oi, clause + '.')
                vclause = param_nature_clause
                break

        if oi.param_names and param_name in oi.param_names:
            # The preamble has previously 'declared' this parameter.
            current_nature = oi.param_nature_[param_name]
            if current_nature == 'TBD':
                new_nature = sub_many(vclause, [
                    ('^VAR is required to be ', ''),
                    ('^VAR is ', ''),
                    ('^VAR serves as both', 'both'),
                    ('^The value of VAR is ', ''),
                ])
            else:
                new_nature = current_nature + '; ' + sub_many(vclause, [
                    ('^The value of VAR may be ', 'or may be '),
                ])

            oi.param_nature_[param_name] = new_nature

        else:
            # The preamble has not previously 'declared' this parameter,
            # and yet it now mentions it in a way
            # that is normally only used when we've already declared it.
            nature = sub_many(vclause, [
                ('^The argument VAR is ', ''),
                ('^The optional(?: argument)? VAR is ', ''),
                ('^In addition the algorithm takes (a Boolean flag) named VAR as a parameter', r'\1'),
                ('^VAR is an? optional ', 'a '),
                ('^VAR (?:is|must be) ', ''),
                ('an optional Lexical', 'a Lexical'),
            ])

            if oi.param_names is None: oi.param_names = []

            oi.param_names.append(param_name)
            oi.param_nature_[param_name] = nature

# ------------------------------------------------------------------------------

def extract_also_info_from_ao_preamble(oi, sentence):
    if sentence == 'It also has access to the _comparefn_ argument passed to the current invocation of the `sort` method.':
        oi.also = [ ('_comparefn_', 'the _comparefn_ argument passed to the current invocation of the `sort` method') ]
        return ''
    elif sentence == 'OP uses the value of _reviver_ that was originally passed to the above parse function.':
        oi.also = [ ('_reviver_', 'the value of _reviver_ that was originally passed to the above parse function') ]
        return ''
    elif sentence == 'OP has access to _ReplacerFunction_ from the invocation of the `stringify` method.':
        oi.also = [ ('_ReplacerFunction_', 'from the invocation of the `stringify` method') ]
        return ''
    elif sentence == 'It has access to the _stack_, _indent_, _gap_, and _PropertyList_ values of the current invocation of the `stringify` method.':
        oi.also = [
            ('_stack_',        'from the current invocation of the `stringify` method'),
            ('_indent_',       'from the current invocation of the `stringify` method'),
            ('_gap_',          'from the current invocation of the `stringify` method'),
            ('_PropertyList_', 'from the current invocation of the `stringify` method'),
        ]
        return ''
    elif sentence == 'It has access to the _stack_, _indent_, and _gap_ values of the current invocation of the `stringify` method.':
        oi.also = [
            ('_stack_',        'from the current invocation of the `stringify` method'),
            ('_indent_',       'from the current invocation of the `stringify` method'),
            ('_gap_',          'from the current invocation of the `stringify` method'),
        ]
        return ''
    else:
        return sentence

# ------------------------------------------------------------------------------

def extract_returns_info_from_ao_preamble(oi, sentence):
    for (pattern, normal, abrupt, rest) in [

        # sentence only contains info re return.
        (r'A Boolean value is returned\.',
            r'a Boolean Value', '', ''),
        (r'OP produces (.+)\.',
            r'\1', '', ''),

        # sentence contains info re return and non-return.
        (r'OP performs the following steps in order to return (either \*false\* or the end index of a match):',
            r'*false* or an integer index', '', r'OP returns \1.'),

        (r'(OP implements .+), and produces (.+)\.',
            r'\2', '', r'\1.'),
        (r'(OP returns a built-in function object created by the following steps:)',
            r'a function object', '', r'OP creates a built-in function object.'),

        (r'(It throws a \*TypeError\* exception if .+)',
            '', 'throw *TypeError*', r'\1'),
        (r'(It throws an exception if .+)',
            '', 'throw', r'\1'),
        (r'(.+ in a manner that will throw a \*TypeError\* exception .+)',
            '', 'throw *TypeError*', r'\1'),

        # 7.4.5 IteratorStep
        (r'(OP requests .+ and returns either \*false\* indicating .+ or the IteratorResult object if .+\.)',
            '*false* or an IteratorResult object', '', r'\1'),

        # 25.4.1.5 NewPromiseCapability
        (r'(The promise plus the resolve and reject functions are used to initialize a new PromiseCapability Record) which is returned as the value of this abstract operation.',
            'a PromiseCapability Record', '', r'\1.'),
    ]:
        fullmatch_pattern = '^(?:' + pattern + ')$'
        mo = re.match(fullmatch_pattern, sentence)
        if mo:
            if normal: oi.returns_normal = mo.expand(normal)
            if abrupt: oi.returns_abrupt = mo.expand(abrupt)
            return mo.expand(rest)
    else:
        return sentence

# ------------------------------------------------------------------------------

def skip_uninformative_from_ao_preamble(oi, sentence):
    if sentence in [
        'During execution of ECMAScript code, OP is performed using the following algorithm:',
        'It performs the following steps:',
        'Its algorithm is as follows:',
        'OP performs the following steps:',
        'Such a comparison is performed as follows:',
        'The following steps are performed:',
        'The following steps are taken:',
        'This abstract operation functions as follows:',
        'This abstract operation performs the following steps:',
        'This operation performs the following steps:',
        'This operator functions as follows:',
        'When called, the following steps are performed:',
    ]:
        return ''
    else:
        return sentence

# ------------------------------------------------------------------------------

def add_to_description(oi, sentence):

    if oi.description is None:
        oi.description = sub_many(sentence, [
            ('^OP is an ', 'an '),
            ('^OP,? ', ''),
            ('^It ', ''),
            ('^This operation ', ''),
            (' as follows:$', ''),
            (' by performing the following steps:$', ''),
            (' created by the following steps:$', ''),
            (':$', '.'),
        ])
    else:
        oi.description += ' ' + sub_many(sentence, [
            ('^OP ', 'This operation '),
            (' OP ', ' this operation '),
            (' by performing the following steps:$', '.'),
        ])

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_for_builtin_function(s, op_kind, hoi, preamble_text):

    if op_kind == 'accessor_property':
        # For an accessor property, the preamble is unusual,
        # so don't call 
        # get_info_from_builtin_function_preamble(s, preamble_text)
        # (Alternatively, I could modify that function.)

        oi = hoi
        oi.kind = 'accessor property'

        if preamble_text == 'The value of the [[Get]] attribute is a built-in function that requires no arguments. It performs the following steps:':
            pass
        elif preamble_text == 'The value of the [[Set]] attribute is a built-in function that takes an argument _proto_. It performs the following steps:':
            oi.param_names = ['_proto_']
            oi.param_nature_['_proto_'] = 'a value'
        else:
            mo = re.fullmatch(r'(\S+) is an accessor property whose set accessor function is \*undefined\*. Its get accessor function performs the following steps:', preamble_text)
            assert mo, repr(preamble_text)
            op_name_plus_ticks = mo.group(1)
            assert (
                re.fullmatch(r'%TypedArray%`[^`]+`', op_name_plus_ticks)
                or
                re.fullmatch(r'`[^`]+`', op_name_plus_ticks)
            )
            op_name = op_name_plus_ticks.replace('`', '')
            assert 'get ' + op_name == oi.name.replace(' [ ', '[').replace(' ]', ']')

    # ----------------------------------------------------
    else:

        poi = get_info_from_builtin_function_preamble(s, op_kind, preamble_text)

        if op_kind.endswith('_overload'):

            if poi.overload_resolver is None:
                # klugey fix
                assert hoi.name == '%TypedArray%.prototype.set'
                emu_alg_text = s.block_children[1].inner_source_text()
                mo = re.search(r'\s+1. Assert: (.+?)\. ', emu_alg_text)
                asserted_condition = mo.group(1)
                if asserted_condition == '_array_ is any ECMAScript language value other than an Object with a [[TypedArrayName]] internal slot':
                    poi.overload_resolver = asserted_condition.replace('_array_', 'the first argument')
                    poi.param_nature_['_array_'] = 'a value'
                elif asserted_condition == '_typedArray_ has a [[TypedArrayName]] internal slot':
                    poi.overload_resolver = 'the first argument is an Object with a [[TypedArrayName]] internal slot'
                    poi.param_nature_['_typedArray_'] = 'an Integer-Indexed object'
                else:
                    assert 0, asserted_condition

            elif poi.overload_resolver == 'at least one argument and the Type of the first argument is not Object':
                assert hoi.param_names == ['_length_']
                poi.param_nature_['_length_'] = 'a primitive value'

            elif poi.overload_resolver == 'at least one argument and the Type of the first argument is Object and that object has a [[TypedArrayName]] internal slot':
                assert hoi.param_names == ['_typedArray_']
                poi.param_nature_['_typedArray_'] = 'an Integer-Indexed object'

            elif poi.overload_resolver == 'at least one argument and the Type of the first argument is Object and that object has an [[ArrayBufferData]] internal slot':
                assert hoi.param_names[0] == '_buffer_'
                poi.param_nature_['_buffer_'] = 'an ArrayBuffer or SharedArrayBuffer'

            elif poi.overload_resolver == 'at least one argument and the Type of the first argument is Object and that object does not have either a [[TypedArrayName]] or an [[ArrayBufferData]] internal slot':
                assert hoi.param_names == ['_object_']
                poi.param_nature_['_object_'] = 'an object'

            elif poi.overload_resolver in [
                'no arguments',
                'exactly one argument',
                'at least two arguments',
            ]:
                # doesn't narrow any paramter types
                pass
            else:
                assert 0, poi.overload_resolver

        oi = resolve_oi(hoi, poi)

        if oi.param_names is None:
            assert oi.name in ['Proxy Revocation', 'ListIteratorNext']
            oi.param_names = []

        if s.section_title.startswith('Math.'):
            # "Each of the following `Math` object functions
            # applies the ToNumber abstract operation
            # to each of its arguments
            # (in left-to-right order if there is more than one)."
            #
            # So the algorithms are written under the assumption
            # that the parameters have type 'Number'.
            default_nature = 'a Number'
        else:
            default_nature = 'a value'
        for name in oi.param_names:
            if oi.param_nature_.get(name, None) in [None, 'TBD']:
                oi.param_nature_[name] = default_nature

        if 0:
            hoi.description = '? '+ preamble_text

    # ----------------------------------------------------

    return oi

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_builtin_function_preamble(s, op_kind, preamble_text):
    poi = OperationInfo()
    poi.kind = op_kind

    if preamble_text in [
        '',
        'The following steps are taken:',
        'The following steps are performed:',
    ]:
        return poi

    mo = re.match(r'^Given zero or more arguments, (calls ToNumber on each of the arguments and returns the \w+est of the resulting values.)$', preamble_text)
    if mo:
        poi.returns_normal = 'a Number'
        poi.description = mo.group(1)
        return poi

    if preamble_text.startswith('This description applies'):
        (preamble_text, group_dict) = re_sub_many_etc(preamble_text, [
            (r'^This description applies( if and)? only if the (Date constructor|Array constructor|_TypedArray_ function) is called with (?P<X>.+?)\. ?', ''),
        ])
        poi.overload_resolver = group_dict['X']

    preamble_text = re.sub(' +The following steps are taken:$', '', preamble_text)
    preamble_text = re.sub(' +It performs the following steps:$', '', preamble_text)

    # Not sure if I should make this change in the spec:
    # because the preamble has later imperatives.
    preamble_text = re.sub('^Return ', 'Returns ', preamble_text)

    for (pattern, return_nature) in [
        (r'^Returns an implementation-dependent approximation to', 'a Number'),
        (r'^Returns an Array object',                              'an Array object'),
        (r'^Returns a new _TypedArray_ object',                    'a TypedArray object'),
        (r'^Returns (a|the) Number value',                         'a Number'),
        (r'^Returns the (absolute value|smallest|greatest|sign|integral part)', 'a Number'),
        (r'^Returns a String containing',                          'a String'),
        (r'^Performs .+ and returns an Array object .+, or \*null\*', 'an Array object or *null*'),
        (r'^Produces a String value',                                 'a String'),
    ]:
        if re.match(pattern, preamble_text):
            poi.returns_normal = return_nature
            poi.description = preamble_text
            return poi

    # simplify subsequent processing:
    preamble_text = preamble_text.replace('%TypedArray%`.prototype', '`%TypedArray%.prototype')

    for pattern in [
        r'\bthe `(@@hasInstance)` method of an object _F_',
        # Theoretically, we'd have to grab the _F_ and put that somewhere in the eoh,
        # but the algorithm starts with "Let _F_ be the *this* value.",
        # so it doesn't actually need the 'declaration' of _F_ in the preamble.

        r'^(_TypedArray_)(?= called with)',

        r'^The (%TypedArray%) constructor\b',
        r'^The (ListIterator `next`) method\b',
        r'^The <dfn>(%ThrowTypeError%)</dfn> intrinsic\b',
        #
        r'^The `([\w.]+)` function\b',
        r'^The `(\w+)` method\b',
        r'(?<= )The `([\w.]+)` function\b',
        r'(?<= )The `(\w+)` method\b',
        r'(?<=^When )`([\w.]+)`(?= is called)',
        r'(?<= When )`([\w.]+)`(?= is called)',
        r'(?<= When )(%ThrowTypeError%)(?= is called)',
        #
        r'\ba _NativeError_ function\b',
        r'\bthe `(\w+)` function\b',
        r'\bthe `(\w+)` method\b',
        r'\bthe `(@@\w+)` method\b',
        r'^`([\w.%]+)`(?= (?:puts|notifies|returns|is)\b)',
        #
        r'\b(?:A|a|Each) (`Promise.(all|allSettled)` (resolve|reject) element) function\b',
        r'\b(?:A|a|An|an|Each) (?!standard|anonymous)([\w -]+?) function\b',
        #
        # no name:
        r'^This function\b',
    ]:
        def replfunc(mo):
            if mo.groups():
                extracted_name = mo.group(1)
                if poi.name is None:
                    poi.name = extracted_name
                    return 'IT'
                elif extracted_name == poi.name:
                    return 'IT'
                elif extracted_name == 'async iterator value unwrap':
                    oh_warn(f"'{extracted_name}' != '{poi.name}'")
                    return 'IT'
                else:
                    return mo.group(0)
            else:
                return 'IT'

        preamble_text = re.sub(pattern, replfunc, preamble_text)

    if op_kind == 'anonymous_built_in_function':
        preamble_text = sub_many(preamble_text, [
            (r'^IT is an anonymous built-in function( object)? that ', 'IT '),
            (r'^IT is an anonymous function that ', 'IT '),
            (r'^IT is a standard built-in function object \(.+\) that ', 'IT '),
            (r'^IT is an anonymous built-in function with ', 'IT has '),
            (r'^IT is an anonymous built-in function\. ', ''),
        ])

    if preamble_text in [
        'When IT is called, the following steps are taken:',
        'IT performs the following steps:',
    ]:
        return poi

    (preamble_text, group_dict) = re_sub_many_etc(preamble_text, [
        (r' These are the steps in stringifying an object:$', ''),
        (r'^When called with (?P<PL>.+), it performs the following steps:$', ''),
        (r' When IT is called with (?P<PL>.+), the following steps are taken:$', ''),
        (r' When IT is called with (?P<PL>.+) it performs the following steps:$', ''),
        (r' When IT is called, the following steps are taken:$', ''),
        (r' When IT is called it performs the following steps:$', ''),
        (r' When IT that expects (?P<PL>.+) is called it performs the following steps:$', ''),
        (r'^When IT is called with (?P<PL>.+), the following steps are taken:$', ''),
        (r'^When IT is called with (?P<PL>.+?),? it performs the following steps:$', ''),
        (r'^IT takes (?P<PL>.+), and performs the following steps:$', ''),
        (r'^IT is called with (?P<PL>one or two arguments, _predicate_ and _thisArg_)\.', ''),
        (r'^IT called with (?P<PL>.+?) performs the following steps:$', ''),

        (r'^When IT is called it returns', 'IT returns'),
        (r'^When IT is called with (?P<PL>.+), it returns', 'IT returns'),
        (r'^IT takes (?P<PL>.+?), and returns', 'IT returns'),
    ])
    if 'PL' in group_dict:
        get_info_from_parameter_listing_in_preamble(poi, group_dict['PL'])

    if preamble_text == '': return poi

    if re.match(r'^IT (returns|produces|provides) ', preamble_text):
        mo = re.match(r'IT (returns|produces|provides) (a Number|a String|a promise|a new promise|a substring|an Iterator object|an array|an implementation-dependent approximation of the square root|an integer|either a new promise)', preamble_text)
        assert mo, preamble_text
        r = mo.group(2)
        poi.returns_normal = {
            'an implementation-dependent approximation of the square root': 'a Number',
            'either a new promise': 'a new promise'
        }.get(r, r)

    if op_kind == 'anonymous_built_in_function':
        expansion = ' Each function created with this algorithm '
    else:
        expansion = ' This function '
    poi.description = sub_many(preamble_text, [
        ('^IT ', ''),
        (' IT ', expansion),
    ])

    # poi.description = '? ' + preamble_text

    return poi

# ------------------------------------------------------------------------------

def re_sub_many_etc(subject, pattern_repls):

    group_dict = {}

    for (pattern, repl) in pattern_repls:

        def replfunc(mo):
            for (name, value) in mo.groupdict().items():
                assert name not in group_dict
                group_dict[name] = value
            return repl

        subject = re.sub(pattern, replfunc, subject)

    return (subject, group_dict)


# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_heading(section):
    oi = OperationInfo()

    if section.section_kind in [
        'catchall',
        'changes',
    ]:
        return oi

    if section.section_kind in [
        'abstract_operation',
        'syntax_directed_operation',
        'env_rec_method',
        'module_rec_method',
        'internal_method',
        'numeric_method',
    ]:
        oi.name = section.ste['op_name']

    elif section.section_kind in [
        'function_property',
        'function_property_overload',
        'accessor_property',
        'CallConstruct',
        'CallConstruct_overload',
        'anonymous_built_in_function',
    ]:
        oi.name = section.ste['prop_path']

    else:
        assert 0, section.section_kind

    if section.section_kind == 'numeric_method':
        oi.for_phrase = re.sub(':.*', '', section.section_title)
        # Should this be in section.ste?

    if 'parameters' not in section.ste:
        return oi

    oi.param_names = []

    for (param_name, param_punct) in section.ste['parameters'].items():
    
        oi.param_names.append(param_name)

        if param_punct == '...':
            oi.rest_params.add(param_name)
        elif param_punct == '[]':
            oi.optional_params.add(param_name)
        elif param_punct == '':
            pass
        else:
            assert 0, param_punct

    return oi

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_parameter_listing_in_preamble(oi, parameter_listing):

    # if '_C_' in parameter_listing: stderr('gifpl', parameter_listing)

    if parameter_listing == '':
        return

    if parameter_listing == 'no arguments':
        oi.param_names = []
        return

    if parameter_listing in [
        'zero or more arguments _item1_, _item2_, etc.',
        'zero or more arguments',
        'any number of arguments',
        'one or two arguments',
        'zero or one arguments',
    ]:
        # XXX not sure what to do
        return

    if parameter_listing == 'one or two arguments, _predicate_ and _thisArg_':
        oi.param_names = ['_predicate_', '_thisArg_']
        oi.optional_params.add('_thisArg_')
        return

    elif parameter_listing in [
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no &ldquo; _p_ &rdquo; arguments, and where _body_ might also not be provided)',
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no &ldquo;_p_&rdquo; arguments, and where _body_ might also not be provided)',
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no "_p_" arguments, and where _body_ might also not be provided)',
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no _p_ arguments, and where _body_ might also not be provided)',
    ]:
        oi.param_names = ['_args_', '_body_']
        oi.param_nature_['_args_'] = 'list of values'
        oi.param_nature_['_body_'] = 'a value'
        oi.optional_params.add('_body_')
        return

    elif parameter_listing  == 'at least one argument _buffer_':
        # kludgey
        if oi.name == '_TypedArray_':
            oi.param_names = ['_buffer_', '_byteOffset_', '_length_']
            oi.optional_params.add('_byteOffset_')
            oi.optional_params.add('_length_')
        elif oi.name == 'DataView':
            oi.param_names = ['_buffer_', '_byteOffset_', '_byteLength_']
            oi.optional_params.add('_byteOffset_')
            oi.optional_params.add('_byteLength_')
        else:
            assert 0, oi.name
        return

    # --------------------

    # InternalizeJSONProperty
    if parameter_listing == 'two parameters: a _holder_ object and the String _name_ of a property in that object.':
        parameter_listing = 'an object _holder_ and a String _name_'
        add_to_description(oi, '_name_ is the name of a property in _holder_.')

    param_listing = sub_many(parameter_listing, [
        (r'\.$', ''),

        ( r'^\((.+)\)$', r'\1' ),
        ( r'&lt;|===|==', 'and' ),

        # pre-handle cases that would give bad results when we split on comma and 'and'...

        # un-elide
        ('(two )?arguments _x_ and _y_ of type BigInt', r'BigInt _x_ and BigInt _y_'),
        ('(argument _obj_) and (optional argument)s (_hint_) and (_method_)', r'\1 and \2 \3 and \2 \4'),
        ('(optionally) (_argumentsList_), and (_newTarget_)', r'\1 \2 and \1 \3'),
        ('(optionally), (a Boolean _writablePrototype_) and (an object _prototype_)', r'\1 \2 and \1 \3'),
        ('Two code units, _lead_ and _trail_', 'code unit _lead_ and code unit _trail_'),
        (', and (Property Descriptor)s (_Desc_), and (_[Cc]urrent_)', r', \1 \2, and \1 \3'),
        ('two (CharSet) parameters (_A_) and (_B_)', r'\1 \2 and \1 \3'),
        (r'two (String) arguments (_string_) and (_\w+_)', r'\1 \2 and \1 \3'),
        (r'two parameters (_p_) and (_v_), each of which is (a List of Unicode code points)', r'\3 \1 and \3 \2'),
        (r'(optional argument)s (_mapfn_) and (_thisArg_)', r'\1 \2 and \1 \3'), # Array.from

        ('optionally, ', 'optionally '),
        (' and with ', ' and '),
        ('(a Lexical Environment)( as)? argument (_E_)', r'\1 \3'),
        (' as its argument$', ''),
        ('(a Parse Node), (_templateLiteral_), as an argument$', r'\1 \2'),
        (' as arguments$', ''),
        (r'(a nonnegative), (non-\*NaN\* Number)', r'\1 \2'),

        # parameter(s):
        ('^parameters ', ''),
        ('^(three|four|five|six|seven|eight) parameters, ', ''),
        ('^two parameters: ', ''),
        # argument(s):
        ('^argument ', ''),
        ('^one argument,? ', ''),
        ('^arguments ', ''),
        ('^as arguments ', ''),
        ('^the arguments: ', ''),
        ('^the argument ', ''),
        ('^two arguments,? ', ''),
        ('^the two arguments ', ''),
        ('^the three arguments ', ''),
        ('^three arguments[:,] ', ''),
        ('^four arguments, ', ''),

        ('which is one of \(`"normal"`, .+?\)', 'which is a String'),

        ('one of \(~key~, ~value~, ~key\+value~\)',  'one_of_key_value_key+value'),
        ('one of \(~SeqCst~, ~Unordered~\)',         'one_of_SeqCst_Unordered'),
        ('one of \(~SeqCst~, ~Unordered~, ~Init~\)', 'one_of_SeqCst_Unordered_Init'),

        (r'\(Normal, ', '(Normal<comma> '),
        (r'Method, Arrow\)', 'Method<comma> Arrow)'),
        (r'\(~Normal~, ', '(~Normal~<comma> '),
        (r'~Method~, ~Arrow~\)', '~Method~<comma> ~Arrow~)'),
        # (The commas will be reinstated below.)
    ])

    param_items = re.split(', and |, | and ', param_listing)

    var_pattern = r'\b_\w+_\b'

    assert oi.param_names is None, oi.name

    oi.param_names = []
    for param_item in param_items:
        mo = re.search(var_pattern, param_item)
        assert mo, param_item
        param_name = mo.group(0)

        assert param_name not in oi.param_names, param_name
        oi.param_names.append(param_name)

        if param_item == 'zero or more _args_':
            # XXX how to represent 'zero or more'?
            continue

        (param_item2, n) = re.subn(r'\b(optionally|(an )?optional( argument)?) ', '', param_item)
        if n == 0:
            # no mention of optionality
            pass
        else:
            assert n == 1
            oi.optional_params.add(param_name)

        nature = sub_many(param_item2, [

            # a few special cases that wouldn't be well-handled by the generic patterns:
            ('^an argument _argumentsList_$', ''), # CreateUnmappedArgumentsObject
            (r'^an _input_ argument$', ''), # ToPrimitive

            # We don't need to repeat that this is an argument/parameter.
            (r' argument ', ' '),

            # We don't need to repeat the variable name:
            (r'\b' + param_name + r'\b', 'VAR'),
            (r'^a parameter VAR that is ', ''),
            (r'^VAR which is ', ''),
            (r'^VAR ', ''),
            (r'^VAR$', ''),
            (r' specified by VAR$', ''),
            (r'^an VAR$', ''),
            (r' VAR$', ''),

            # Eliminate 'parameter' from "a character parameter" and "an integer parameter",
            # but not from "a parameter list Parse Node".
            (r' parameter$', ''),

            # Undo the comma-protecting hack above:
            (r'<comma>', ','),

            # If what remains is parenthesized, drop the parentheses:
            (r'^\((.+)\)$', r'\1'),

            # Prepend "a" or "an" as appropriate:
            # ('(?i)^(?!an? |one |the |either )(?=[aeiou])', r'an '),
            # ('(?i)^(?!an? |one |the |either )(?=[^aeiou])', r'a '),

            # If the remainder is empty, use "TBD".
            ('^$', 'TBD'),
        ])

        oi.param_nature_[param_name] = nature

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class OperationInfo:
    def __init__(self):
        self.kind = None
        self.name = None
        self.for_phrase = None
        self.overload_resolver = None
        self.param_names = None
        self.optional_params = set()
        self.rest_params = set()
        self.param_nature_ = {}
        self.also = None
        self.returns_normal = None
        self.returns_abrupt = None
        self.description = None
        self.definitions = []
        self.line_num = None

    def finalize(self):
        assert len(self.rest_params) in [0,1]

        self.parameters = OrderedDict()
        for param_name in self.param_names:
            optionality = '(optional) ' if param_name in self.optional_params else ''

            if param_name in self.rest_params:
                assert param_name not in self.optional_params
                if self.name.startswith('Math.'):
                    typ = 'List of Number'
                else:
                    typ = 'List of Tangible_'
            else:
                nature = self.param_nature_.get(param_name, 'TBD')
                typ = convert_nature_to_typ(nature)

            param_type = optionality + typ

            self.parameters[param_name] = param_type

        self.return_type_normal = convert_nature_to_typ(self.returns_normal or 'TBD')
        self.return_type_abrupt = convert_nature_to_typ(self.returns_abrupt or 'TBD')

    def lines(self, ind):
        lines = []
        def p(s): lines.append(ind + s)

        p("<emu-operation-header>")
        p("  op kind: " + self.kind)
        p("  name: " + self.name)

        if self.for_phrase:
            p("  for: " + self.for_phrase)

        if self.overload_resolver:
            p("  overload selected when called with: " + self.overload_resolver)

        assert self.parameters is not None
        if len(self.parameters) == 0:
            p("  parameters: none")
        else:
            p("  parameters:")

            maxwidth = max(len(param_name) for param_name in self.parameters.keys())
            for (param_name, param_type) in self.parameters.items():
                p("    - " + param_name.ljust(maxwidth) + ' : ' + param_type)

        if self.also:
            p("  also has access to:")
            maxwidth = max(len(var_name) for (var_name,_) in self.also)
            for (var_name, expl) in self.also:
                p("    - %s : %s" % (var_name.ljust(maxwidth), expl))

        p("  returns:")
        p("    - normal : " + self.return_type_normal)
        p("    - abrupt : " + self.return_type_abrupt)

        if self.description:
            p("  description: " + self.description)

        p("</emu-operation-header>")

        return lines

def resolve_oi(hoi, poi):
    if poi is None:
        # no preamble, so just use info from heading
        return hoi

    oi = OperationInfo()

    # kind
    assert hoi.kind is None
    assert poi.kind is not None
    oi.kind = poi.kind

    # name
    if hoi.name is None and poi.name is None:
        assert 0
    elif hoi.name is None:
        # Only happens for ops/functions that are "hidden"
        # within a section that is about something else.
        oi.name = poi.name
    else:
        # We prefer to use the heading-name:
        oi.name = hoi.name
        # ... but we also check that it's consistent with the preamble-name, if any:
        if (
            poi.name is None
            or
            hoi.name == poi.name
            or
            hoi.name.endswith('.' + poi.name)
            or
            hoi.name.endswith(f'.prototype [ {poi.name} ]')
            or
            hoi.name.lower() == poi.name.lower()
        ):
            pass
        else:
            oh_warn()
            oh_warn(f'resolve_oi: name in heading ({hoi.name}) != name in preamble ({poi.name})')

    # for_phrase
    if hoi.for_phrase and poi.for_phrase:
        assert hoi.for_phrase == poi.for_phrase
        oi.for_phrase = hoi.for_phrase
    elif hoi.for_phrase:
        oi.for_phrase = hoi.for_phrase
    else:
        oi.for_phrase = poi.for_phrase # which might or might not be None

    # overload_resolver
    assert hoi.overload_resolver is None
    oi.overload_resolver = poi.overload_resolver # might or might not be None

    # param_names
    if hoi.param_names is None:
        # assert poi.param_names is not None
        oi.param_names = poi.param_names
        oi.optional_params = poi.optional_params
        oi.rest_params = poi.rest_params
    elif poi.param_names is None:
        assert hoi.param_names is not None
        oi.param_names = hoi.param_names
        oi.optional_params = hoi.optional_params
        oi.rest_params = hoi.rest_params
    else:
        # neither is None

        # When the heading contains a signature,
        # it's deemed authoritative:
        oi.param_names = hoi.param_names
        oi.optional_params = hoi.optional_params
        oi.rest_params = hoi.rest_params

        if hoi.param_names != poi.param_names and oi.name not in [
            'OrdinaryCreateFromConstructor',
            'TriggerPromiseReactions',
        ]:
            oh_warn()
            oh_warn(oi.name, 'has param name mismatch:')
            oh_warn(hoi.param_names)
            oh_warn(poi.param_names)
        else:
            if hoi.optional_params != poi.optional_params:
                oh_warn()
                oh_warn(oi.name, 'has param optionality mismatch:')
                oh_warn('h:', sorted(list(hoi.optional_params)))
                oh_warn('p:', sorted(list(poi.optional_params)))

        assert not poi.rest_params

    assert hoi.param_nature_ == {} # heading never has type info
    oi.param_nature_ = poi.param_nature_

    assert hoi.also is None
    oi.also = poi.also

    assert hoi.returns_normal is None
    oi.returns_normal = poi.returns_normal

    assert hoi.returns_abrupt is None
    oi.returns_abrupt = poi.returns_abrupt

    assert hoi.description is None
    oi.description = poi.description

    return oi

# --------------------------------------------------------------------

def convert_nature_init():
    global un_f
    un_f = shared.open_for_output('unconverted_natures')

def convert_nature_to_typ(nature):
    if nature == 'TBD': return 'TBD'

    t = nature_to_typ.get(nature, None)
    if t is not None: return t

    print(nature, file=un_f)
    return nature

nature_to_typ = {
    # ------------------------------
    # ECMAScript language types

        # Undefined

        # Null

        # Boolean
        'Boolean'           : 'Boolean',
        'Boolean value'     : 'Boolean',
        'a Boolean'         : 'Boolean',
        'a Boolean Value'   : 'Boolean',
        'a Boolean flag'    : 'Boolean',
        '*true* or *false*' : 'Boolean',

        # String
        'String'          : 'String',
        'a String'        : 'String',
        'a String value'  : 'String',
        'a substring'     : 'String',

        # Symbol

        # Number
        'Number'                     : 'Number',
        'a Number'                   : 'Number',
        'an ECMAScript Number value' : 'Number',
        'a nonnegative non-*NaN* Number' : 'Number', # XXX loses info

        # BigInt
        'BigInt'      : 'BigInt',

        # Object
        'Object'      : 'Object',
        'an Object'   : 'Object',
        'an object'   : 'Object',
        'object'      : 'Object',
        'the object'  : 'Object',
        'a VAR object': 'Object',
        'an VAR of entries': 'Object', # this is kludgey: VAR is '_iterable_'

    # unofficial 'supertypes':
        'a primitive value'             : 'Primitive',

        'an ECMAScript language value'  : 'Tangible_',
        'the ECMAScript language value' : 'Tangible_',
        'ECMAScript language value'     : 'Tangible_',
        'an ECMAScript value'           : 'Tangible_',
        'ECMAScript value'              : 'Tangible_',
        'a value'                       : 'Tangible_',
        'the value'                     : 'Tangible_',
        'value'                         : 'Tangible_',
        'Tangible_'                     : 'Tangible_',

    # unofficial 'subtypes' of the above:
        # function_: an object with a [[Call]] internal method
        'a Function'          : 'function_object_',
        'a function object'   : 'function_object_',
        'function object'     : 'function_object_',
        'the function object' : 'function_object_',
        'an VAR function to be invoked': 'function_object_',

        # constructor_: an object with a [[Construct]] internal method
        'a constructor function' : 'constructor_object_',
        'a constructor'          : 'constructor_object_',

        # ArrayBuffer_: an object with an [[ArrayBufferData]] internal slot
        'an ArrayBuffer' : 'ArrayBuffer_object_',
        'an ArrayBuffer or SharedArrayBuffer' : 'ArrayBuffer_object_ | SharedArrayBuffer_object_',
        'a SharedArrayBuffer' : 'SharedArrayBuffer_object_',

        'a TypedArray instance' : 'TypedArray_object_',
        'a TypedArray object'   : 'TypedArray_object_',

        # 9.4.2
        'an Array exotic object' : 'Array_object_',
        'an Array object'        : 'Array_object_',
        'an array'               : 'Array_object_',

        'a promise' : 'Promise_object_',
        'a new promise': 'Promise_object_',

        'an Integer-Indexed object': 'Integer_Indexed_object_',

        # 25.1.1.3: IteratorResult_object_

        'an Iterator object': 'Iterator_object_',

        # it's unclear whether 'integer' is a subtype of 'Number',
        # or is mathematical integers
        'an integer length' : 'Integer_',
        'an integer offset' : 'Integer_',
        'an integer'        : 'Integer_',
        'integer'           : 'Integer_',
        'a numeric code point value'     : 'Integer_',
        'either 0 or a positive integer' : 'NonNegativeInteger_',
        'a nonnegative integer'          : 'NonNegativeInteger_',
        'nonnegative integer'            : 'NonNegativeInteger_',
        'an index'                       : 'NonNegativeInteger_',

    # ------------------------------
    # ECMAScript specification types

    # The ones enumerated in 6.2

        # Reference

        # List
        'List' : 'List',
        'a List' : 'List',
        'List of String': 'List of String',
        'a List of Unicode code points': 'List of Integer_',

        # Completion

        # Property Descriptor
        'Property Descriptor'   : 'Property Descriptor',
        'a Property Descriptor' : 'Property Descriptor',

        # Lexical Environment
        'a Lexical Environment' : 'Lexical Environment',
        'a global lexical environment' : 'Lexical Environment',

        # Environment Record
        'Environment Record' : 'Environment Record',
        'Scope Record' : 'Scope Record', # PR 1477 scope-records

        # Data Block
        'a Shared Data Block' : 'Shared Data Block',
        # is it a subtype of Data Block? Doesn't seem to be treated that way

    # official 'subtypes' of the above:
        # Object Environment Record
        # Declarative Environment Record

    # other 'declared' spec types:

        # 8.2 Realms: Realm Record
        'Realm Record' : 'Realm Record',

        # 8.3 Execution Contexts
        'execution context' : 'execution context',

        # 15.1.8 Script Records: Script Record

        # 15.2.1.15 Abstract Module Records: Module Record
        'a Module Record' : 'Module Record',
        'Module Record'   : 'Module Record',

        # 15.2.1.16 Source Text Module Records:
        # ImportEntry Record
        # ExportEntry Record

        # 21.2.2.1 Notation:
        # CharSet
            'CharSet'        : 'CharSet',
            'a CharSet'      : 'CharSet',
        # State
            'a State'        : 'State',
        # MatchResult
        # Continuation
            'a Continuation' : 'Continuation',
        # Matcher
            'a Matcher'      : 'Matcher',
        # AssertionTester

        # 24.4
        'a WaiterList' : 'WaiterList',

        # 27.4 Candidate Executions
        'a candidate execution': 'candidate execution',
        'a Shared Data Block event': 'Shared Data Block event',

        # 25.4.1.1: PromiseCapability Record 
        'a PromiseCapability Record': 'PromiseCapability Record',

        # 25.4.1.2: PromiseReaction Records

        # 27.1 Memory Model Fundamentals
        'a ReadSharedMemory or ReadModifyWriteSharedMemory event':
            'ReadSharedMemory event | ReadModifyWriteSharedMemory event',
        'a List VAR of WriteSharedMemory or ReadModifyWriteSharedMemory events':
            'List of (WriteSharedMemory event | ReadModifyWriteSharedMemory event)',

    # unofficial 'subtypes' of official spec types:

        'List of Tangible_'                        : 'List of Tangible_',
        'a List of values'                         : 'List of Tangible_',
        'a List of slot-names'                     : 'List of SlotName_',
        'a List of ECMAScript Language Type names' : 'List of LangTypeName_',
        'a collection of PromiseReactionRecords'   : 'List of PromiseReaction Record',

    # unofficial spec types

        'a code unit' : 'code_unit_',
        'a character' : 'character_',

        # 8.7.1 AgentSignifier
        'an agent signifier' : 'agent_signifier_',

        # 24.1.1.9 GetModifySetValueInBuffer
        'a semantic function'        : 'bytes_combining_op_',
        # 24.4.1.11 AtomicReadModifyWrite
        'a pure combining operation' : 'bytes_combining_op_',

        'a parameter list Parse Node'    : 'Parse Node',
        'a body Parse Node'              : 'Parse Node',
        'a Parse Node'                   : 'Parse Node',
        'Parse Node'                     : 'Parse Node',
        'the result of parsing an |AssignmentExpression| or |Initializer|' : 'Parse Node for |AssignmentExpression| | Parse Node for |Initializer|',
        'a |ScriptBody|'                 : 'Parse Node for |ScriptBody|',
        '|CaseClause|'                   : 'Parse Node for |CaseClause|',

        'one of (~Normal~, ~Method~, ~Arrow~)' : 'FunctionKind1_',
        'one of (~Normal~, ~Method~)'          : 'FunctionKind1_',
        # 'one of (Normal, Method, Arrow)'       : 'FunctionKind1_',
        # 'one of (Normal, Method)'              : 'FunctionKind1_',

        # 'either `"normal"` or `"generator"`'             : 'String', # 'FunctionKind2_',
        # 'either `"normal"`, `"generator"`, or `"async"`' : 'String', # 'FunctionKind2_',
        # 'either `"normal"`, `"generator"`, `"async"`, or `"async generator"`': 'String', # 'FunctionKind2_',
        'either ~normal~, ~generator~, ~async~, or ~asyncGenerator~' : 'FunctionKind2_',

        'either ~lexical-this~ or ~non-lexical-this~': 'this_mode2_',

        'either ~enumerate~ or ~iterate~' : 'IterationKind_',
        'either ~enumerate~, ~iterate~, or ~async-iterate~' : 'IterationKind_',

        'either ~sync~ or ~async~' : 'IteratorKind_',

        'either ~assignment~, ~varBinding~ or ~lexicalBinding~' : 'LhsKind_',

        'throw'             : 'throw_',
        'throw *TypeError*' : 'throw_ *TypeError*',
        'throw_ *TypeError*': 'throw_ *TypeError*',
        'throw_ *ReferenceError*': 'throw_ *ReferenceError*',

        'one of the ECMAScript specification types String or Symbol' : 'LangTypeName_',

        'a TypedArray element type'     : 'TypedArray_element_type_',
        'one_of_SeqCst_Unordered'       : 'SharedMemory_ordering_',
        'one_of_SeqCst_Unordered_Init'  : 'SharedMemory_ordering_',
        'one_of_key_value_key+value'    : 'iteration_result_kind_',

    # -----------------------------
    # union of named types

    'a BigInt or a Number'                                       : 'BigInt | Number',
    'a Number or BigInt'                                         : 'Number | BigInt',
    'an Array object or *null*'                                  : 'Array_object_ | Null',
    '*false* or an integer index'                                : 'Boolean | Integer_',
    '*false* or an IteratorResult object'                        : 'Boolean | IteratorResult_object_',
    '*true*, *false*, or *undefined*'                            : 'Boolean | Undefined',
    'an integer (or &infin;)'                                    : 'Integer_ | Infinity_',
    'a Lexical Environment; or may be *null*'                    : 'Lexical Environment | Null',
    'a Lexical Environment or *null*'                            : 'Lexical Environment | Null', # PR 1668
    'an object or null'                                          : 'Object | Null',
    'Object | Undefined'                                         : 'Object | Undefined',
    'Object | Null | Undefined'                                  : 'Object | Null | Undefined',
    'Property Descriptor (or *undefined*)'                       : 'Property Descriptor | Undefined',
    'ResolvedBinding Record | Null | String'                     : 'ResolvedBinding Record | Null | String',
    'a Script Record or Module Record or *null*'                 : 'Script Record | Module Record | Null',
    'a String or Symbol'                                         : 'String | Symbol',
    'a String or Symbol or Private Name'                         : 'String | Symbol | Private Name', # PR 1668
    'property key'                                               : 'String | Symbol',
    'the property key'                                           : 'String | Symbol',

}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

oh_inc_f = shared.open_for_output('oh_warnings')
def oh_warn(*args):
    print(*args, file=oh_inc_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def fullmatch_any(subject, patterns):
    # If any pattern in `patterns` is a fullmatch for `subject`,
    # return the resulting match-object (of the first such).
    for pattern in patterns:
        fullmatch_pattern = '^(?:' + pattern + ')$'
        mo = re.match(fullmatch_pattern, subject)
        if mo: return mo
    return None

def sub_many(subject, pattern_repls):
    # Apply each of `pattern_repls` to `subject`
    # and return the result.
    result = subject
    for (pattern, repl) in pattern_repls:
        result = re.sub(pattern, repl, result)
    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

main()

# vim: sw=4 ts=4 expandtab
