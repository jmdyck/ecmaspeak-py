#!/usr/bin/python3

# ecmaspeak-py/headers.py:
# This module is primarily concerned with making the version of the spec for PR 545,
# and will probably mostly disappear if/when that PR is merged.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re, pdb
from collections import OrderedDict, defaultdict

import shared
from shared import spec, stderr, RE, DL

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def generate_spec_for_PR_545():
    stderr("generate_spec_for_PR_545 ...")

    shared.prep_for_line_info()
    add_styling()

    global oh_inc_f
    oh_inc_f = shared.open_for_output('oh_warnings')

    for s in spec.root_section.each_descendant_that_is_a_section():
        create_operation_info_for_section(s)

    oh_inc_f.close()

    write_modified_spec()
    note_unused_rules()

# ------------------------------------------------------------------------------

def oh_warn(*args):
    print(*args, file=oh_inc_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def add_styling():
    # Hard-coding a line number is brittle,
    # but it'll probably work for as long as we need it to.
    spec.info_for_line_[4].afters.append(NewStyling())

class NewStyling:
    def lines(self, indentation, mode):
        return [
            '<style>',
            '  /* Eventually, styling for dl.header would move to ecmarkup.css. */',
            '  dl.header {',
            '    background: #CFC;',
            '  }',
            '  dl.header dt { font-weight: bold; }',
            '</style>',
        ]

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

    if s.section_kind == 'numeric_method':
        return True

    # -----------------------------

    # It's the kind of section that we usually want to create op info for,
    # but with some exceptions:

    if s.section_kind == 'env_rec_method':
        assert s.section_id in [
            'sec-object-environment-records-createimmutablebinding-n-s',
            'sec-module-environment-records-deletebinding-n',
        ]
        return False

    if s.section_kind == 'accessor_property':
        if s.section_title == 'Object.prototype.__proto__':
            # The section is just a holder for subsections
            # that define the 'get' and 'set' functions.
            return False
        else:
            assert 0, s.section_title
            return True

    if s.section_kind == 'function_property':

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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def create_operation_info_for_section(s):

    # There are a few cases where a section contains <emu-alg> elements,
    # but we don't want to create emu-operation-header elements for any of them,
    # because we can't really apply STA to them.

    if s.section_title in [
        'Algorithm Conventions',
        'Syntax-Directed Operations',
        'The Abstract Closure Specification Type',
    ]:
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

    # if s.section_title.startswith('String.prototype.localeCompare'):
        # The emu-alg in the section isn't the (full) alg for the function,
        # so don't connect them.
        # return


    if s.section_id in [
        'sec-regular-expression-patterns-semantics',
        'sec-initializers-in-forin-statement-heads',
        'sec-__proto__-property-names-in-object-initializers',
        'sec-IsHTMLDDA-internal-slot-to-boolean',
    ]:
        # Omnibus clauses in Annex B.
        # For now, skip them because they're too weird.
        return

    # ------------------------------------------------------

    if s.section_kind == 'syntax_directed_operation':
        # Rather than putting an EOH here
        # (one for every defn of the SDO),
        # we put one at the end, in annex C.
        something_sdo(s)
        return

    elif s.section_num == 'C':
        ln = get_last_ln(s)

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
        )
    ]

    n_algos = len(algo_child_posns)
    if n_algos == 0:
        # Even though the section has no algos,
        # we might want to create a header.
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

    elif s.section_title == '%TypedArray%.prototype.sort ( _comparefn_ )':
        assert n_algos == 2
        # The first algo is just a variant of the first few steps from Array.p.sort,
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

    # ==========================================================================

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

            'Apply the algorithm in',

            'The implementation of',                        # 15.2.1.17 Runtime Semantics: HostResolveImportedModule

            'An implementation of Host',                    # 16.1 HostReportErrors
                                                            # 18.2.1.2 HostEnsureCanCompileStrings
                                                            # 25.6.1.9 HostPromiseRejectionTracker

            'Most hosts will be able to simply define',     # HostFinalizeImportMeta

            'The Boolean prototype object:',
            'The Symbol prototype object:',
            'The Number prototype object:',
            'The BigInt prototype object:',
            'The Date prototype object:',
            'The String prototype object:',

            # PR 2065:
            'The <dfn>Boolean prototype object</dfn>:',
            'The <dfn>Symbol prototype object</dfn>:',
            'The <dfn>Number prototype object</dfn>:',
            'The <dfn>BigInt prototype object</dfn>:',
            'The <dfn>Date prototype object</dfn>:',
            'The <dfn>String prototype object</dfn>:',

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

    # ==========================================================================

    for (span_start_i, span_end_i) in pre_algo_spans:

        if n_algos == 0 or span_end_i == len(s.block_children):
            algo = None
        else:
            algo = s.block_children[span_end_i]
            assert algo.element_name in ['emu-alg', 'emu-table']

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

        else:
            # The op is *not* the one indicated by the section heading.
            # print(s.section_num, s.section_kind, 'isnt', span_end_i)
            hoi = AlgHeader()
            if s.section_title.startswith('MakeArgGetter'):
                pass
            elif s.section_title.startswith('MakeArgSetter'):
                pass
            elif s.section_title.startswith('%TypedArray%.prototype.sort'):
                pass
            elif s.section_title.startswith('Properties of the'):
                pass
            elif s.section_title == 'Array.prototype [ @@unscopables ]':
                hoi.name = 'initializer for @@unscopables'
                hoi.kind = 'abstract operation'
                hoi.param_names = []
            elif s.section_id in [
                'sec-regular-expression-patterns-semantics',
                'sec-initializers-in-forin-statement-heads',
            ]:
                # print('347', s.section_num, s.section_title)
                continue # XXX
            else:
                assert 0, s.section_title

        # -----------------------------------

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

        if p_start_i == 0:
            prev = s.heading_child
        else:
            prev = s.block_children[p_start_i-1]
        ln = get_last_ln(prev)

        if p_start_i == p_end_i:
            # no children in preamble, so no lines to suppress
            poi = None
        else:
            start_ln = get_first_ln(s.block_children[p_start_i])
            # end_ln = get_first_ln(s.block_children[p_end_i]) node might not exist
            end_ln = 1 + get_last_ln(s.block_children[p_end_i-1])
            for line_info in spec.info_for_line_[start_ln:end_ln]:
                line_info.suppress = True

            info_holder = extract_info_from_preamble(s.block_children[p_start_i:p_end_i], s)
            poi = info_holder.convert_to_header()

        # -----------------------------------

        oi = resolve_oi(hoi, poi)
        oi.finish_initialization()
        spec.info_for_line_[ln].afters.append(oi)
        if algo:
            if algo.element_name == 'emu-alg':
                if hasattr(algo, '_parent_algdefn'):
                    oi.add_defn(algo._parent_algdefn)
                else:
                    stderr(f"No _parent_algdefn for {algo}")
            else:
                assert algo.element_name in ['emu-table']
                assert not hasattr(algo, '_parent_algdefn')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def something_sdo(s):
    assert s.section_kind == 'syntax_directed_operation'

    # get parameters
    param_dict = OrderedDict()
    for (param_name, param_punct) in s.ste['parameters'].items():
        if param_name == '_argumentsList_':
            param_type = 'a List'
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
    ('_WordCharacters_'  , 'from somewhere'),
]

# ----------------------------

spec.oi_for_sdo_ = {}

def declare_sdo(op_name, param_dict, also=[]):
    oi = AlgHeader()
    oi.kind = 'syntax-directed operation'
    oi.name = op_name
    oi.for_phrase = 'Parse Node'
    oi.param_names = list(param_dict.keys())
    oi.param_nature_ = param_dict
    oi.also = also

    if op_name == 'regexp-Evaluate':
        assert oi.param_names == [] or oi.param_names == ['_direction_']
        oi.param_names = ['_direction_']
        oi.param_nature_ = OrderedDict( [('_direction_', '1 or -1')] )
        # oi.optional_params.add('_direction_') no, because then get (Integer_ | not_passed) when expect Integer_

    if op_name in spec.oi_for_sdo_:
        pre_oi = spec.oi_for_sdo_[op_name]
        assert pre_oi.param_names == oi.param_names
        assert pre_oi.param_nature_ == oi.param_nature_
        assert pre_oi.also == oi.also
    else:
        oi.finish_initialization()
        spec.oi_for_sdo_[op_name] = oi

        op_info = spec.alg_info_['op'][op_name]
        assert op_info.name == op_name
        assert op_info.species == 'op: syntax-directed'
        for alg_defn in op_info.definitions:
            if alg_defn.section.section_num.startswith('B'): continue
            if alg_defn.discriminator is None: continue # XXX for now
            oi.add_defn(alg_defn)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

multi_sentence_rules_str = r'''

        This (?P<kind>function) returns (?P<retn>a String value). The contents of the String (are .+)
        v=The contents of the returned String \3

        (`([][@\w.]+)` is an accessor property whose set accessor function is \*undefined\*.) Its get accessor function performs the following steps:
        name=get \2
        v= \1
        # A bit kludgey: Insert a space to prevent later match against /`(?P<name>[\w.]+)` (.+)/

        ((%TypedArray%)`([^`]+)` is an accessor property whose set accessor function is \*undefined\*.) Its get accessor function performs the following steps:
        name=get \2\3
        v= \1
        # Ditto re space

        (.+) In addition to (_x_ and _y_) the algorithm takes (a Boolean flag named _LeftFirst_) as a parameter. The flag is (.+)
        pl=\2 and \3
        v=\1 The _LeftFirst_ flag is \4
'''

single_sentence_rules_str = r'''

    # ==========================================================================
    # Sentences that start with "A" or "An"

        A (candidate execution (_\w+_)) (has .+) if the following (?P<kind>abstract operation) (returns \*true\*).
        pl=a \1
        v=\2 \3 if this operation \5.

        A (?P<name>.+) function is an (?P<kind>anonymous built-in function).

        (An? (?P<name>.+) function) is an (?P<kind>anonymous built-in function) that ((has|is) .+)
        v=!FUNC \4

        (An (?P<name>.+) function) is an (?P<kind>anonymous built-in function) with (\[\[.+)
        v=\1 has \4

    # ==========================================================================

        For (?P<pl>an execution _\w+_, two events (_\w_ and _\w_) in \S+) (are in a .+) if the following (?P<kind>abstract operation) (returns \*true\*).
        v=\2 \3 if this operation \5.

    # ==========================================================================
    # Sentences that start with "It"

        It can take three parameters.
        # could send to <ps>, but not helpful.

        It performs the following steps when called:

    # ==========================================================================

        Such a comparison is performed as follows:

    # ==========================================================================
    # Sentences that start with "The"

        # --------------

        The (comparison .+), where (?P<ps>_x_ and _y_ are values), produces (.+)
        v=!OP performs the \1, returning \3

        The following steps are performed:

        The following steps are taken:

        # ---------

        ((?P<ps>The optional _\w+_ value) indicates .+)
        v=\1

        # ---------

        # Don't match "The value of _separator_ may be a String of any length or it may be ..."
        # because it belongs in the description, is misleading for parameter-type.

        (The value of the \[\[\w+\]\] attribute is a built-in function) that (requires|takes) (?P<pl>no arguments|an argument _proto_).
        kind=accessor property

        # ---------

        The (?P<name>ResolveExport) (?P<kind>concrete method) of (?P<for>.+) takes (?P<pl>.+)\.

        The <dfn>(?P<name>[^<>]+)</dfn> intrinsic is an (?P<kind>anonymous built-in function object) that (?P<desc>is defined once for each realm.)

        The (?P<name>[%\w]+) (?P<kind>constructor) performs the following steps:

        # ------------

        The `(?P<name>[\w.]+)` (?P<kind>function|method) (.+)
        v=!FUNC \3

        `(?P<name>[\w.]+)` (.+)
        v=!FUNC \2

            !FUNC is called with (?P<pl>.+).

            !FUNC takes (?P<pl>.+), and performs the following steps:

            !FUNC takes (?P<pl>.+), and (returns .+)
            v=!FUNC \2

            !FUNC takes (?P<pl>.+).

            !FUNC performs the following steps:

    # ==========================================================================
    # Sentences that start with "This"

        # Note that none of these leave anything for the description.

        This (?P<kind>function) takes (?P<pl>no arguments).

        This function (.+)
        v=!FUNC \1

        This concrete method performs the following steps when called:

    # ==========================================================================
    # Sentences that start with "When"

        # (Ultimately, almost nothing falls through to the description.)

        # When the ...

        When the `(?P<name>Date)` (function) is called(.+)
        kind=constructor
        v=When it is called\3

        (When the `@@hasInstance` method) of an object _F_ (is called .+)
        v=\1 \2
        # convert anomalous syntax into syntax handled by next rule:

        When the `(?P<name>@*[\w.]+)` (?P<kind>function|method) is called(.+)
        v=When it is called\3

        # -----------------------------------------------------

        # When a|an ...

        When an? (?P<name>.+) function is called(.+)
        v=When it is called\2

        When an? (?P<name>.+) function that expects (?P<pl>.+) is called it performs the following steps:

        When a (?P<name>Default Constructor) Function is called with (?P<pl>zero or more arguments which form the rest parameter \.\.\._args_), the following steps are taken:

        # -----------------------------------------------------

        # When <name> ...

        When `(?P<name>[\w.]+)` is called(.+)
        v=When it is called\2

        When (?P<name>%\w+%) is called it performs the following steps:

        # -----------------------------------------------------

        When it is called with (?P<pl>.+?),? the following steps are (performed|taken):

        When it is called with (?P<pl>.+?),? it performs the following steps:

        When it is called, the following steps are taken:

        When it is called with (?P<pl>.+?),? it returns (.+)
        v=It returns \2

        When it is called it returns (.+)
        v=It returns \1

    # ==========================================================================
    # Sentences that start with the operation/function name:

        (?P<name>LocalTZA)\( _t_, _isUTC_ \) is an (?P<kind>implementation-defined algorithm) that (returns .+)
        v=!OP \3

    # ==========================================================================
    # Sentences that (now) start with "!OP":

        # !OP (.+)
        # v=The operation \1

    # ==========================================================================
    # Miscellaneous starts:

        Given (?P<pl>zero or more arguments), (calls ToNumber .+)
        v=!FUNC \2

        # (Don't extract parameter info ('ps') from env-rec preambles,
        # because you'll get lots of warnings re mismatches.)

        Specifically, perform the following steps:

        These are the steps in stringifying an object:

    # ==========================================================================
    # Sentences where we don't care how it starts:

        # ----------
        # produces ...

        (Produces (?P<retn>a String value) .+)
        v=\1

        (.+ produces (?P<retn>a Number value) .+)
        v=\1

        (.+ produces (?P<retn>an ECMAScript value).)
        v=\1

        # ----------
        # provides ...

        (.+ provides (?P<retn>a String) representation of .+)
        v=\1

        # ----------
        # returns ...

        (.+ returning (?P<retn>\*true\*, \*false\*, or \*undefined\*) .+)
        v=\1

        (.+ returning (?P<retn>\*true\* or \*false\*)\.)
        v=\1

        (Return (?P<retn>a String) .+)
        v=\1

        (Returns (?P<retn>a Number) .+)
        v=\1

        (Returns the Number .+)
        retn=a Number
        v=\1

        (Returns (?P<retn>a new _TypedArray_ object) .+)
        v=\1

        (Returns (?P<retn>an Array object) into .+)
        v=\1

        (Returns the .+ integral Number value .+)
        retn=an integral Number
        v=\1

        (Returns the integral part of the number .+)
        retn=an integral Number
        v=\1

        (.+ returns (?P<retn>a Number) .+)
        v=\1

        (.+ returns (?P<retn>a String) .+)
        v=\1

        (.+ returns (?P<retn>a new promise) .+)
        v=\1

        (.+ returns (?P<retn>a promise) .+)
        v=\1

        (.+ returns a <emu-not-ref>substring</emu-not-ref> .+)
        retn=a String
        v=\1

        (.+ returns (an Array object) containing .+, (or \*null\*) if _string_ did not match.)
        retn=\2 \3
        v=\1

        (.+ returns (?P<retn>an Iterator object) .+)
        v=\1

        (.+ returns (?P<retn>an array) .+)
        v=\1

        (.+ returns (?P<retn>an Iterator object) .+)
        v=\1

        (.+ returns either a new promise .+ or the argument itself if the argument is a promise .+)
        retn=a promise
        v=\1

        (.+ returns (?P<retn>an integral Number) representing the local time zone adjustment, .+)
        v=\1

        # -----------

        # (.+) the value of (the Boolean argument) _S_.
        # ps=\2 _S_
        # v=\1 the value of _S_.
        # Better to not try to extract parameter info from env-rec preambles?

        (.+) as follows:
        v=\1.

'''

class ExtractionRules:
    def __init__(self, rules_str):
        self.rules = []
        rules_str = rules_str.strip()
        if rules_str == '': 
            return

        for chunk in re.split(r'\n{2,} *', rules_str):
            lines = [
                line
                for line in re.split(r'\n *', chunk)
                if not line.startswith('#')
            ]
            if len(lines) == 0:
                # A chunk consisting only of comment-lines.
                continue

            self.rules.append(HeaderConstructionRule(lines))

    def apply(self, orig_subject, info_holder, trace):
        assert orig_subject != ''
        have_shown_a_trace_for_this_subject = False

        subject = orig_subject

        for rule in self.rules:
            mo = rule.reo.fullmatch(subject)
            if mo is None:
                continue

            # match!
            rule.count += 1

            if trace:
                if not have_shown_a_trace_for_this_subject:
                    stderr('--------------------------')
                    stderr(f"subject: {orig_subject}")
                    stderr()
                have_shown_a_trace_for_this_subject = True
                stderr(f"matches: {rule.raw_pattern}")

            for (key, value) in mo.groupdict().items():
                if trace: stderr(f"inline : {key} = {value}")
                info_holder.add(key, value)

            for (key, template) in rule.templates.items():
                value = mo.expand(template)
                if key == 'v':
                    # 'v' just because it looks like a down-arrow,
                    # i.e., this is what gets passed down to the next rule
                    subject = value
                else:
                    if trace: stderr(f"outline: {key} = {value}")
                    info_holder.add(key, value)

            if trace:
                stderr(f"leaving: {subject}")
                stderr()

            if subject == '':
                # no point trying further rules
                break

        # debugging:
        # if self == single_sentence_rules and subject == orig_subject:
        #     print(f"No change: {orig_subject}")

        return subject

class HeaderConstructionRule:
    def __init__(self, lines):
        self.raw_pattern = lines.pop(0)
        self.reo = re.compile(self.raw_pattern)
        self.templates = {}
        for line in lines:
            mo = re.fullmatch(r'([\w ]+)=(.*)', line)
            if mo is None:
                stderr(f"bad line: {line}")
                sys.exit(1)
            (key, template) = mo.groups()
            assert key not in self.templates
            self.templates[key] = template
        if 'v' not in self.templates:
            self.templates['v'] = ''
        self.count = 0

multi_sentence_rules = ExtractionRules(multi_sentence_rules_str)
single_sentence_rules = ExtractionRules(single_sentence_rules_str)

def extract_info_from_preamble(preamble_nodes, section):
    # PR #1914 established a consistent format for abstract operation preambles
    if len(preamble_nodes) == 1:
        preamble_node = preamble_nodes[0]
        preamble_text = preamble_node.inner_source_text().strip()
        if (
            preamble_text.startswith('The abstract operation')
            or
            (preamble_text.startswith('The ') and ' takes ' in preamble_text)
            and
            not preamble_text.startswith("The `")
        ):
            ih = extract_info_from_standard_preamble(preamble_nodes[0])
            if ih: return ih
    
    # Okay, so this preamble has a non-standard format.
    if section.section_kind in [
        'anonymous_built_in_function',
        'accessor_property',
        'function_property',
        'CallConstruct',
    ]:
        # no standard yet
        pass
    else:
        oh_warn()
        oh_warn(f"non-standard preamble for {section.section_kind}:")
        oh_warn(section.section_num, section.section_title, section.section_id)

    info_holder = PreambleInfoHolder()

    para_texts_remaining = []
    for preamble_node in preamble_nodes:
        assert preamble_node.element_name == 'p'

        para_text = preamble_node.inner_source_text().strip()
        trace = ('xInvoke' in para_text)
        para_text_remaining = multi_sentence_rules.apply(para_text, info_holder, trace)
        if para_text_remaining != '':
            sentences_remaining = []
            for sentence in re.split('(?<=\.) +', para_text_remaining):
                sentence_remaining = single_sentence_rules.apply(sentence, info_holder, trace)
                if sentence_remaining != '':
                    sentences_remaining.append(sentence_remaining)
            # if sentences_remaining:
            para_text_remaining = ' '.join(sentences_remaining)
            if para_text_remaining != '':
                info_holder.add('desc', para_text_remaining)

    return info_holder

def note_unused_rules():
    stderr()
    stderr("Unused rules in `multi_sentence_rules`:")
    for rule in multi_sentence_rules.rules:
        if rule.count == 0:
            stderr(f"    {rule.raw_pattern}")

    stderr()
    stderr("Unused rules in `single_sentence_rules`:")
    for rule in single_sentence_rules.rules:
        if rule.count == 0:
            stderr(f"    {rule.raw_pattern}")
    stderr()

class PreambleInfoHolder:
    def __init__(self):
        self.fields = defaultdict(list)

    def add(self, key, value):
        self.fields[key].append(value)

    def _dedupe(self):
        for (key, values) in self.fields.items():
            deduped_values = [
                v
                for (i,v) in enumerate(values)
                if v not in values[0:i]
            ]
            self.fields[key] = deduped_values

    def convert_to_header(self):
        self._dedupe()

        poi = AlgHeader()

        def join_field_values(key, joiner = ' & '):
            values = self.fields[key]
            if not values: return None
            return joiner.join(values)

        def at_most_one_value(key):
            values = self.fields[key]
            if not values: return None
            assert len(values) == 1, values
            return values[0]

        vs = join_field_values('kind')
        poi.kind = {
            'abstract operation'                        : 'abstract operation',
            'concrete method'                           : 'concrete method',
            'concrete method & abstract method'         : 'concrete method', # spec bug?
            'host-defined abstract operation'           : 'host-defined abstract operation',
            'implementation-defined algorithm'          : 'host-defined abstract operation',
            'internal comparison abstract operation'    : 'abstract operation',
            'job'                                       : 'abstract operation',
            'internal method'                           : 'internal method',
            'numeric method'                            : 'numeric method',
            #
            'anonymous built-in function object'        : 'anonymous built-in function',
            'anonymous built-in function'               : 'anonymous built-in function',
            'accessor property'                         : 'accessor property',
            'constructor'                               : 'function property',
            'function'                                  : 'function property',
            'method'                                    : 'function property',
            None                                        : None,
        }[vs]

        poi.name = at_most_one_value('name')

        poi.for_phrase = at_most_one_value('for')

        if poi.name and RE.fullmatch('(.+)(::.+)', poi.name):
            assert poi.for_phrase is None
            poi.for_phrase = RE.group(1)

            poi.name = RE.group(2)

            assert poi.kind == 'abstract operation'
            poi.kind = 'numeric method'

        # Have to do this one "out of order"
        # because of possible calls to add_to_description(). 
        poi.description_paras = self.fields['desc']

        pl_values = self.fields['pl']
        if len(pl_values) == 0:
            poi.param_names = None
        elif len(pl_values) == 1:
            get_info_from_parameter_listing_in_preamble(poi, pl_values[0])
        elif pl_values == [
            'zero or more arguments',
            'zero or more arguments which form the rest parameter ..._args_'
        ]:
            get_info_from_parameter_listing_in_preamble(poi, pl_values[1])
        else:
            stderr(f"{poi.name} has multi-pl: {poi.param_names}")
            assert 0

        for ps in self.fields['ps']:
            get_info_from_parameter_sentence_in_ao_preamble(poi, ps)

        also = at_most_one_value('also')
        if also is None:
            poi.also = None
        else:
            # move to finish_initialization ?
            (varnames, where) = {
                'the _comparefn_ argument passed to the current invocation of the `sort` method':
                    (['_comparefn_'], 'from the current invocation of the `sort` method'),

                # 'preambles' PR:
                'the _comparefn_ and _buffer_ values of the current invocation of the `sort` method':
                    (['_comparefn_', '_buffer_'], 'from the `sort` method'),

                # '_reviver_ that was originally passed to the above parse function':
                #     (['_reviver_'], 'from the above parse function'),
                # ^ obsoleted by the merge of PR #1879

                # '_ReplacerFunction_ from the invocation of the `stringify` method':
                #     (['_ReplacerFunction_'], 'from the invocation of the `stringify` method'),
                # 'the _stack_, _indent_, _gap_, and _PropertyList_ values of the current invocation of the `stringify` method':
                #     (['_stack_', '_indent_', '_gap_', '_PropertyList_'], 'from the current invocation of the `stringify` method'),
                # 'the _stack_, _indent_, and _gap_ values of the current invocation of the `stringify` method':
                #     (['_stack_', '_indent_', '_gap_'], 'from the current invocation of the `stringify` method'),
                # ^ obsoleted by the merge of PR #1890
            }[also]
            poi.also = [
                (varname, where)
                for varname in varnames
            ]

        # Cheat: Add some 'also' info that doesn't appear in the preamble.
        # move to finish_initialization?

        if poi.name in [
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
            assert poi.also is None
            poi.also = regexp_also

        poi.return_nature_normal = join_field_values('retn', ' or ')

        poi.return_nature_abrupt = at_most_one_value('reta')

        if poi.return_nature_normal and 'a completion record' in poi.return_nature_normal:
            assert poi.return_nature_abrupt is None
            if poi.return_nature_normal == 'a completion record whose [[Type]] is ~normal~ and whose [[Value]] is a Boolean':
                poi.return_nature_normal = 'a Boolean'
                poi.return_nature_abrupt = 'N/A'
            elif poi.return_nature_normal == 'a completion record which, if its [[Type]] is ~normal~, has a [[Value]] which is a Boolean':
                poi.return_nature_normal = 'a Boolean'
            else:
                stderr()
                stderr(poi.name)
                stderr(poi.return_nature_normal)

        return poi

# ----------------------------------

def get_first_ln(node):
    (ln, _) = shared.convert_posn_to_linecol(node.start_posn)
    return ln

def get_last_ln(node):
    (ln, _) = shared.convert_posn_to_linecol(node.end_posn)
    return ln

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

rec_method_declarations = '''

    # Table 16: Abstract Methods of Environment Records
    HasBinding(N)                -> a Boolean
    CreateMutableBinding(N, D)   -> TBD
    CreateImmutableBinding(N, S) -> TBD
    InitializeBinding(N, V)      -> TBD
    SetMutableBinding(N, V, S)   -> a Boolean or *empty* | throw
    GetBindingValue(N, S)        -> an ECMAScript language value | throw *ReferenceError*
    DeleteBinding(N)             -> a Boolean
    HasThisBinding()             -> a Boolean
    HasSuperBinding()            -> a Boolean
    WithBaseObject()             -> an Object or *undefined*

    # Table 18: Additional Methods of Function Environment Records
    BindThisValue(V) -> TBD
    GetThisBinding() -> an ECMAScript language value | throw *ReferenceError*
    GetSuperBase()   -> an Object or *null* or *undefined*

    # Table 20: Additional Methods of Global Environment Records
    # GetThisBinding()                   -> an ECMAScript language value | throw *ReferenceError*
    HasVarDeclaration(N)                 -> a Boolean
    HasLexicalDeclaration(N)             -> a Boolean
    HasRestrictedGlobalProperty(N)       -> a Boolean
    CanDeclareGlobalVar(N)               -> a Boolean
    CanDeclareGlobalFunction(N)          -> a Boolean
    CreateGlobalVarBinding(N, D)         -> TBD
    CreateGlobalFunctionBinding(N, V, D) -> TBD

    # Table 21: Additional Methods of Module Environment Records
    CreateImportBinding(N, M, N2) -> TBD
    # GetThisBinding()            -> an ECMAScript language value | throw *ReferenceError*

    # Table 39: Abstract Methods of Module Records
    GetExportedNames(exportStarSet)       -> a List of names
    ResolveExport(exportName, resolveSet) -> a ResolvedBinding Record or *null* or *"ambiguous"*
    Link()                                -> TBD
    Evaluate()                            -> TBD

    # Table 41: Additional Abstract Methods of Cyclic Module Record
    InitializeEnvironment() -> TBD
    ExecuteModule()         -> TBD
'''

rec_method_param_nature_ = {
    '_D_' : 'a Boolean',
    '_M_' : 'a Module Record',
    '_N_' : 'a String',
    '_N2_': 'a String',
    '_S_' : 'a Boolean',
    '_V_' : 'an ECMAScript language value',
    '_exportStarSet_' : 'TBD',
    '_exportName_'    : 'a String',
    '_resolveSet_'    : 'TBD',
}

predeclared_rec_method_info = {}
for line in rec_method_declarations.split('\n'):
    line = line.strip()
    if line == '':
        # blank line
        continue
    if line.startswith('#'):
        # comment
        continue
    
    mo = re.fullmatch(r'(\w+)\(([^()]*)\) +-> (.+)', line)
    assert mo, line
    (name, params_str, return_nature) = (mo.groups())
    if params_str == '':
        param_names = []
    else:
        param_names = [
            ('_' + name + '_')
            for name in params_str.split(', ')
        ]
    param_nature_ = dict(
        (param_name, rec_method_param_nature_[param_name])
        for param_name in param_names
    )
    if 'throw' in return_nature:
        (return_nature_normal, return_nature_abrupt) = re.split(r' \| (?=throw)', return_nature)
    else:
        (return_nature_normal, return_nature_abrupt) = (return_nature, 'TBD')
    predeclared_rec_method_info[name] = (param_names, param_nature_, return_nature_normal, return_nature_abrupt)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def extract_info_from_standard_preamble(preamble_node):
    preamble_text = preamble_node.inner_source_text().strip()

    sentences = re.split('(?<=\.) +', preamble_text)

    sentence0 = sentences.pop(0)

    info_holder = PreambleInfoHolder()

    # -----------------------------------
    # The first sentence in the preamble:

    for pattern in [
        r'The (?P<kind>abstract operation) (?P<name>[\w:/]+) takes (?P<pl>.+) and returns (?P<retn>.+?)\.',
        r'The (?P<kind>abstract operation) (?P<name>[\w:/]+) takes (?P<pl>.+)\.',
        r'The (?P<kind>abstract operation) (?P<name><dfn id="\w+" aoid="\w+" oldids="sec-\w+">\w+</dfn>) takes (?P<pl>.+)\.',
        r'The (?P<kind>host-defined abstract operation) (?P<name>\w+) takes (?P<pl>.+)\.',
        r'The (?P<name>\w+) (?P<kind>concrete method) of (?P<for>.+) takes (?P<pl>.+)\.',
        r'The (?P<name>\[\[\w+\]\]) (?P<kind>internal method) of (?P<for>.+) takes (?P<pl>.+)\.',
    ]:
        mo = re.fullmatch(pattern, sentence0)
        if mo:
            for (key, value) in mo.groupdict().items():
                info_holder.add(key, value)
            break
    else:
        oh_warn()
        oh_warn("Starts like std preamble but isn't:")
        oh_warn(preamble_text)
        return None

    if sentences == []:
        return info_holder

    # ----------------------------------
    # also

    if RE.fullmatch('It also has access to (.+)\.', sentences[0]):
        info_holder.add('also', RE.group(1))
        del sentences[0]

    # ----------------------------------
    # The last sentence of the preamble:

    if sentences[-1] == 'It performs the following steps when called:':
        del sentences[-1]

    # ----------------------------------------
    # Any remaining sentences are description:
    
    if sentences:
        description = ' '.join(sentences)
        info_holder.add('desc', description)

    # -------------------------------------
    # But some of those sentences may give (additional) info about what's returned.

    for sentence in sentences:
        if sentence.startswith('It returns '):
            # Maybe if it's a numeric method, we shouldn't bother?
            for (pattern, nature) in [
                ("It returns the one's complement of _x_.+", 'TBD'),
                ('It returns \*true\* if .+ and \*false\* otherwise.', 'a Boolean'),
                ('It returns _argument_ converted to a Number value .+.', 'a Number'),
                ('It returns _value_ argument converted to a non-negative integer if it is a valid integer index value.', 'a non-negative integer'),
                ('It returns _value_ argument converted to a non-negative integer if it is a valid Uint53-string value.', 'a non-negative integer'), # PR 1623
                ('It returns _value_ converted to a numeric value of type Number or BigInt.', 'a Number or a BigInt'),
                ('It returns _value_ converted to a Number or a BigInt.', 'a Number or a BigInt'),
                ('It returns a new Job Abstract Closure .+', 'a Job Abstract Closure'),
                ('It returns a new promise resolved with _x_.', 'a promise'),
                ('It returns an implementation-approximated value .+', 'a Number'),
                ('It returns either \*false\* or the end index of a match.', '*false* or a non-negative integer'),
                ('It returns either ~not-matched~ or the end index of a match.', '~not-matched~ or a non-negative integer'),
                ('It returns the BigInt value that .+', 'a BigInt'),
                ('It returns the global object used by the currently running execution context.', 'an object'),
                ('It returns the loaded value.', 'TBD'),
                ('It returns the sequence of Unicode code points that .+', 'a sequence of Unicode code points'),
                ("It returns the value of its associated binding object's property whose name is the String value of the argument identifier _N_.", 'an ECMAScript language value'),
                ('It returns the value of its bound identifier whose name is the value of the argument _N_.', 'an ECMAScript language value'),
                ('It returns the value of the \*"length"\* property of an array-like object.', 'a non-negative integer'),
                ('It returns the value of the \*"length"\* property of an array-like object \(as a non-negative integer\).', 'a non-negative integer'),
            ]:
                if re.fullmatch(pattern, sentence):
                    info_holder.add('retn', nature)
                    break
            else:
                assert 0, sentence

        elif sentence == 'Otherwise, it returns *undefined*.':
            info_holder.add('retn', '*undefined*'),

        elif sentence.startswith('It throws'):
            for (pattern, nature) in [
                ('It throws an error .+',     'throw'),
                ('It throws an exception .+', 'throw'),
                ('It throws a \*TypeError\* exception .+', 'throw *TypeError*'),
            ]:
                if re.fullmatch(pattern, sentence):
                    info_holder.add('reta', nature)
                    break
            else:
                assert 0, sentence

    return info_holder

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_parameter_sentence_in_ao_preamble(oi, parameter_sentence):
    # if '_C_' in parameter_sentence: stderr('gifps', parameter_sentence)
    # if 'neither' in parameter_sentence: pdb.set_trace()

    if oi.name in [
        'FunctionDeclarationInstantiation',
        'CodePointAt',
        'BlockDeclarationInstantiation',
        'GlobalDeclarationInstantiation',
        'CreateDynamicFunction',
    ]:
        return

    foo = {
        '_x_ and _y_ are values':
            [('_x_', 'an ECMAScript language value'), ('_y_', 'an ECMAScript language value')],
        "_M_ is a Module Record, and _N2_ is the name of a binding that exists in _M_'s module Environment Record":
            [('_M_', 'a Module Record'), ('_N2_', 'a String')],
        "_argumentsList_ is a possibly empty List of ECMAScript language values":
            [('_argumentsList_', 'a List of ECMAScript language values')],
        "the |ModuleSpecifier| String, _specifier_":
            [('_specifier_', 'a String')],
        "the Script Record or Module Record _referencingScriptOrModule_":
            [('_referencingScriptOrModule_', 'a Script Record or Module Record')],
        "_array_":
            [('_array_', 'TBD')],
        "The optional _offset_ value":
            [('_offset_', 'TBD')],
        "the _typedArray_ argument object":
            [('_typedArray_', 'TBD')],
        '_referencingScriptOrModule_ may also be *null*':
            [('_referencingScriptOrModule_', 'Null')]
    }[parameter_sentence]

    for (param_name, nature) in foo:
        if oi.param_names and param_name in oi.param_names:
            # The preamble has previously 'declared' this parameter.
            current_nature = oi.param_nature_[param_name]
            if current_nature == 'TBD':
                new_nature = nature
            else:
                new_nature = current_nature + '; may also be ' + nature
            oi.param_nature_[param_name] = new_nature
        else:
            # The preamble has not previously 'declared' this parameter,
            # and yet it now mentions it in a way
            # that is normally only used when we've already declared it.

            if oi.param_names is None: oi.param_names = []

            oi.param_names.append(param_name)
            oi.param_nature_[param_name] = nature

# ------------------------------------------------------------------------------

def add_to_description(oi, sentence):
    # This is only called 9 times.
    # It would be nice to get rid of it,
    # because it can rearrange the contents of the preamble.
    # On the other hand, it doesn't do so in the remaining cases.

    # stderr('atd>', oi.name, ':', sentence)

    if oi.description_paras == []:
        desc = sub_many(sentence, [
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
        desc = sub_many(sentence, [
            ('^OP ', 'This operation '),
            (' OP ', ' this operation '),
            (' by performing the following steps:$', '.'),
        ])
    oi.description_paras.append(desc)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_heading(section):
    oi = AlgHeader()

    if section.section_kind in [
        'catchall',
        'changes',
    ]:
        return oi

    oi.kind = ( section.section_kind
        .replace('_', ' ')
        .replace('built in',                   'built-in')
        .replace('env rec method',             'concrete method')
        .replace('module rec method',          'concrete method')
        .replace('CallConstruct',              'function property')
    )

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
        'accessor_property',
        'CallConstruct',
        'anonymous_built_in_function',
    ]:
        # convert heading-style to elsewhere-style:
        # oi.name = ( section.ste['prop_path']
        #     .replace(' [ ', '[')
        #     .replace(' ]',  ']')
        # )
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

    assert oi.param_names is None, oi.name

    # if '_C_' in parameter_listing: stderr('gifpl', parameter_listing)

    if parameter_listing == '':
        assert 0
        return

    if parameter_listing == 'no arguments':
        # 27 cases
        oi.param_names = []
        return

    if parameter_listing in [
        'zero or more arguments _item1_, _item2_, etc.',
        'zero or more arguments',
        'any number of arguments',
        'one or two arguments',
        'zero or one arguments',
    ]:
        # 24 cases
        # XXX not sure what to do
        return

    if parameter_listing == 'zero or more arguments which form the rest parameter ..._args_':
        oi.param_names = ['_args_']
        oi.param_nature_['_args_'] = 'a List of ECMAScript language values'
        oi.rest_params.add('_args_')
        return

    if parameter_listing == 'one or two arguments, _predicate_ and _thisArg_':
        # 1 case
        oi.param_names = ['_predicate_', '_thisArg_']
        oi.optional_params.add('_thisArg_')
        return

    elif parameter_listing == 'an execution _execution_, two events _E_ and _D_ in SharedDataBlockEventSet(_execution_)':
        # 2 cases
        oi.param_names = ['_execution_', '_E_', '_D_']
        oi.param_nature_['_execution_'] = 'an execution'
        oi.param_nature_['_E_'] = 'an event in SharedDataBlockEventSet(_execution_)'
        oi.param_nature_['_D_'] = 'an event in SharedDataBlockEventSet(_execution_)'
        return

    elif parameter_listing in [
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no &ldquo; _p_ &rdquo; arguments, and where _body_ might also not be provided)',
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no &ldquo;_p_&rdquo; arguments, and where _body_ might also not be provided)',
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no "_p_" arguments, and where _body_ might also not be provided)',
        'some arguments _p1_, _p2_, &hellip; , _pn_, _body_ (where _n_ might be 0, that is, there are no _p_ arguments, and where _body_ might also not be provided)',
    ]:
        # 4 cases
        oi.param_names = ['_args_', '_body_']
        oi.param_nature_['_args_'] = 'a List of ECMAScript language values'
        oi.param_nature_['_body_'] = 'an ECMAScript language value'
        oi.optional_params.add('_body_')
        return

    elif parameter_listing  == 'at least one argument _buffer_':
        # 2 cases
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

    elif parameter_listing == 'up to three arguments _target_, _start_ and _end_':
        # 1 case
        oi.param_names = ['_target_', '_start_', '_end_']
        oh_warn()
        oh_warn(f"`{oi.name}` preamble param list:")
        oh_warn(repr(parameter_listing))
        oh_warn(f"is of the form: ... X, X and X")
        oh_warn(f"but expected  : ... X, X, and X")
        return
    elif parameter_listing == 'up to three arguments _value_, _start_ and _end_':
        # 1 case
        oi.param_names = ['_value_', '_start_', '_end_']
        oh_warn()
        oh_warn(f"`{oi.name}` preamble param list:")
        oh_warn(repr(parameter_listing))
        oh_warn(f"is of the form: ... X, X and X")
        oh_warn(f"but expected  : ... X, X, and X")
        return

    elif re.fullmatch(r'(two )?arguments _x_ and _y_ of type BigInt', parameter_listing):
        oi.param_names = ['_x_', '_y_']
        oi.param_nature_['_x_'] = 'a BigInt'
        oi.param_nature_['_y_'] = 'a BigInt'
        return

    # --------------------

    # 'Hide' commas within parentheses, so they don't mess up splits:
    def hide_commas(mo):
        return mo.group(0).replace(',', '<COMMA>')
    param_listing = re.sub(r'\(.*?\)', hide_commas, parameter_listing)
    # The commas will be unhidden later.

    # Also here:
    param_listing = re.sub(r'(_argumentsList_), (a List of ECMAScript language values)', r'\1<COMMA> \2', param_listing)

    # ---------------------

    oi.param_names = []

    # Split the listing into the 'required' and 'optional' parts:
    parts = []
    if 'optional' in param_listing:
        if RE.fullmatch(r'optional (argument.+)', param_listing):
            parts.append(('optional', RE.group(1)))
        elif RE.fullmatch(r'(.+?),? and optional (argument.+)', param_listing):
            parts.append(('required', RE.group(1)))
            parts.append(('optional', RE.group(2)))
        else:
            assert 0, param_listing
    else:
        parts.append(('required', param_listing))

    for (optionality, part) in parts:
        part = sub_many(part, [
            ('^parameters ', ''),
            ('^argument ', ''),
            ('^one argument,? ', ''),
            ('^an argument ', ''),
            ('^arguments ', ''),
            ('^two arguments,? ', ''),
        ])

        pieces = re.split('(, and |, | and )', part)
        assert len(pieces) % 2 == 1
        param_items = pieces[0::2]
        connectors = pieces[1::2]

        if len(connectors) == 0:
            expected_connectors = []
        elif len(connectors) == 1:
            expected_connectors = [' and ']
        else:
            expected_connectors = [', '] * (len(connectors) - 1) + [', and ']

        if connectors != expected_connectors:
            oh_warn()
            oh_warn(f"`{oi.name}` preamble param list:")
            oh_warn(repr(part))
            oh_warn(f"is of the form: X{'X'.join(connectors)}X")
            oh_warn(f"but expected  : X{'X'.join(expected_connectors)}X")

        var_pattern = r'\b_\w+_\b'

        for param_item in param_items:

            # unhide_commas:
            param_item = param_item.replace('<COMMA>', ',')

            parameter_names = re.findall(var_pattern, param_item)
            if len(parameter_names) != 1:
                stderr()
                stderr(f"> {oi.name}: param listing")
                stderr(f"    {parameter_listing!r}")
                stderr(f"  contains item {param_item!r} with {len(parameter_names)} parameter names")
                continue

            [param_name] = parameter_names

            assert param_name not in oi.param_names, param_name
            oi.param_names.append(param_name)

            if optionality == 'optional':
                oi.optional_params.add(param_name)

            if param_item == 'zero or more _args_':
                # XXX how to represent 'zero or more'?
                continue

            r_param_item = re.sub(var_pattern, 'VAR', param_item)

            for (pat, nat) in [
                (r'VAR, (a List of ECMAScript language values)', r'\1'),
                (r'VAR which is (a possibly empty List of ECMAScript language values)', r'\1'),
                (r'VAR of type BigInt', 'a BigInt'),
                (r'VAR \((.+)\)', r'\1'),
                (r'VAR',          'TBD'),

                (r'a Boolean flag named VAR', 'a Boolean'),
                (r'(an? .+) VAR', r'\1'),
                (r'(value) VAR',     r'a \1'),
            ]:
                mo = re.fullmatch(pat, r_param_item)
                if mo:
                    nature = mo.expand(nat)
                    break
            else:
                print(f"?   {r_param_item}")
                assert 0

            oi.param_nature_[param_name] = nature

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def resolve_oi(hoi, poi):
    if poi is None:
        # no preamble, so just use info from heading
        return hoi

    oi = AlgHeader()

    # kind
    if hoi.kind is None and poi.kind is None:
        assert 0
    elif hoi.kind is None:
        oi.kind = poi.kind
    elif poi.kind is None:
        oi.kind = hoi.kind
    else:
        if hoi.kind == poi.kind:
            oi.kind = hoi.kind
        elif hoi.kind == 'abstract operation' and poi.kind == 'host-defined abstract operation':
            oi.kind = poi.kind
        elif hoi.kind == 'numeric method' and poi.kind == 'abstract operation':
            oi.kind = hoi.kind
        else:
            stderr(f"mismatch of 'kind' in heading/preamble for {hoi.name}: {hoi.kind!r} != {poi.kind!r}")
            assert 0

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
            or
            hoi.name.replace(' [ ', '[').replace(' ]', ']') == poi.name
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

        assert (
            not poi.rest_params
            or
            poi.rest_params == hoi.rest_params
        )

    assert hoi.param_nature_ == {} # heading never has type info
    oi.param_nature_ = poi.param_nature_

    assert hoi.also is None
    oi.also = poi.also

    assert hoi.return_nature_normal is None
    oi.return_nature_normal = poi.return_nature_normal

    assert hoi.return_nature_abrupt is None
    oi.return_nature_abrupt = poi.return_nature_abrupt

    assert hoi.description_paras == []
    oi.description_paras = poi.description_paras

    return oi

# --------------------------------------------------------------------

def sub_many(subject, pattern_repls):
    # Apply each of `pattern_repls` to `subject`
    # and return the result.
    result = subject
    for (pattern, repl) in pattern_repls:
        result = re.sub(pattern, repl, result)
    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class AlgHeader:
    def __init__(self):
        self.kind = None
        self.name = None
        self.for_phrase = None
        self.param_names = None
        self.optional_params = set()
        self.rest_params = set()
        self.param_nature_ = {}
        self.also = None
        self.return_nature_normal = None
        self.return_nature_abrupt = None
        self.description_paras = []
        self.u_defns = []
        self.line_num = None

    # --------------------------------------------------------------------------

    def __str__(self):
        return f"""
            AlgHeader:
                name: {self.name}
                kind: {self.kind}
                for : {self.for_phrase}
                params: {', '.join(
                    pn + ' : ' + self.param_nature_.get(pn, 'TBD')
                    for pn in self.param_names
                    )
                }
                returns: {self.return_nature_normal}
                # defns: {len(self.u_defns)}
        """

    # --------------------------------------------------------------------------

    def add_defn(self, alg_defn):
        self.u_defns.append(alg_defn)
        assert alg_defn.header is None
        alg_defn.header = self

    # --------------------------------------------------------------------------

    def finish_initialization(self):

        self.name_w_markup = self.name
        if self.name.startswith('<'):
            mo = re.fullmatch(r'<dfn [^<>]+>([^<>]+)</dfn>', self.name)
            assert mo
            self.name = mo.group(1)

        # ------------------------------------------------------------

        # In addition to the clause-heading and the preamble,
        # there are other sources of information that can contribute to the header.
        # One is pre-declared info, like a table of method-signatures.
        # (Properly, we'd scrape that info from the spec itself.)

        def checked_set(prop_name, new_value):
            curr_value = getattr(self, prop_name)
            if curr_value is not None and curr_value != new_value:
                oh_warn()
                oh_warn(f"{self.name}, {prop_name}:")
                oh_warn(f"predeclared nature {new_value!r} overrides extracted nature {curr_value!r}")
            setattr(self, prop_name, new_value)

        if self.name in predeclared_rec_method_info:

            (pd_param_names, pd_param_nature_, pd_return_nature_normal, pd_return_nature_abrupt) = predeclared_rec_method_info[self.name]
            assert self.param_names == pd_param_names
            for param_name in self.param_names:
                pd_nature = pd_param_nature_[param_name]
                if param_name in self.param_nature_:
                    if self.param_nature_[param_name] != pd_nature:
                        oh_warn()
                        oh_warn(f"{self.name}, param {param_name}:")
                        oh_warn(f"predeclared nature {pd_nature!r} != extracted nature {self.param_nature_[param_name]!r}")
                else:
                    self.param_nature_[param_name] = pd_nature

            checked_set('return_nature_normal', pd_return_nature_normal)
            checked_set('return_nature_abrupt', pd_return_nature_abrupt)

        if self.kind == 'numeric method':
            assert self.for_phrase  in ['Number', 'BigInt']
            numeric_nature = f"a {self.for_phrase}"

            assert self.param_names
            for param_name in self.param_names:
                if param_name in self.param_nature_:
                    if self.param_nature_[param_name] != numeric_nature:
                        oh_warn()
                        oh_warn(f"{self.name}, param {param_name}:")
                        oh_warn(f"predeclared nature {numeric_nature!r} != extracted nature {self.param_nature_[param_name]!r}")
                else:
                    self.param_nature_[param_name] = numeric_nature

            if self.name in ['::equal', '::sameValue', '::sameValueZero']:
                pd_return_nature_normal = 'a Boolean'
            elif self.name == '::lessThan':
                pd_return_nature_normal = 'a Boolean or *undefined*'
            elif self.name == '::toString':
                pd_return_nature_normal = 'a String'
            else:
                pd_return_nature_normal = numeric_nature

            if self.name in ['::exponentiate', '::divide', '::remainder']:
                pd_return_nature_abrupt = 'throw *RangeError*'
            elif self.name == '::unsignedRightShift':
                pd_return_nature_abrupt = 'throw *TypeError*'
            else:
                pd_return_nature_abrupt = None

            checked_set('return_nature_normal', pd_return_nature_normal)
            checked_set('return_nature_abrupt', pd_return_nature_abrupt)

        # --------------------------------------------------------------------------

        assert len(self.rest_params) in [0,1]

        if self.param_names is None:
            if self.name == 'Proxy Revocation':
                # It has no parameters,
                # but neither the clause-heading nor the preamble say so.
                self.param_names = []
            else:
                oh_warn()
                oh_warn(f"{self.name}: self.param_names is None")
                self.param_names = []

        if self.kind in ['function property', 'anonymous built-in function', 'accessor property']:
            for param_name in self.param_names:
                nature = self.param_nature_.get(param_name, 'TBD')
                if nature == 'TBD':
                    if param_name in self.rest_params:
                        nature = 'a List of ECMAScript language values'
                    else:
                        nature = 'an ECMAScript language value'
                    self.param_nature_[param_name] = nature

        if self.return_nature_normal is None:
            if self.name.startswith('Math.'):
                self.return_nature_normal = 'a Number'
            else:
                self.return_nature_normal = 'TBD'

        if self.return_nature_abrupt is None:
            self.return_nature_abrupt = 'TBD'

        # -------------------------

        assert isinstance(self.description_paras, list)
        desc = ' '.join(self.description_paras)
        desc = re.sub(r'^(!OP|!FUNC|!CM) ', '', desc)
        desc = re.sub(r'^(It|This operation|The job) ', '', desc)
        desc = (desc
            .replace('!OP', 'This operation')
            .replace('!FUNC', 'This function')
        )
        self.description = desc
        # Alternatively: if len(self.description_paras) > 1: make separate <p> elements?

        # -------------------------

        if self.kind in ['function property', 'accessor property', 'anonymous built-in function']:
            bif_or_op = 'bif'
        else:
            bif_or_op = 'op'
        alg = spec.alg_info_[bif_or_op][self.name]
        alg.headers.append(self)

    # --------------------------------------------------------------------------

    def lines(self, indentation, mode):
        if mode != 'dls w initial info':
            # kludge
            return self.tah.lines(indentation, mode)

        _ = DL(indentation)

        # ---------------------------------------

        _.start()
        _.dt("op kind")
        _.dd(self.kind)
        _.dt("name")
        _.dd(self.name_w_markup)

        if self.for_phrase:
            _.dt("for")
            _.dd(self.for_phrase)

        # -------------------------

        assert self.param_names is not None
        if len(self.param_names) == 0:
            _.dt("parameters")
            _.dd("none")

        else:
            _.dt("parameters")
            _.dd_ul_start(self.param_names)

            for param_name in self.param_names:
                optionality = '(optional) ' if param_name in self.optional_params else ''
                param_nature = self.param_nature_.get(param_name, 'TBD')
                _.dd_ul_li(param_name, optionality + param_nature)

            _.dd_ul_end()

        # -------------------------

        if self.also:
            _.dt("also has access to")
            _.dd_ul_start(var_name for (var_name,_) in self.also)

            for (var_name, expl) in self.also:
                _.dd_ul_li(var_name, expl)

            _.dd_ul_end()

        # -------------------------

        _.dt("returns")
        _.dd_ul_start(["normal", "abrupt"])

        _.dd_ul_li("normal", self.return_nature_normal)
        _.dd_ul_li("abrupt", self.return_nature_abrupt)

        _.dd_ul_end()

        # -------------------------

        if self.description:
            _.dt("description")
            _.dd(self.description)

        lines = _.end()

        return lines

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class AnnexForSDOs:

    def lines(self, ind, mode):
        # ignore `ind`
        yield ''
        yield '<emu-annex id="sec-headers-for-sdos">'
        yield '  <h1>Headers for Syntax-Directed Operations</h1>'
        yield '  <p>blah</p>'
        for (_, header) in sorted(spec.oi_for_sdo_.items()):
            for line in header.lines(2, mode):
                yield line
        yield '</emu-annex>'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def write_modified_spec():
    mode = 'dls w initial info'
    show_targeted_msgs = False

    filename = 'spec_w_eoh'
    f = shared.open_for_output(filename)

    shared.write_spec_with_extras(mode, show_targeted_msgs, f)

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
