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

    global oh_inc_f
    oh_inc_f = shared.open_for_output('oh_warnings')

    for s in spec.root_section.each_descendant_that_is_a_section():
        create_operation_info_for_section(s)

    oh_inc_f.close()

    note_unused_rules()

    write_header_info()

# ------------------------------------------------------------------------------

def oh_warn(*args):
    print(*args, file=oh_inc_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def should_create_op_info_for_algoless_section(s):

    # It depends on what we intend to do with the op_info.
    # From the point of view of static type analysis,
    # there's no reason to generate op_info for an algoless section.

    # -----------------------------

    # It's the kind of section that we never want to create op info for:

    if s.section_kind in [
        'env_rec_method_unused',
        #
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

    if s.section_kind.endswith('abstract_operation'):
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
        'Changes to IsLooselyEqual',
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

    if s.section_kind in ['syntax_directed_operation', 'early_errors']:
        something_sdo(s)
        return

    # ------------------------------------------------------

    algo_child_posns = [
        i
        for (i, child) in enumerate(s.block_children)
        if (
            child.element_name == 'emu-alg'
            or
            (
                # Conversions are often presented in a table
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
        elif child.element_name == 'emu-grammar':
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
        ):
            # The op is the one indicated by the section heading.
            # print(s.section_num, s.section_kind, 'is', span_end_i)
            hoi = get_info_from_heading(s)

        else:
            # The op is *not* the one indicated by the section heading.
            # print(s.section_num, s.section_kind, 'isnt', span_end_i)
            hoi = AlgHeader()
            if s.section_title == 'Array.prototype [ @@unscopables ]':
                hoi.name = 'initializer for @@unscopables'
                hoi.kind = 'abstract operation'
                hoi.param_names = []
            else:
                oh_warn()
                oh_warn(f"In {s.section_num} {s.section_title},")
                oh_warn(f"    an algorithm gets no info from heading")

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

        if p_start_i == p_end_i or (span_start_i == 0 and s.has_structured_header):
            # no children in preamble, so no lines to suppress
            poi = None
        else:
            if False:
                # Suppress the preamble lines, since anything useful
                # in the preamble will appear in the header.
                #
                # We don't do this any more (after the merge of PR #545),
                # as the purpose is no longer to replace preambles with structured headers.
                # But it's possible that we might have a similar purpose again
                # (e.g., for built-in functions), so I'm keeping the code just in case.
                #
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
        oi.node_at_end_of_header = prev
        if algo:
            if algo.element_name == 'emu-alg':
                if hasattr(algo, '_parent_algdefn'):
                    oi.add_defn(algo._parent_algdefn)
                else:
                    stderr(f"No _parent_algdefn for {algo}")
            elif algo.element_name == 'emu-table':
                assert not hasattr(algo, '_parent_algdefn')
                assert oi.kind == 'abstract operation'
                op = spec.alg_info_['op'][oi.name]
                for alg_defn in op.definitions:
                    if alg_defn.section is s:
                        oi.add_defn(alg_defn)
                    else:
                        assert alg_defn.section.section_title == 'Changes to ToBoolean'
                        # skip it for now
            else:
                assert 0, algo.element_name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def something_sdo(s):
    assert s.section_kind in ['syntax_directed_operation', 'early_errors']

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

    if op_name == 'regexp-Evaluate':
        declare_sdo(s, op_name, param_dict, regexp_also)
    else:
        declare_sdo(s, op_name, param_dict)

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

def declare_sdo(section, op_name, param_dict, also=[]):
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
        assert op_info.species in ['op: syntax-directed', 'op: early error']
        for alg_defn in op_info.definitions:
            if alg_defn.section.section_num.startswith('B'): continue
            oi.add_defn(alg_defn)

        oi.node_at_end_of_header = section.heading_child

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

multi_sentence_rules_str = r'''

        This (?P<kind>function) returns (?P<retn>a String value). The contents of the String (are .+)
        v=The contents of the returned String \3

        (`([][@\w.]+)` is an accessor property whose set accessor function is \*undefined\*.) Its get accessor function performs the following steps:
        name=get \2
        v= \1
        # A bit kludgey: Insert a space to prevent later match against /`(?P<name>[\w.]+)` (.+)/
'''

single_sentence_rules_str = r'''

    # ==========================================================================
    # Sentences that start with "A" or "An"

        A (candidate execution (_\w+_)) (has .+) if the following (?P<kind>algorithm) (returns \*true\*).
        pl=a \1
        v=\2 \3 if this operation \5.

        (An? (?P<name>.+) function) is an (?P<kind>anonymous built-in function) that ((has|is) .+)
        v=!FUNC \4

    # ==========================================================================

        For (?P<pl>an execution _\w+_, two events (_\w_ and _\w_) in \S+) (are in a .+) if the following (?P<kind>algorithm) (returns \*true\*).
        v=\2 \3 if this operation \5.

    # ==========================================================================
    # Sentences that start with "It"

        It can take three parameters.
        # could send to <ps>, but not helpful.

        It performs the following steps when called:

        Its get accessor function performs the following steps when called:

    # ==========================================================================

        (Returns (?P<retn>an array) containing .+)
        v=\1

    # ==========================================================================
    # Sentences that start with "The"

        # --------------

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

        The <dfn>(?P<name>[^<>]+)</dfn> intrinsic is an (?P<kind>anonymous built-in function object) that (?P<desc>is defined once for each realm.)

        The (?P<name>[%\w]+) (?P<kind>constructor) performs the following steps when called:

        # ------------

        The `(?P<name>[\w.]+)` (?P<kind>function|method) (.+)
        v=!FUNC \3

        `(?P<name>[\w.]+)` (.+)
        v=!FUNC \2

            !FUNC takes (?P<pl>.+), and performs the following steps:

            !FUNC takes (?P<pl>.+), and (returns .+)
            v=!FUNC \2

            !FUNC performs the following steps:

    # ==========================================================================
    # Sentences that start with "This"

        # Note that none of these leave anything for the description.

        This (?P<kind>function) takes (?P<pl>no arguments).

        This function (.+)
        v=!FUNC \1

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

        if trace:
            stderr('--------------------------')
            stderr(f"subject: {orig_subject}")
            stderr()
            have_shown_a_trace_for_this_subject = True

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
        oh_warn(f"In {section.section_num} {section.section_title} ({section.section_id}),")
        oh_warn(f"there is a non-standard preamble")

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
            'algorithm'                                 : 'abstract operation',
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
                'the _comparefn_ and _buffer_ values of the current invocation of the `sort` method':
                    (['_comparefn_', '_buffer_'], 'from the `sort` method'),
            }[also]
            poi.also = [
                (varname, where)
                for varname in varnames
            ]

        poi.return_nature_normal = join_field_values('retn', ' or ')

        poi.return_nature_abrupt = at_most_one_value('reta')

        poi.description_paras = self.fields['desc']

        return poi

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

rec_method_declarations = '''

    # Table 16: Abstract Methods of Environment Records
    HasBinding(N)                -> a Boolean
    CreateMutableBinding(N, D)   -> TBD
    CreateImmutableBinding(N, S) -> TBD
    InitializeBinding(N, V)      -> TBD
    SetMutableBinding(N, V, S)   -> a Boolean or ~empty~ | throw
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
    ExecuteModule(capability) -> TBD
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
    '_capability_'    : 'an optional PromiseCapability',
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
        r'The (?P<kind>abstract operation) (?P<name>[\w:/]+) takes (?P<pl>.+)\.',
        r'The (?P<kind>abstract operation) (?P<name><dfn id="\w+" aoid="\w+" oldids="sec-\w+">\w+</dfn>) takes (?P<pl>.+)\.',
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
    
    assert sentences == [] # since the merge of PR 545

    return info_holder

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_parameter_sentence_in_ao_preamble(oi, parameter_sentence):
    # if '_C_' in parameter_sentence: stderr('gifps', parameter_sentence)
    # if 'neither' in parameter_sentence: pdb.set_trace()

    foo = {
        "The optional _offset_ value":
            [('_offset_', 'TBD')],
    }[parameter_sentence]

    for (param_name, nature) in foo:
        if oi.param_names and param_name in oi.param_names:
            # The preamble has previously 'declared' this parameter.
            assert 0 # since PR #1914 or so
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
        'host-defined_abstract_operation',
        'implementation-defined_abstract_operation',
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

    if 'parameters' not in section.ste or section.ste['parameters'] is None:
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

    if 'for_phrase' in section.ste:
        oi.for_phrase = section.ste['for_phrase']

    oi.param_nature_ = section.ste.get('param_nature_', {})

    oi.return_nature_normal = section.ste.get('return_nature_normal', None)
    oi.return_nature_abrupt = section.ste.get('return_nature_abrupt', None)

    if 'also' in section.ste:
        oi.also = section.ste['also']

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
        # 1 case
        # kludgey
        if oi.name == 'DataView':
            oi.param_names = ['_buffer_', '_byteOffset_', '_byteLength_']
            oi.optional_params.add('_byteOffset_')
            oi.optional_params.add('_byteLength_')
        else:
            assert 0, oi.name
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
        oh_warn()
        oh_warn(f'resolve_oi: {hoi.name}/{poi.name}: kind is None in both hoi and poi')
    elif hoi.kind is None:
        oi.kind = poi.kind
    elif poi.kind is None:
        oi.kind = hoi.kind
    else:
        if hoi.kind == poi.kind:
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

        if self.name not in spec.alg_info_[bif_or_op]:
            oh_warn()
            oh_warn(f"finish_initialization: spec.alg_info_[{bif_or_op!r}] has no entry for {self.name!r}")
            return
            
        alg = spec.alg_info_[bif_or_op][self.name]
        alg.headers.append(self)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def write_header_info():
    stderr("write_header_info ...")

    f = shared.open_for_output('header_info')

    def put(*args): print(*args, file=f)

    for bif_or_op in ['op', 'bif']:
        put('X'*40)
        put(bif_or_op)
        for (alg_name, alg_info) in sorted(spec.alg_info_[bif_or_op].items()):
            n_defns_via_headers = 0
            assert alg_info.name == alg_name
            assert alg_info.bif_or_op == bif_or_op
            put()
            put(f"  {alg_info.name}")
            put(f"    {alg_info.species}")
            put(f"    {len(alg_info.headers)} headers:")
            for alg_header in alg_info.headers:
                assert alg_header.name == alg_name
                assert (alg_info.species, alg_header.kind) in [
                  ('bif: * per realm'               , 'anonymous built-in function'    ),
                  ('bif: accessor function'         , 'accessor property'              ),
                  ('bif: value of data property'    , 'function property'              ),
                  ('op: concrete method: env rec'   , 'concrete method'                ),
                  ('op: concrete method: module rec', 'concrete method'                ),
                  ('op: early error'                , 'syntax-directed operation'      ),
                  ('op: host-defined'               , 'abstract operation'             ),
                  ('op: host-defined'               , 'host-defined abstract operation'),
                  ('op: implementation-defined'     , 'implementation-defined abstract operation'),
                  ('op: internal method'            , 'internal method'                ),
                  ('op: numeric method'             , 'numeric method'                 ),
                  ('op: solo'                       , 'abstract operation'             ),
                  ('op: solo'                       , 'host-defined abstract operation'),
                  ('op: syntax-directed'            , 'syntax-directed operation'      ),
                ]
                put(f"      --")
                put(f"        {alg_header.kind}")
                if alg_header.for_phrase: put(f"        for: {alg_header.for_phrase}")
                # alg_header.param_names, .optional_params, .rest_params, .param_nature_
                # alg_header.also
                # alg_header.return_nature_{normal,abrupt}
                # alg_header.description_paras
                put(f"        {len(alg_header.u_defns)} defns")
                n_defns_via_headers += len(alg_header.u_defns)
                for alg_defn in alg_header.u_defns:
                    assert alg_defn.header is alg_header
            n_defns = len(alg_info.definitions)
            if n_defns_via_headers != n_defns:
                put(f"    ERROR: n_defns_via_headers = {n_defns_via_headers}, but n_defns = {n_defns}, so {n_defns-n_defns_via_headers} missing")
            # alg_info.invocations
            # alg_info.callees
            # alg_info.callers
        put()

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
