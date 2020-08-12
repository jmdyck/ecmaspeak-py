#!/usr/bin/python3

# ecmaspeak-py/static_type_analysis.py:
# Perform static type analysis/inference on the spec's pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, atexit, time, sys, pdb
from operator import itemgetter
from collections import OrderedDict, defaultdict
from itertools import zip_longest
from pprint import pprint

import shared, HTML
from shared import stderr, spec, RE
from Pseudocode_Parser import ANode
from Graph import Graph

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def main():
    if sys.argv[1] == '-just_initial_headers':
        stop_after_initial_headers = True
        outdir = sys.argv[2]
    else:
        stop_after_initial_headers = False
        outdir = sys.argv[1]

    shared.register_output_dir(outdir)
    spec.restore()
    add_line_info()

    add_styling()
    make_initial_headers()
    if stop_after_initial_headers: return

    prep_for_STA()
    gather_nonterminals()
    levels = compute_dependency_levels()
    do_static_type_analysis(levels)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
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

def make_initial_headers():
    global un_f
    un_f = shared.open_for_output('unconverted_natures')
    global oh_inc_f
    oh_inc_f = shared.open_for_output('oh_warnings')

    stderr("collecting info...")
    for s in spec.root_section.each_descendant_that_is_a_section():
        create_operation_info_for_section(s)

    write_modified_spec('dls w initial info')

    note_unused_rules()

    un_f.close()
    oh_inc_f.close()

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
    elif s.section_id == 'sec-module-environment-records-deletebinding-n':
        # "Assert: This method is never invoked."
        # So there's no point type-checking it.
        # (It shouldn't even be there, really.)
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
    elif s.section_id == 'sec-static-semantic-rules':
        # It has the default definition for 'Contains',
        # but that's an SDO, so it only gets a header at the end.
        # (But we can't call something_sdo(s).)
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
            or
            (
                # For most Math functions (and many Number methods),
                # a <ul> plays roughly the role of an <emu-alg>.
                child.element_name == 'ul'
                and
                (
                    s.parent.section_title == 'Function Properties of the Math Object'
                    or
                    s.section_title.startswith('Number::')
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
            assert algo.element_name in ['emu-alg', 'emu-table', 'ul']

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
            hoi = Header()
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

            info_holder = extract_info_from_preamble(s.block_children[p_start_i:p_end_i])
            poi = info_holder.convert_to_header()

        # -----------------------------------

        oi = resolve_oi(hoi, poi)
        oi.apply_ad_hoc_fixes(s)
        oi.finish_initialization()
        spec.info_for_line_[ln].afters.append(oi)
        if algo:
            if algo.element_name == 'emu-alg':
                oi.u_defns.append(algo._parent_foodefn)
            else:
                assert algo.element_name in ['ul', 'emu-table']
                assert not hasattr(algo, '_parent_foodefn')

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
    oi = Header()
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
        oi.finish_initialization()
        spec.oi_for_sdo_[op_name] = oi

        op_info = spec.info_for_op_named_[op_name]
        assert op_info.name == op_name
        assert op_info.kind == 'op: syntax-directed'
        for foo_defn in op_info.definitions:
            if foo_defn.section.section_num.startswith('B'): continue
            if foo_defn.discriminator is None: continue # XXX for now
            oi.u_defns.append(foo_defn)

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

        A (?P<pl>candidate execution (_\w+_)) (has .+) if the following (?P<kind>abstract operation) (returns \*true\*).
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

        The concrete Environment Record method (?P<name>\w+) for (?P<for>.+ Environment Record)s (.+)
        kind=concrete method
        v=!CM \3

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

        The (?P<name>\w+) (?P<kind>concrete method) of (?P<for>a .+) (implements .+)
        v=!CM \4

            !CM implements the corresponding.* Module Record abstract method.

        The <dfn>(?P<name>[^<>]+)</dfn> intrinsic is an (?P<kind>anonymous built-in function object) that (?P<desc>is defined once for each realm.)

        The (?P<name>[%\w]+) (?P<kind>constructor) performs the following steps:

        The (?P<name>\[\[\w+\]\]) (?P<kind>internal method) (for|of) (?P<for>.+) is called with (?P<pl>.+).

        The (?P<name>\[\[\w+\]\]) (?P<kind>internal method) (for|of) (?P<for>.+) when called with (?P<pl>.+) performs the following steps:

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

        This (?P<kind>abstract method) performs the following steps \(m(ost of the work is done by .+)\):
        v=(M\2.)

        This (?P<kind>abstract method) performs the following steps:

        This description applies if and only if the (?P<name>Array) constructor is called with (.+).
        kind=overloaded constructor
        overload_resolver=\2

        This description applies only if the (?P<name>Date) constructor is called with (.+).
        kind=overloaded constructor
        overload_resolver=\2

        This description applies only if the (?P<name>_TypedArray_) function is called with (.+).
        kind=overloaded function
        overload_resolver=\2

        This (?P<kind>function) takes (?P<pl>no arguments).

        This function (.+)
        v=!FUNC \1

    # ==========================================================================
    # Sentences that start with "When"

        # (Ultimately, almost nothing falls through to the description.)

        # When the ...

        When the (?P<name>\[\[\w+\]\]) (?P<kind>internal method) of (?P<for>_\w+_) is called(.+)
        v=When it is called\4

        When the (?P<name>\[\[\w+\]\]) (?P<kind>internal method) of (?P<for>an? .+ _\w+_) is called(.+)
        v=When it is called\4

        When the (?P<name>\[\[\w+\]\]) (?P<kind>internal method) of (a bound function exotic object), _F_(, which| that) was created using the bind function is called(.+)
        for=\3 _F_
        v=When it is called\5

        When the `(?P<name>Date)` (function) is called(.+)
        kind=overloaded constructor
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

        When called with (?P<pl>.+), it performs the following steps:

    # ==========================================================================
    # Sentences that start with the operation/function name:

        (?P<name>_\w+_) called with (?P<pl>.+) performs the following steps:

        (?P<name>\w+) is a (?P<kind>host-defined abstract operation) that (.+)
        v=!OP \3

        (?P<name>LocalTZA)\( _t_, _isUTC_ \) is an (?P<kind>implementation-defined algorithm) that (returns .+)
        v=!OP \3

    # ==========================================================================
    # Sentences that (now) start with "!OP":

        # !OP (.+)
        # v=The operation \1

    # ==========================================================================
    # Sentences that start with a parameter name:

        (?P<ps>_\w+_ is a Module Record, and _N2_ is .+).

        (?P<ps>_\w+_ is a possibly empty List of ECMAScript language values).

    # ==========================================================================
    # Miscellaneous starts:

        Given (?P<pl>zero or more arguments), (calls ToNumber .+)
        v=!FUNC \2

        If (Boolean argument) _D_ (.+)
        # ps=\1 _D_
        v=If _D_ \2

        If (the Boolean argument) _S_ (.+)
        # ps=\1 _S_
        v=If _S_ \2

        (.+ of) the Boolean argument _S_.
        v=\1 _S_.

        (.+ depends upon the value of) the _S_ argument:
        v=\1 _S_.

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

        (.+ produces (?P<retn>an integer value) .+)
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

        (Returns (a|the) (?P<retn>Number) .+)
        v=\1

        (Returns a new (?P<retn>_TypedArray_ object) .+)
        v=\1

        (Returns (?P<retn>an Array object) into .+)
        v=\1

        (Returns the .+ (?P<retn>Number value) .+)
        v=\1

        (Returns the integral part of the number .+)
        retn=integer
        v=\1

        (.+ returns (?P<retn>a Number) .+)
        v=\1

        (.+ returns (?P<retn>a String) .+)
        v=\1

        (.+ returns (?P<retn>a new promise) .+)
        v=\1

        (.+ returns (?P<retn>a promise) .+)
        v=\1

        (.+ returns a substring .+)
        retn=String
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

        (.+ returns the local time zone adjustment, .+)
        retn=a Number
        v=\1

        # -----------

        (.+ to) (?P<ps>the \|ModuleSpecifier\| String, _specifier_), (occurring .+)
        v=\1 _specifier_ \3

        (.+ by) (?P<ps>the Script Record or Module Record (_\w+_)).
        v=\1 \3.

        (.*(?P<ps>_\w+_ may also be \*null\*), if .+)
        v=\1

        # ----

        # (.+) the value of (the Boolean argument) _S_.
        # ps=\2 _S_
        # v=\1 the value of _S_.
        # Better to not try to extract parameter info from env-rec preambles?

        (.+, reading the values from) (?P<ps>the _typedArray_ argument object).
        v=\1 _typedArray_.

        (.+, reading the values from) the object (?P<ps>_array_).
        v=\1 _array_.
        # don't include 'object' in ps because that's misleading

        (.+) as follows:
        v=\1.

        (.+ determines .+):
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

def extract_info_from_preamble(preamble_nodes):
    # PR #1914 established a consistent format for abstract operation preambles
    def looks_like_a_standard_ao_preamble(preamble_text):
        return (
            preamble_text.startswith('The abstract operation')
            # and
            # 'takes' in preamble_text
        )
    tao_nodes = [
        preamble_node
        for preamble_node in preamble_nodes
        if looks_like_a_standard_ao_preamble(preamble_node.inner_source_text().strip())
    ]
    if tao_nodes:
        assert len(tao_nodes) == 1
        assert len(preamble_nodes) == 1
        ih = extract_info_from_standard_ao_preamble(preamble_nodes[0])
        if ih: return ih

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

        poi = Header()

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
            'overloaded constructor'                    : 'function property overload',
            'overloaded constructor & function'         : 'function property overload',
            'overloaded function'                       : 'function property overload',
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

        poi.overload_resolver = at_most_one_value('overload_resolver')

        # Have to do this one "out of order"
        # because of possible calls to add_to_description(). 
        poi.description = self.fields['desc']

        pl_values = self.fields['pl']
        if len(pl_values) == 0:
            poi.param_names = None
        elif len(pl_values) == 1:
            get_info_from_parameter_listing_in_preamble(poi, pl_values[0])
        else:
            stderr(f"{poi.name} has multi-pl: {poi.param_names}")
            assert 0

        for ps in self.fields['ps']:
            get_info_from_parameter_sentence_in_ao_preamble(poi, ps)

        also = at_most_one_value('also')
        if also is None:
            poi.also = None
        else:
            # move to apply_ad_hoc_fixes ?
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
        # move to apply_ad_hoc_fixes?

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
    SetMutableBinding(N, V, S)   -> a Boolean or *empty* | throw_
    GetBindingValue(N, S)        -> an ECMAScript language value | throw_ *ReferenceError*
    DeleteBinding(N)             -> a Boolean
    HasThisBinding()             -> a Boolean
    HasSuperBinding()            -> a Boolean
    WithBaseObject()             -> an Object or *undefined*

    # Table 18: Additional Methods of Function Environment Records
    BindThisValue(V) -> TBD
    GetThisBinding() -> an ECMAScript language value | throw_ *ReferenceError*
    GetSuperBase()   -> an Object or *null* or *undefined*

    # Table 20: Additional Methods of Global Environment Records
    # GetThisBinding()                   -> an ECMAScript language value | throw_ *ReferenceError*
    HasVarDeclaration(N)                 -> a Boolean
    HasLexicalDeclaration(N)             -> a Boolean
    HasRestrictedGlobalProperty(N)       -> a Boolean
    CanDeclareGlobalVar(N)               -> a Boolean
    CanDeclareGlobalFunction(N)          -> a Boolean
    CreateGlobalVarBinding(N, D)         -> TBD
    CreateGlobalFunctionBinding(N, V, D) -> TBD

    # Table 21: Additional Methods of Module Environment Records
    CreateImportBinding(N, M, N2) -> TBD
    # GetThisBinding()            -> an ECMAScript language value | throw_ *ReferenceError*

    # Table 39: Abstract Methods of Module Records
    GetExportedNames(exportStarSet)       -> a List of String
    ResolveExport(exportName, resolveSet) -> a ResolvedBinding Record or *null* or a String
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

def extract_info_from_standard_ao_preamble(preamble_node):
    preamble_text = preamble_node.inner_source_text().strip()

    sentences = re.split('(?<=\.) +', preamble_text)

    sentence0 = sentences.pop(0)

    info_holder = PreambleInfoHolder()

    # -----------------------------------
    # The first sentence in the preamble:

    for pattern in [
        r'The abstract operation (?P<name>[\w:/]+) takes (?P<pl>.+) and returns (?P<retn>.+?)\.',
        r'The abstract operation (?P<name>[\w:/]+) takes (?P<pl>.+)\.',
        r'The abstract operation (?P<name><dfn id="\w+" aoid="\w+" oldids="sec-\w+">\w+</dfn>) takes (?P<pl>.+)\.',
    ]:
        mo = re.fullmatch(pattern, sentence0)
        if mo:
            info_holder.add('kind', 'abstract operation')
            for (key, value) in mo.groupdict().items():
                info_holder.add(key, value)
            break
    else:
        oh_warn()
        oh_warn("Starts like std preamble but isn't:")
        oh_warn(preamble_text)
        return None

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
                ('It returns _value_ converted to a numeric value of type Number or BigInt.', 'a Number or a BigInt'),
                ('It returns a new Job Abstract Closure .+', 'a Job Abstract Closure'),
                ('It returns a new promise resolved with _x_.', 'a promise'),
                ('It returns an implementation-approximated value .+', 'a Number'),
                ('It returns either \*false\* or the end index of a match.', '*false* or a non-negative integer'),
                ('It returns the BigInt value that .+', 'a BigInt'),
                ('It returns the global object used by the currently running execution context.', 'an object'),
                ('It returns the loaded value.', 'TBD'),
                ('It returns the sequence of Unicode code points that .+', 'a sequence of Unicode code points'),
                ('It returns the value of the \*"length"\* property of an array-like object.', 'a non-negative integer'),
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
                ('It throws an error .+',     'throws an exception'),
                ('It throws an exception .+', 'throws an exception'),
                ('It throws a \*TypeError\* exception .+', 'throws a *TypeError* exception'),
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

    if oi.description is None:
        oi.description = []
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
    oi.description.append(desc)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_heading(section):
    oi = Header()

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
        'function_property_overload',
        'accessor_property',
        'CallConstruct',
        'CallConstruct_overload',
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
        oi.param_nature_['_args_'] = 'list of values'
        oi.param_nature_['_body_'] = 'a value'
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
        return
    elif parameter_listing == 'up to three arguments _value_, _start_ and _end_':
        # 1 case
        oi.param_names = ['_value_', '_start_', '_end_']
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

        param_items = re.split(', and |, | and ', part)

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
                (r'(.+) VAR',     r'\1'), # XXX prefix with "a"/"an"?
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

    oi = Header()

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

    assert hoi.return_nature_normal is None
    oi.return_nature_normal = poi.return_nature_normal

    assert hoi.return_nature_abrupt is None
    oi.return_nature_abrupt = poi.return_nature_abrupt

    assert hoi.description is None
    oi.description = poi.description

    return oi

# --------------------------------------------------------------------

def oh_warn(*args):
    print(*args, file=oh_inc_f)

def convert_nature_to_tipe(nature):
    if nature == 'TBD': return 'TBD'

    assert 'VAR' not in nature, nature

    t = nature_to_tipe.get(nature, None)
    if t is not None: return t

    print(nature, file=un_f)
    return nature

nature_to_tipe = {
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
        'A Boolean value'   : 'Boolean',
        '*true* or *false*' : 'Boolean',
        'a completion record which, if its [[Type]] is ~normal~, has a [[Value]] which is a Boolean': 'Boolean',
        'a completion record whose [[Type]] is ~normal~ and whose [[Value]] is a Boolean':            'Boolean',

        # String
        'String'          : 'String',
        'a String'        : 'String',
        'a String value'  : 'String',
        'the String value': 'String',
        'a substring'     : 'String',
        '*"default"*, *"number"*, and *"string"*': 'String',
        'passed as a String value': 'String',
        'the String name of a property in _holder_': 'String', # TODO
        'the |ModuleSpecifier| String': 'String', # TODO
        "the name of a binding that exists in _M_'s module Environment Record": 'String', # TODO
        'the name of a TypedArray constructor in <emu-xref href="#table-the-typedarray-constructors"></emu-xref>': 'String', # TODO
        'a String which is the name of a TypedArray constructor in <emu-xref href="#table-the-typedarray-constructors"></emu-xref>': 'String',

        # Symbol

        # Number
        'Number'                     : 'Number',
        'a Number'                   : 'Number',
        'a Number value'             : 'Number',
        'Number value'               : 'Number',
        'an ECMAScript Number value' : 'Number',
        'a nonnegative non-*NaN* Number' : 'Number', # XXX loses info

        # BigInt
        'BigInt'      : 'BigInt',
        'a BigInt'    : 'BigInt',

        # Object
        'Object'      : 'Object',
        'an Object'   : 'Object',
        'an object'   : 'Object',
        'object'      : 'Object',
        'the object'  : 'Object',
        'the argument object': 'Object',
        'an object with a *"constructor"* property whose value is _F_': 'Object', # TODO

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
        'an ECMAScript value, which is usually an object or array, although it can also be a String, Boolean, Number or *null*': 'Tangible_',
        'not a numeric value'           : 'Tangible_', # TODO

    # unofficial 'subtypes' of the above:
        # function_: an object with a [[Call]] internal method
        'function'            : 'function_object_',
        'a Function'          : 'function_object_',
        'a function object'   : 'function_object_',
        'function object'     : 'function_object_',
        'the function object' : 'function_object_',
        'a built-in function object'   : 'function_object_',
        'a function that takes two parameters, _key_ and _value_': 'function_object_',

        # constructor_: an object with a [[Construct]] internal method
        'a constructor function' : 'constructor_object_',
        'a constructor'          : 'constructor_object_',
        'constructor'            : 'constructor_object_',

        # ArrayBuffer_: an object with an [[ArrayBufferData]] internal slot
        'an ArrayBuffer' : 'ArrayBuffer_object_',
        'an ArrayBuffer object' : 'ArrayBuffer_object_',
        'an ArrayBuffer or SharedArrayBuffer' : 'ArrayBuffer_object_ | SharedArrayBuffer_object_',
        'an ArrayBuffer object or a SharedArrayBuffer object' : 'ArrayBuffer_object_ | SharedArrayBuffer_object_',
        'a SharedArrayBuffer' : 'SharedArrayBuffer_object_',
        'a SharedArrayBuffer object' : 'SharedArrayBuffer_object_',

        'the TypedArray instance' : 'TypedArray_object_',
        'a TypedArray instance'   : 'TypedArray_object_',
        'a TypedArray object'     : 'TypedArray_object_',
        '_TypedArray_ object'     : 'TypedArray_object_',

        # 9.4.2
        'an Array exotic object' : 'Array_object_',
        'an Array object'        : 'Array_object_',
        'an array'               : 'Array_object_',

        'an array-like object': 'Object', # TODO

        #? 'a Proxy exotic object' : 'Proxy_object_',

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
        'an integer value'  : 'Integer_',
        'integer'           : 'Integer_',
        'a numeric code point value'     : 'Integer_', # TODO
        'either 0 or a positive integer' : 'NonNegativeInteger_',
        'a nonnegative integer'          : 'NonNegativeInteger_',
        'a non-negative integer'         : 'NonNegativeInteger_',
        'nonnegative integer'            : 'NonNegativeInteger_',
        'an index'                       : 'NonNegativeInteger_',

    # ------------------------------
    # ECMAScript specification types

    # The ones enumerated in 6.2

        # Reference

        # List
        'List' : 'List',
        'a List' : 'List',
        'List of String'                       : 'List of String',
        'a List of String'                     : 'List of String',
        'ECMAScript source text'               : 'Unicode_code_points_',
        'a sequence of Unicode code points'    : 'Unicode_code_points_',
        'a sequence of Unicode code points that is the source text of the syntactic definition of the function to be created' : 'Unicode_code_points_',
        'a List of Unicode code points'        : 'List of Integer_',
        'List of Tangible_'                    : 'List of Tangible_',
        'a List of values'                     : 'List of Tangible_',
        'a list of arguments'                  : 'List of Tangible_',
        'a List of ECMAScript language values' : 'List of Tangible_',
        'a possibly empty List of ECMAScript language values': 'List of Tangible_',
        'a List of ImportEntry Records (see <emu-xref href="#table-39"></emu-xref>)': 'List of ImportEntry Record',

        # Completion

        # Property Descriptor
        'Property Descriptor'   : 'Property Descriptor',
        'a Property Descriptor' : 'Property Descriptor',

        # Environment Record
        'Environment Record' : 'Environment Record',
        'an Environment Record' : 'Environment Record',
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
        'a Realm Record' : 'Realm Record',

        # 8.3 Execution Contexts
        'execution context' : 'execution context',
        'an execution context' : 'execution context',

        # 8.4 Jobs etc
        'a Job Abstract Closure' : 'Job Abstract Closure',

        # 15.1.8 Script Records: Script Record

        # 15.2.1.15 Abstract Module Records: Module Record
        'a Module Record' : 'Module Record',
        'Module Record'   : 'Module Record',
        'Cyclic Module Record': 'Cyclic Module Record',
        'a Cyclic Module Record': 'Cyclic Module Record',

        # 15.2.1.16 Source Text Module Records:
        'a Source Text Module Record': 'Source Text Module Record',
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

        # 24.1.1 [ArrayBuffer Objects] Notation
        'a read-modify-write modification function': 'ReadModifyWrite_modification_closure',

        # 24.4
        'a WaiterList' : 'WaiterList',

        # 25.1
        'a WeakRef': 'WeakRef_object_',

        # 25.2
        'a FinalizationRegistry' : 'FinalizationRegistry_object_',

        # 27.4 Candidate Executions
        'candidate execution'  : 'candidate execution',
        'a candidate execution': 'candidate execution',
        'an execution'         : 'candidate execution', # ???

        'a Shared Data Block event': 'Shared Data Block event',
        'an event in SharedDataBlockEventSet(_execution_)': 'Shared Data Block event',

        # 25.4.1.1: PromiseCapability Record 
        'a PromiseCapability Record'    : 'PromiseCapability Record',
        'a new PromiseCapability Record': 'PromiseCapability Record',

        # 25.4.1.2: PromiseReaction Records

        # 27.1 Memory Model Fundamentals
        'a ReadSharedMemory or ReadModifyWriteSharedMemory event':
            'ReadSharedMemory event | ReadModifyWriteSharedMemory event',
        'a List of WriteSharedMemory or ReadModifyWriteSharedMemory events':
            'List of (WriteSharedMemory event | ReadModifyWriteSharedMemory event)',

    # unofficial 'subtypes' of official spec types:

        'a List of byte values'                       : 'List of Integer_',
        'a List of slot-names'                        : 'List of SlotName_',
        'a List of names of internal slots'           : 'List of SlotName_',
        'a List of ECMAScript Language Type names'    : 'List of LangTypeName_',
        'a List of names of ECMAScript Language Types': 'List of LangTypeName_',
        'a collection of PromiseReactionRecords'      : 'List of PromiseReaction Record',
        'a collection of PromiseReaction Records'     : 'List of PromiseReaction Record',

    # unofficial spec types

        'empty_'      : 'empty_',
        'code unit'   : 'code_unit_',
        'a code unit' : 'code_unit_',
        'a character' : 'character_',

        # 8.7.1 AgentSignifier
        'an agent signifier' : 'agent_signifier_',

        'a parameter list Parse Node'    : 'Parse Node',
        'a body Parse Node'              : 'Parse Node',
        'a Parse Node'                   : 'Parse Node',
        'Parse Node'                     : 'Parse Node',
        'the Parse Node'                 : 'Parse Node',
        'the result of parsing an |AssignmentExpression| or |Initializer|' : 'Parse Node for |AssignmentExpression| | Parse Node for |Initializer|',
        'a Parse Node for |AssignmentExpression| or a Parse Node for |Initializer|': 'Parse Node for |AssignmentExpression| | Parse Node for |Initializer|',
        'a Parse Node for |CaseClause|'  : 'Parse Node for |CaseClause|',
        'a |ScriptBody|'                 : 'Parse Node for |ScriptBody|',
        'the |ScriptBody|'               : 'Parse Node for |ScriptBody|',
        'a Parse Node for |ScriptBody|'  : 'Parse Node for |ScriptBody|',
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

        'one of ~string~ or ~symbol~' : 'PropertyKeyKind_',
        'either ~string~ or ~symbol~' : 'PropertyKeyKind_',

        'throw *RangeError*'             : 'throw_ *RangeError*',
        'throw *TypeError*'              : 'throw_ *TypeError*',
        'throw a *TypeError* exception'  : 'throw_ *TypeError*',
        'throw'                          : 'throw_',
        'throw_'                         : 'throw_',
        'throw_ *ReferenceError*'        : 'throw_ *ReferenceError*',
        'throw_ *TypeError*'             : 'throw_ *TypeError*',
        'throws a *TypeError* exception' : 'throw_ *TypeError*',
        'throws an exception'            : 'throw_',

        'one of the ECMAScript specification types String or Symbol' : 'LangTypeName_',

        'a TypedArray element type'     : 'TypedArray_element_type_',
        'one_of_SeqCst_Unordered'       : 'SharedMemory_ordering_',
        'one_of_SeqCst_Unordered_Init'  : 'SharedMemory_ordering_',
        'either ~SeqCst~ or ~Unordered~': 'SharedMemory_ordering_',
        'one of ~SeqCst~, ~Unordered~, or ~Init~': 'SharedMemory_ordering_',
        'one_of_key_value_key+value'    : 'iteration_result_kind_',
        'one of ~key~, ~value~, or ~key+value~': 'iteration_result_kind_',

    # -----------------------------
    # union of named types

    'a function or an array of Strings and Numbers'              : 'function_object_ | Array_object_',
    'a BigInt or a Number'                                       : 'BigInt | Number',
    'Number or BigInt'                                           : 'Number | BigInt',
    'a Number or BigInt'                                         : 'Number | BigInt',
    'a Number or a BigInt'                                       : 'Number | BigInt',
    'a Number value & *undefined*'                               : 'Number | Undefined',
    'a Number or *undefined*'                                    : 'Number | Undefined',
    'an Array object or *null*'                                  : 'Array_object_ | Null',
    'a Boolean or a non-negative integer'                        : 'Boolean | Integer_',
    '*false* or an integer index'                                : 'Boolean | Integer_',
    '*false* or a non-negative integer'                          : 'Boolean | Integer_',
    '*false* or an IteratorResult object'                        : 'Boolean | IteratorResult_object_',
    '*true*, *false*, or *undefined*'                            : 'Boolean | Undefined',
    'Boolean or Undefined'                                       : 'Boolean | Undefined',
    'a Boolean or *undefined*'                                   : 'Boolean | Undefined',
    'Boolean | empty_'                                           : 'Boolean | empty_',
    'a Boolean or *empty*'                                       : 'Boolean | empty_',
    'an integer (or &infin;)'                                    : 'Integer_ | Infinity_',
    'an integer or &infin;'                                      : 'Integer_ | Infinity_',
    'an Environment Record or *null*'                            : 'Environment Record | Null',
    'an object or null'                                          : 'Object | Null',
    'an object or *null*'                                        : 'Object | Null',
    'an Object or *null*'                                        : 'Object | Null',
    'an Object or *undefined*'                                   : 'Object | Undefined',
    'Object | Undefined'                                         : 'Object | Undefined',
    'Object | Null | Undefined'                                  : 'Object | Null | Undefined',
    'an Object or *null* or *undefined*'                         : 'Object | Null | Undefined',
    'a Property Descriptor or *undefined*'                       : 'Property Descriptor | Undefined',
    'Property Descriptor (or *undefined*)'                       : 'Property Descriptor | Undefined',
    'ResolvedBinding Record | Null | String'                     : 'ResolvedBinding Record | Null | String',
    'a ResolvedBinding Record or *null* or a String'             : 'ResolvedBinding Record | Null | String',
    'a Script Record or Module Record or *null*'                 : 'Script Record | Module Record | Null',
    'the Script Record or Module Record; may also be *null*'     : 'Script Record | Module Record | Null',
    'a Script Record or Module Record; may also be Null'         : 'Script Record | Module Record | Null',
    'a String or Number'                                         : 'String | Number',
    'a String or Symbol'                                         : 'String | Symbol',
    'a String or Symbol or Private Name'                         : 'String | Symbol | Private Name', # PR 1668
    'property key'                                               : 'String | Symbol',
    'a property key'                                             : 'String | Symbol',
    'the property key'                                           : 'String | Symbol',

}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def sub_many(subject, pattern_repls):
    # Apply each of `pattern_repls` to `subject`
    # and return the result.
    result = subject
    for (pattern, repl) in pattern_repls:
        result = re.sub(pattern, repl, result)
    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def prep_for_STA():
    stderr('prep_for_STA ...')

    # headers for SDOs:
    for header in spec.oi_for_sdo_.values():
        header.prep_for_STA()

    # headers for everything else:
    for line_info in spec.info_for_line_[1:]:
        for after_thing in line_info.afters:
            if isinstance(after_thing, Header):
                after_thing.prep_for_STA()
        line_info.msgs = []

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def gather_nonterminals():
    # Find all the Nonterminals that are mentioned in pseudocode,
    # and create a NamedType and a TNode for each.
    #
    # This is a kludge because grammar info doesn't get passed through pickling yet.

    global nonterminals
    nonterminals = set()

    stderr("gather_nonterminals...")

    def recurse_h(hnode):
        if hasattr(hnode, '_syntax_tree'):
            if hnode._syntax_tree is not None:
                recurse_a(hnode._syntax_tree)

        else:
            for child in hnode.children:
                recurse_h(child)

    def recurse_a(anode):
        if isinstance(anode, str): return
        assert isinstance(anode, ANode)
#        if anode.prod.lhs_s == '{CONDITION_1}':
#            print(anode.source_text())
        if anode.prod.lhs_s == '{nonterminal}':
            [nonterminal_name] = anode.children
            if '[' in nonterminal_name or '?' in nonterminal_name: # or '_opt' in nonterminal_name:
                return
            nonterminals.add(nonterminal_name)
        else:
            for child in anode.children:
                recurse_a(child)

    recurse_h(spec.doc_node)
#    sys.exit(1)

    for nonterminal_name in sorted(list(nonterminals)):
        # print(nonterminal_name)
        t = ptn_type_for(nonterminal_name)
        if t not in tnode_for_type_:
            parent_type = T_Parse_Node
            TNode(t, tnode_for_type_[parent_type])
            # which has the side-effect of adding it to tnode_for_type_

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# Handle built-in operations?
built_in_ops = [
    # true built-ins:
    'abs',
    'floor',
    'min',

    # defined as shorthands:
    'Completion',
    'NormalCompletion',
    'ThrowCompletion',
    # 'IfAbruptRejectPromise',

    # not built-in at all,
    # but defined by <emu-eqn>,
    # which I don't want to deal with just yet:
    'DateFromTime',
    'MonthFromTime',
    'YearFromTime',
    'WeekDay',
]

def compute_dependency_levels():
    stderr()
    stderr('analyzing dependencies...')

    for op in operation_named_.values():
        op.summarize_headers()

    # Analyze the definition(s) of each named operation to find its dependencies.
    dep_graph = Graph()
    for (op_name, op) in sorted(operation_named_.items()):
        op.find_dependencies(dep_graph)

    f = shared.open_for_output('deps')
    dep_graph.print_arcs(file=f)

    for vertex in sorted(list(dep_graph.vertices)):
        if vertex not in operation_named_ and vertex not in built_in_ops:
            print("unknown operation:", vertex)

    # Based on all that dependency info, compute the dep levels.
    levels = dep_graph.compute_dependency_levels()

    # Print levels
    for (L, clusters_on_level_L) in enumerate(levels):
        print(file=f)
        print("level %d (%d clusters):" % (L, len(clusters_on_level_L)), file=f)
        for cluster in clusters_on_level_L:
            print("    cluster #___ (%d members, %d direct prerequisite clusters):" % (
                # cluster.number,
                len(cluster.members), len(cluster.direct_prereqs)),
                file=f
            )
            for vertex in cluster.members:
                print("       ", vertex, file=f)

    f.close()
    # sys.exit(0)
    return levels

operation_named_ = {}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX


class Operation:
    def __init__(self, name, kind):
        assert kind in [
            'abstract operation',
            'concrete method',
            'host-defined abstract operation',
            'internal method',
            'numeric method',
            'syntax-directed operation',
            #
            'accessor property',
            'anonymous built-in function',
            'function property',
            'function property overload',
        ]
        self.name = name
        self.kind = kind
        self.headers = []
        self.return_type = None

    def summarize_headers(self):
        assert len(self.headers) > 0
        if len(self.headers) == 1:
            [header] = self.headers
            self.parameters_with_types = header.parameter_types.items()
            self.return_type = header.return_type

        elif self.kind in ['CallConstruct_overload', 'function property overload']:
            pass

        else:
            assert self.kind in ['concrete method', 'internal method', 'numeric method']
            n_params = len(self.headers[0].parameter_types)
            assert all(len(header.parameter_types) == n_params for header in self.headers)

            param_names_ = [set() for i in range(n_params)]
            param_types_ = [set() for i in range(n_params)]
            return_types = set()
            for header in self.headers:
                for (i, (param_name, param_type)) in enumerate(header.parameter_types.items()):
                    param_names_[i].add(param_name)
                    param_types_[i].add(param_type)
                return_types.add(header.return_type)

            self.parameters_with_types = [
                (
                    '|'.join(sorted(list(param_names_[i])))
                ,
                    union_of_types(param_types_[i])
                )
                for i in range(n_params)
            ]
            self.return_type = union_of_types(return_types)

    def find_dependencies(self, dep_graph):
        if self.kind in [
            'function property',
            'anonymous built-in function',
            'CallConstruct',
            'function property overload',
            'CallConstruct_overload',
            'accessor property',
        ]:
            d = spec.info_for_bif_named_
        else:
            d = spec.info_for_op_named_

        dep_graph.add_vertex(self.name)

        if self.name.startswith('<'):
            mo = re.fullmatch(r'<dfn [^<>]+>([^<>]+)</dfn>', self.name)
            assert mo
            name_for_spec_info = mo.group(1)
        elif self.name == 'built-in Set':
            name_for_spec_info = 'Set'
        else:
            name_for_spec_info = self.name

        foo_info = d[name_for_spec_info]
        for callee in sorted(foo_info.callees):
            if self.name in ['ToNumber', 'ToString'] and callee in ['ToPrimitive']: continue # XXX for now
            dep_graph.add_arc(self.name, callee)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Header:
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
        self.return_nature_normal = None
        self.return_nature_abrupt = None
        self.description = None
        self.u_defns = []
        self.line_num = None

    def apply_ad_hoc_fixes(self, section):

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

            if section.parent.parent.section_title in ['Environment Records', 'The Environment Record Type Hierarchy']:
                mo = re.fullmatch(r'(\w+) Environment Records', section.parent.section_title)
                assert mo
                f = mo.group(1).lower() + ' Environment Record'
                if self.for_phrase is None:
                    self.for_phrase = f
                else:
                    assert self.for_phrase == f
            else:
                assert self.for_phrase != ''

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

        # ------------------------------------------------------------

        # For the internal methods of ordinary objects, 
        # the preambles don't say that they're for ordinary objects.
        # (Unlike the internal methods of everything else.)

        if self.kind == 'internal method' and section.parent.section_title == 'Ordinary Object Internal Methods and Internal Slots':
            assert self.for_phrase == '_O_'
            self.for_phrase = 'ordinary object _O_'

        # ------------------------------------------------------------

        # For the overloads of %TypedArray%.prototype.set,
        # the preambles don't say how to resolve theoverload.
        # Instead, that info is given by Asserts in the alg.

        if section.section_title.startswith('%TypedArray%.prototype.set'):
            assert self.kind == 'function property overload'
            assert self.overload_resolver is None

            emu_alg_text = section.block_children[1].inner_source_text()
            mo = re.search(r'\s+1. Assert: (.+?)\. ', emu_alg_text)
            asserted_condition = mo.group(1)
            if asserted_condition == '_array_ is any ECMAScript language value other than an Object with a [[TypedArrayName]] internal slot':
                self.overload_resolver = asserted_condition.replace('_array_', 'the first argument')
                self.param_nature_['_array_'] = 'a value'
            elif asserted_condition == '_typedArray_ has a [[TypedArrayName]] internal slot':
                self.overload_resolver = 'the first argument is an Object with a [[TypedArrayName]] internal slot'
                self.param_nature_['_typedArray_'] = 'an Integer-Indexed object'
            else:
                assert 0, asserted_condition

        # ------------------------------------------------------------

        # For the overloads of _TypedArray_,
        # the overload_resolver lets you infer a type for the first parameter
        # (narrower than Tangible_).

        if section.section_title.startswith('_TypedArray_ ('):
            if self.overload_resolver == 'no arguments':
                pass
            else:
                abbr = self.overload_resolver.replace('at least one argument and the Type of the first argument is ', '')
                if abbr == 'not Object':
                    assert self.param_names == ['_length_']
                    self.param_nature_['_length_'] = 'a primitive value'

                elif abbr == 'Object and that object has a [[TypedArrayName]] internal slot':
                    assert self.param_names == ['_typedArray_']
                    self.param_nature_['_typedArray_'] = 'an Integer-Indexed object'

                elif abbr == 'Object and that object has an [[ArrayBufferData]] internal slot':
                    assert self.param_names[0] == '_buffer_'
                    self.param_nature_['_buffer_'] = 'an ArrayBuffer or SharedArrayBuffer'

                elif abbr == 'Object and that object does not have either a [[TypedArrayName]] or an [[ArrayBufferData]] internal slot':
                    assert self.param_names == ['_object_']
                    self.param_nature_['_object_'] = 'an object'

        # ------------------------------------------------------------

        if section.section_id == 'sec-built-in-function-objects-construct-argumentslist-newtarget':
            # The clause just says that it's like [[Call]] except for one step,
            # so it doesn't say anything about the parameters.
            # Presumably they're the same as for [[Call]].
            # Rather than fish those out, hard-code this:
            assert self.param_nature_['_argumentsList_'] == 'TBD'
            self.param_nature_['_argumentsList_'] = 'List of Tangible_'

    # --------------------------------------------------------------------------

    def finish_initialization(self):
        assert len(self.rest_params) in [0,1]

        if self.param_names is None:
            if self.name == 'Proxy Revocation':
                # It has no parameters,
                # but neither the clause-heading nor the preamble say so.
                self.param_names = []
            else:
                assert 0

        self.param_tipes = OrderedDict()
        for param_name in self.param_names:
            optionality = '(optional) ' if param_name in self.optional_params else ''

            if param_name in self.rest_params:
                assert param_name not in self.optional_params
                if self.name.startswith('Math.'):
                    tipe = 'List of Number'
                else:
                    tipe = 'List of Tangible_'
            else:
                # not a rest parameter
                nature = self.param_nature_.get(param_name, 'TBD')

                # move to apply_ad_hoc_fixes?
                if self.kind in ['function property', 'function property overload', 'anonymous built-in function', 'accessor property']:
                    if self.name.startswith('Math.'):
                        # "Each of the following `Math` object functions
                        # applies the ToNumber abstract operation
                        # to each of its arguments
                        # (in left-to-right order if there is more than one)."
                        #
                        # So the algorithms are written under the assumption
                        # that the parameters have type 'Number'.
                        exp_nature = 'Number'
                    else:
                        exp_nature = 'a value'

                    if nature == 'TBD':
                        nature = exp_nature
                    elif nature == exp_nature:
                        pass
                    elif self.kind == 'function property overload':
                        pass
                        # because the overload-resolver can cause an overload
                        # to only get certain types for some parameters
                    else:
                        oh_warn()
                        oh_warn(f"{self.name}: {exp_nature!r} overrides {nature!r}")
                        nature = exp_nature

                tipe = convert_nature_to_tipe(nature)

            param_tipe = optionality + tipe

            self.param_tipes[param_name] = param_tipe

        if self.return_nature_normal is None:
            if self.name.startswith('Math.'):
                self.return_nature_normal = 'Number'

        self.return_tipe_normal = convert_nature_to_tipe(self.return_nature_normal or 'TBD')
        self.return_tipe_abrupt = convert_nature_to_tipe(self.return_nature_abrupt or 'TBD')

    def prep_for_STA(self):

        if self.for_phrase is None:
            self.for_param_type = None
            self.for_param_name = None
        else:
            mo = re.fullmatch(r'(.+) (_\w+_)', self.for_phrase)
            if mo:
                (for_param_type_string, self.for_param_name) = mo.groups()
            else:
                for_param_type_string = self.for_phrase
                self.for_param_name = None
            for_param_type_string = re.sub(r'^an? ', '', for_param_type_string)

            x = {
                'ECMAScript function object'        : T_function_object_,
                'built-in function object'          : T_function_object_,
                'Proxy exotic object'               : T_Proxy_exotic_object_,
                'Integer-Indexed exotic object'     : T_Integer_Indexed_object_,
                'String exotic object'              : T_Object,
                'arguments exotic object'           : T_Object,
                'immutable prototype exotic object' : T_Object,
                'module namespace exotic object'    : T_Object,
                'ordinary object'                   : T_Object,

                'bound function exotic object'      : T_bound_function_exotic_object_,
                'Array exotic object'               : T_Array_object_,
            }

            if for_param_type_string in x:
                self.for_param_type = x[for_param_type_string]
            else:
                self.for_param_type = parse_type_string(for_param_type_string)

        self.initial_parameter_types = OrderedDict()
        for (param_name, param_type_str) in self.param_tipes.items():
            self.initial_parameter_types[param_name] = parse_type_string(param_type_str)

        self.parameter_types = self.initial_parameter_types.copy()

        if self.also is None:
            self.typed_alsos = {}
        else:
            self.typed_alsos = dict(
                (pn, parse_type_string(ahat_[(pn, pt)]))
                for (pn, pt) in self.also
            )

        if self.return_tipe_normal == 'TBD' and self.return_tipe_abrupt == 'TBD':
            rt = 'TBD'
        elif self.return_tipe_abrupt == 'TBD':
            rt = self.return_tipe_normal
        elif self.return_tipe_normal == 'TBD':
            rt = self.return_tipe_abrupt
        else:
            rt = self.return_tipe_normal + " | " + self.return_tipe_abrupt
        self.initial_return_type = parse_type_string(rt)
        self.return_type = self.initial_return_type

        self.fake_node_for_ = {}
        for pname in self.param_names:
            self.fake_node_for_[pname] = ANode(None, None, 0, 0)
        self.fake_node_for_['normal'] = ANode(None, None, 0, 0)
        self.fake_node_for_['abrupt'] = ANode(None, None, 0, 0)
        self.fake_node_for_['*return*'] = ANode(None, None, 0, 0)

        # -------------------------

        # tweak some parameter/return types:
        # Theoretically, the STA would figure all this out,
        # but (a) it's not that smart, and (b) this saves some churn.
        for (ton, tpn, tot, tnt) in type_tweaks:
            # NUMBER=INTEGER?
            if tot == T_Number and tnt == T_Number: continue
            if ton == self.name:
                try:
                    old_type = self.return_type if tpn == '*return*' else self.parameter_types[tpn]
                except KeyError:
                    print("type_tweaks: %s does not have param named %s" % (ton, tpn))
                    sys.exit(1)
                if tot != old_type:
                    # This can happen when you've read tweaks from the cheater file,
                    # because return-type is split in spec,
                    # and fake_node only points to the abrupt part.
                    # "warning: tweak %s fails old-type check: In %s, existing type of %s is %s, not %s" % (
                    # (ton, tpn, tot, tnt), self.name, tpn, old_type, tot)
                    assert 0, (ton, tpn, tot, tnt, old_type)
                self.change_declared_type(tpn, tnt, tweak=True)

        # -------------------------

        self.t_defns = []

        for foo_defn in self.u_defns:
            if self.kind == 'syntax-directed operation':
                discriminator = foo_defn.discriminator
            else:
                discriminator = self.for_param_type

            if self.kind == 'syntax-directed operation':
                assert (
                    isinstance(discriminator, HTML.HNode)
                        and discriminator.element_name in ['emu-grammar', 'p']
                    or
                    isinstance(discriminator, ANode)
                        and discriminator.prod.lhs_s in ['{h_emu_grammar}', '{nonterminal}']
                )
            elif self.kind in ['concrete method', 'internal method', 'numeric method']:
                assert isinstance(discriminator, Type)
            elif self.kind == 'abstract operation':
                assert discriminator is None
            elif self.kind in [
                'function property',
                'function property overload',
                'accessor property',
                'CallConstruct',
                'CallConstruct_overload',
                'anonymous built-in function',
                'host-defined abstract operation', # HostMakeJobCallback has a default implementation
            ]:
                assert discriminator is None
            else:
                assert 0, self.kind

            assert isinstance(foo_defn.anode, ANode)
            assert foo_defn.anode.prod.lhs_s in [
                '{EMU_ALG_BODY}',
                '{IAO_BODY}',
                '{EXPR}',
                '{NAMED_OPERATION_INVOCATION}',
            ], foo_defn.anode.prod.lhs_s

            self.t_defns.append((discriminator,foo_defn.anode))

        # -------------------------

        if self.name == 'Set' and self.kind == 'function property':
            name_for_op_dict = 'built-in Set'
            # so that it doesn't collide with the abstract operation 'Set'
        elif self.name.startswith('<'):
            mo = re.fullmatch(r'<dfn [^<>]+>([^<>]+)</dfn>', self.name)
            assert mo
            name_for_op_dict = mo.group(1)
        else:
            name_for_op_dict = self.name

        if name_for_op_dict in operation_named_:
            # We've already seen a header for an operation with this name.
            op = operation_named_[name_for_op_dict]
            assert self.kind != 'abstract operation'
            assert op.kind == self.kind
        else:
            # First header for an operation with this name.
            op = Operation(name_for_op_dict, self.kind)
            operation_named_[name_for_op_dict] = op

        op.headers.append(self)

    # ------------------------------------------------------

    def __repr__(self):
        return f"""
            Header:
                name: {self.name}
                kind: {self.kind}
                for : {self.for_param_type}
                params: {', '.join(
                    pn + ' : ' + str(pt)
                    for (pn, pt) in self.parameter_types.items())}
                returns: {self.return_type}
                # defns: {len(self.u_defns)}
        """

    # ------------------------------------------------------

    def lines(self, indentation, mode):
        assert mode in ['dls w initial info', 'messages in algs and dls', 'dls w revised info']

        ind = ' ' * indentation
        lines = []
        def pwi(s=''): # put-with-indentation
            lines.append('' if s == '' else ind + s)

        # ---------------------------------------

        pwi(f"<dl class='header'>")
        pwi()
        pwi(f"  <dt>op kind</dt>")
        pwi(f"  <dd>{self.kind}</dd>")
        pwi()
        pwi(f"  <dt>name</dt>")
        pwi(f"  <dd>{self.name}</dd>")

        if self.for_phrase:
            pwi()
            pwi(f"  <dt>for</dt>")
            pwi(f"  <dd>{self.for_phrase}</dd>")

        if self.overload_resolver:
            pwi()
            pwi(f"  <dt>overload selected when called with</dt>")
            pwi(f"  <dd>{self.overload_resolver}</dd>")

        kludge = None

        # ---------------------------------------
        def put_prefix_and_type(prefix, ptype):
            nonlocal kludge
            if ptype == T_0:
                if mode == 'messages in algs and dls':
                    pwi(f"      <li>{prefix} : TBD</li>")
                    kludge = 3
                else:
                    # show nothing
                    pass
            else:
                s = ptype.unparse()
                pwi(f"      <li>{prefix} : {s}</li>")
                kludge = len(s)
        # ---------------------------------------

        assert self.param_names is not None
        if len(self.param_names) == 0:
            pwi()
            pwi(f"  <dt>parameters</dt>")
            pwi(f"  <dd>none</dd>")

        else:
            pwi()
            pwi(f"  <dt>parameters</dt>")
            pwi(f"  <dd>")
            pwi(f"    <ul>")

            pn_max_width = max(
                len(param_name)
                for param_name in self.param_names
            )

            if mode == 'dls w initial info':
                for (param_name, param_tipe) in self.param_tipes.items():
                    prefix = param_name.ljust(pn_max_width)
                    pwi(f"      <li>{prefix} : {param_tipe}</li>")

            else:
                if mode == 'messages in algs and dls':
                    params = self.initial_parameter_types
                else:
                    params = self.parameter_types

                for (pn, pt) in params.items():
                    put_prefix_and_type(pn.ljust(pn_max_width), pt)

                    # XXX Cases where operation_headers types the parameter as 'NonNegativeInteger_',
                    # but then that gets translated to 'Integer',
                    # so that's how it appears here.
                    # - ArrayCreate              : _length_
                    # - CodePointAt              : _position_
                    # - GetModifySetValueInBuffer: _byteIndex_
                    # - GetWaiterList            : _i_
                    # - RemoveWaiters            : _c_
                    # - ComposeWriteEventBytes   : _byteIndex_

                    if mode == 'messages in algs and dls':
                        p_node = self.fake_node_for_[pn]
                        if hasattr(p_node, 'errors'):
                            for msg in p_node.errors:
                                lines.append('-' * (indentation + 6 + 4 + pn_max_width + 3) + '^' * kludge)
                                lines.append('>>> ' + msg)
                                lines.append('')

            pwi(f"    </ul>")
            pwi(f"  </dd>")

        # -------------------------

        if self.also:
            pwi()
            pwi(f"  <dt>also has access to</dt>")
            pwi(f"  <dd>")
            pwi(f"    <ul>")

            max_width = max(len(var_name) for (var_name,_) in self.also)

            if mode == 'dls w initial info':
                for (var_name, expl) in self.also:
                    pwi(f"      <li>{var_name: <{max_width}} : {expl}</li>")
            else:
                for (var_name, vt) in self.typed_alsos.items():
                    pwi(f"      <li>{var_name: <{max_width}} : {vt}</li>")

            pwi(f"    </ul>")
            pwi(f"  </dd>")

        # -------------------------

        pwi()
        pwi(f"  <dt>returns</dt>")
        pwi(f"  <dd>")
        pwi(f"    <ul>")

        if mode == 'dls w initial info':
            pwi(f"      <li>normal : {self.return_tipe_normal}</li>")
            pwi(f"      <li>abrupt : {self.return_tipe_abrupt}</li>")

        else:
            if mode == 'messages in algs and dls':
                rt = self.initial_return_type
            else:
                rt = self.return_type

            if rt == T_TBD:
                abrupt_part = T_TBD
                normal_part = T_TBD
            else:
                (abrupt_part, normal_part) = rt.split_by(T_Abrupt)

            put_prefix_and_type('normal', normal_part)
            put_prefix_and_type('abrupt', abrupt_part)

            if mode == 'messages in algs and dls':
                p_node = self.fake_node_for_['*return*']
                if hasattr(p_node, 'errors'):
                    for msg in p_node.errors:
                        lines.append('-' * (indentation + 6 + 4 + 6 + 3) + '^' * kludge)
                        lines.append('>>> ' + msg)
                        lines.append('')

        pwi(f"    </ul>")
        pwi(f"  </dd>")

        # -------------------------

        if self.description:
            pwi()
            pwi(f"  <dt>description</dt>")
            assert isinstance(self.description, list)
            assert len(self.description) > 0
            desc = ' '.join(self.description)
            desc = re.sub(r'^(!OP|!FUNC|!CM) ', '', desc)
            desc = re.sub(r'^(It|This operation|The job) ', '', desc)
            desc = (desc
                .replace('!OP', 'This operation')
                .replace('!FUNC', 'This function')
            )
            pwi(f"  <dd>{desc}</dd>")

            # if len(self.description) > 1: make separate <p> elements?

        pwi(f"</dl>")

        return lines

    # ------------------------------------------------------

    def make_env(self):
        e = Env()

        if self.for_param_name is not None:
            assert self.for_param_type is not None
            e.vars[self.for_param_name] = self.for_param_type

        for (pn, pt) in self.parameter_types.items():
            assert isinstance(pt, Type)
            e.vars[pn] = pt

        for (vn, vt) in self.typed_alsos.items():
            assert isinstance(vt, Type)
            e.vars[vn] = vt

        e.vars['*return*'] = self.return_type

        return e

    # ----------------------------------------------------------------

    def change_declared_type(self, pname, new_t, tweak=False):
        if pname == '*return*':
            # if new_t == T_Reference: pdb.set_trace()
            old_t = self.return_type
            self.return_type = new_t
        else:
            old_t = self.parameter_types[pname]
            self.parameter_types[pname] = new_t

        assert old_t != new_t

        verb = 'tweak' if tweak else 'change'
        change = "%s%s type of `%s` from `%s` to `%s`" % (
            g_level_prefix, verb, pname, old_t, new_t)
        node = self.fake_node_for_[pname]
        node._new_t = new_t
        install_error(node, change)

        #!!! print("EDIT: In a header for `%s`: %s" % (self.name, change))
        # if self.name == 'LabelledEvaluation' and pname == '_labelSet_': pdb.set_trace()

# ------------------------------------------------------------------------------

# "also has access to" type info
ahat_ = {
    ('_comparefn_', 'from the current invocation of the `sort` method'):
        'Undefined | function_object_',

    # ('_reviver_', 'from the above parse function'):
    #     'function_object_',
    # ^ obsoleted by the merge of PR #1879

    # ('_ReplacerFunction_', 'from the invocation of the `stringify` method'):
    #     'function_object_ | Undefined',
    # ('_stack_'       , 'from the current invocation of the `stringify` method'): 'List of Object',
    # ('_indent_'      , 'from the current invocation of the `stringify` method'): 'String',
    # ('_gap_'         , 'from the current invocation of the `stringify` method'): 'String',
    # ('_PropertyList_', 'from the current invocation of the `stringify` method'): 'Undefined | List',
    # ^ obsoleted by the merge of PR #1890

    ('_IgnoreCase_', 'Boolean'): 'Boolean',

    ('_Input_'           , 'from somewhere'): 'List of character_',
    ('_InputLength_'     , 'from somewhere'): 'Integer_',
    ('_NcapturingParens_', 'from somewhere'): 'Integer_',
    ('_DotAll_'          , 'from somewhere'): 'Boolean',
    ('_IgnoreCase_'      , 'from somewhere'): 'Boolean',
    ('_Multiline_'       , 'from somewhere'): 'Boolean',
    ('_Unicode_'         , 'from somewhere'): 'Boolean',

    ('_comparefn_' , 'from the `sort` method'): 'function_object_ | Undefined',
    ('_buffer_'    , 'from the `sort` method'): 'ArrayBuffer_object_ | SharedArrayBuffer_object_',
}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

subtype_memo = {}
split_memo = {}

class Type(tuple):

    def set_of_types(self):
        return self.member_types if isinstance(self, UnionType) else frozenset([self])

    def __or__(A, B):
        if A == B: return A
        # check subtyping?
        A_members = A.set_of_types()
        B_members = B.set_of_types()
        u = maybe_UnionType(A_members | B_members)
        # print(A, '|', B, '=', u)
        return u

    # -----------------------------------------------------

    # @memoize()
    def is_a_subtype_of_or_equal_to(A, B):

        if (A,B) in subtype_memo:
            return subtype_memo[(A,B)]
        # No speed-up? 

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if T_TBD in A_members or T_TBD in B_members:
            result = False

        elif A_members <= B_members:
            result = True
        elif A_members > B_members:
            result = False

        else:
            # A is a subtype of B iff every A_member is a subtype of B.
            result = all(
                # and an A_member is a subtype of B
                # iff it is a subtype of some B_member
                any(
                    member_is_a_subtype_or_equal(A_member, B_member)
                    for B_member in B_members
                )
                for A_member in A_members
            )

        if 0:
            print(
                "SUBTYPING:",
                A,
                "is" if result else "is not",
                "a subtype of",
                B
            )

        subtype_memo[(A,B)] = result

        return result

    # -----------------------------------------------------

    def split_by(A, B):
        # Return a pair of types that partition A
        # (i.e., two disjoint types whose union is A):
        # one that is a subtype of (or equal to) B,
        # and one that is outside of B.
        # (Either can be T_0.)

        # if A == T_TBD and B == ListType(T_String): pdb.set_trace()

        if 0:
            (outside_B, inside_B, _) = compare_types(A, B)
            return (inside_B, outside_B)

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if (A,B) in split_memo:
            return split_memo[(A,B)]

        A_memtypes = A.set_of_types()
        B_memtypes = B.set_of_types()

        # A few cases that can be handled quickly:
        if A_memtypes == B_memtypes:
            inside_B  = A # or B
            outside_B = T_0

        elif A_memtypes <= B_memtypes:
            inside_B  = A
            outside_B = T_0

        elif B_memtypes <= A_memtypes:
            inside_B  = B
            outside_B = maybe_UnionType(A_memtypes - B_memtypes)

        else:
            # The general case:
            inside_B = set()
            outside_B = set()

            def recurse(A_subtypes, B_subtypes):
                for a in A_subtypes:
                    assert isinstance(a, Type)

                    # Treat T_TBD like Top
                    if a == T_TBD: a = T_Top_ # assert 0

                    if a.is_a_subtype_of_or_equal_to(B):
                        inside_B.add(a)
                    else:
                        # get a list of the B_subtypes that are subtypes of a
                        bs_within_a = [
                            b
                            for b in B_subtypes
                            if b.is_a_subtype_of_or_equal_to(a)
                        ]
                        if bs_within_a:
                            # break down `a`
                            if a == T_List:
                                if len(bs_within_a) == 1:
                                    [bwa] = bs_within_a
                                    if isinstance(bwa, ListType):
                                        inside_B.add(bwa)
                                        outside_B.add(ListType(T_other_))
                                        # pdb.set_trace()
                                    else:
                                        assert 0
                                else:
                                    assert 0
                            elif isinstance(a, ListType):
                                if a == ListType(T_character_) and bs_within_a == [ListType(T_code_point_)]:
                                    inside_B.add(ListType(T_code_point_))
                                    outside_B.add(ListType(T_code_unit_))
                                elif a == ListType(T_character_) and bs_within_a == [ListType(T_code_unit_)]:
                                    inside_B.add(ListType(T_code_unit_))
                                    outside_B.add(ListType(T_code_point_))
                                elif a == ListType(T_Tangible_) and bs_within_a == [ListType(T_Number)]:
                                    inside_B.add(ListType(T_Number))
                                    outside_B.add(ListType(T_Tangible_)) # XXX T_Tangible_ - T_Number (TypedArrayCreate)
                                else:
                                    assert 0
                            else:
                                tnode = tnode_for_type_[a]
                                a_imm_subtypes = [child.type for child in tnode.children]
                                recurse(a_imm_subtypes, bs_within_a)
                        else:
                            # no B_subtype is within `a`
                            # so `a` must be disjoint from B
                            outside_B.add(a)

            recurse(A_memtypes, B_memtypes)

            inside_B  = maybe_UnionType(inside_B)
            outside_B = maybe_UnionType(outside_B)

        print("%s :: %s  ===>  %s  ///  %s" %
            (A, B, outside_B, inside_B),
            file=split_types_f)

        result = (inside_B, outside_B)
        split_memo[(A,B)] = result
        return result


def member_is_a_subtype_or_equal(A, B):
    assert not isinstance(A, UnionType); assert A != T_TBD
    assert not isinstance(B, UnionType); assert B != T_TBD

    if A == B: return True

    if isinstance(A, NamedType):
        if isinstance(B, NamedType):
            A_tnode = tnode_for_type_[A]
            B_tnode = tnode_for_type_[B]
            if A_tnode.level < B_tnode.level:
                # A is higher in the hierarchy than B
                # (not necessarily an ancestor of B, but at a higher level).
                return False
            elif A_tnode.level == B_tnode.level:
                # They're at the same level in the hierarchy.
                # But we've already tested them for equality,
                # so they must be siblings/cousins.
                return False
            elif A_tnode.level > B_tnode.level:
                # A is at a lower level than B in the hierarchy.
                # So it might be a subtype.
                n_levels_diff = A_tnode.level - B_tnode.level
                tnode = A_tnode
                for i in range(n_levels_diff): tnode = tnode.parent
                assert tnode.level == B_tnode.level
                return (tnode is B_tnode)
            else:
                assert 0, "can't happen"
        else:
            # e.g., is Foo a subtype of List of Foo?
            # I don't think there's much need to say it is.
            return False

    elif isinstance(A, ListType):
        if isinstance(B, ListType):
            return (A.element_type.is_a_subtype_of_or_equal_to(B.element_type))
        elif isinstance(B, NamedType):
            return (T_List.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ThrowType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, ThrowType):
        if isinstance(B, ThrowType):
            return (A.error_type.is_a_subtype_of_or_equal_to(B.error_type))
        elif isinstance(B, NamedType):
            return (T_throw_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, ProcType):
        if isinstance(B, ProcType):
            if A.param_types == B.param_types:
                return A.return_type.is_a_subtype_of_or_equal_to(B.return_type)
            else:
                assert 0, (A, B)
        elif isinstance(B, NamedType):
            return (T_proc_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
            return False
        else:
            assert 0, (A, B)

    else:
        assert 0, (A, B)


    # --------------------------------------------------------------------------

class TBDType(Type):
    __slots__ = ()
    def __new__(cls):
        return tuple.__new__(cls, ('TBDType',))
    def __repr__(self): return "%s()" % self
    def __str__(self): return 'TBD'
    def unparse(self, parenthesuze=False): return 'TBD'

class NamedType(Type):
    __slots__ = ()
    def __new__(cls, name):
        assert isinstance(name, str)
        assert re.fullmatch(r'[\w -]+', name), name
        assert not name.startswith('a ')
        return tuple.__new__(cls, ('NamedType', name))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return self.name
    def unparse(self, parenthesize=False):
        if self.name.startswith('PTN_'):
            x = 'Parse Node for |%s|' % self.name.replace('PTN_','')
            if parenthesize: x = '(%s)' % x
            return x
        else:
            return self.name
    name = property(itemgetter(1))

class ListType(Type):
    __slots__ = ()
    def __new__(cls, element_type):
        return tuple.__new__(cls, ('ListType', element_type))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "List of %s" % str(self.element_type)
    def unparse(self, _=False): return "List of %s" % self.element_type.unparse(True)
    element_type = property(itemgetter(1))

class TupleType(Type):
    __slots__ = ()
    def __new__(cls, component_types):
        return tuple.__new__(cls, ('TupleType', component_types))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "(%s)" % str(self.component_types)
    def unparse(self, _=False): return "(%s)" % self.component_types.unparse(True)
    component_types = property(itemgetter(1))

class ThrowType(Type):
    __slots__ = ()
    def __new__(cls, error_type):
        return tuple.__new__(cls, ('ThrowType', error_type))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "throw_(%s)" % str(self.error_type)
    def unparse(self, _=False): return "throw_ *%s*" % self.error_type.unparse(True)
    error_type = property(itemgetter(1))

class ProcType(Type):
    __slots__ = ()
    def __new__(cls, param_types, return_type):
        return tuple.__new__(cls, ('ProcType', tuple(param_types), return_type))
    def __repr__(self): return "%s(%r, %r)" % self
    def __str__(self):
        if self == T_Continuation:
            return "Continuation"
        elif self == T_Matcher:
            return "Matcher"
        elif self == T_ReadModifyWrite_modification_closure:
            return "ReadModifyWrite_modification_closure"
        elif self == T_RegExpMatcher_:
            return "RegExpMatcher_"
        else:
            return "(%s -> %s)" % (self.param_types, self.return_type)
    def unparse(self, _=False): return str(self)

    param_types = property(itemgetter(1))
    return_type = property(itemgetter(2))

class UnionType(Type):
    # A union of (non-union) types.
    # Must satisfy the constraint that no member-type
    # is a subtype or supertype of any other member-type.
    # (XXX: Should check that in __new__.)

    __slots__ = ()
    def __new__(cls, member_types):
        assert len(member_types) != 1
        for type in member_types:
            assert not isinstance(type, UnionType)
        return tuple.__new__(cls, ('UnionType', frozenset(member_types)))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "(%s)" % ' | '.join(sorted(map(str, self.member_types)))

    def unparse(self, parenthesize=False):
        if T_not_passed in self.member_types:
            # This only makes sense for a top-level type,
            # but I don't think it'll occur anywhere else.
            prefix = '(optional) '
            member_types = set(self.member_types)
            member_types.remove(T_not_passed)
        else:
            prefix = ''
            member_types = self.member_types

        x = ' | '.join(sorted(
            member_type.unparse()
            for member_type in member_types
        ))
        if parenthesize: x = '(' + x + ')'
        return prefix + x

    member_types = property(itemgetter(1))

T_0 = UnionType([])

def maybe_UnionType(member_types):
    assert not isinstance(member_types, Type)
    if len(member_types) == 1:
        return list(member_types)[0]
    else:
        return UnionType(member_types)

# ------------------------------------------------------------------------------

def parse_type_string(text):
    assert isinstance(text, str)
    assert text != ''

    mo = re.match(r'^\(optional\) (.+)$', text)
    if mo:
        is_optional = True
        text = mo.group(1)
    else:
        is_optional = False

    t = ptsr(text)

    if is_optional:
        t = t | T_not_passed

    return t

def type_for_environment_record_kind(kind):
    return parse_type_string(kind.source_text() + ' Environment Record')

def ptsr(text):
    assert text != ''
    for (pattern, lam) in [
        (r'\(([^()]*)\) -> (.+)', text_to_proc_type),
        (r'(List of \([^()]+\)) \| ([\w ]+)', lambda mo: UnionType([ptsr(mo.group(1)), ptsr(mo.group(2))])),
        (r'List of \(([^()]+)\)', lambda mo: ListType(ptsr(mo.group(1)))),
        (r'List of ([\w ]+)',     lambda mo: ListType(ptsr(mo.group(1)))),
        (r'Parse Node for \|(\w+)\|', lambda mo: ptn_type_for(mo.group(1))),
        (r'.+ \| .+',         lambda mo: UnionType([ptsr(alt) for alt in text.split(' | ')])),
        (r'throw_ \*(\w+)\*', lambda mo: ThrowType(ptsr(mo.group(1)))),
        (r'\w+( \w+)*',       lambda mo: maybe_NamedType(mo.group(0))),
    ]:
        mo = re.match('^' + pattern + '$', text)
        if mo:
            memtype = lam(mo)
            # assert memtype in tnode_for_type_, memtype
            return memtype
    assert 0, repr(text)

def text_to_proc_type(mo):
    (param_text, return_text) = mo.groups()

    if re.match('^ *$', param_text):
        param_types = []
    else:
        param_types = [parse_type_string(tx) for tx in param_text.split(', ')]

    if re.match(r'^\([^()]+\)$', return_text):
        return_text = return_text[1:-1]
    return_type = parse_type_string(return_text)

    return ProcType(param_types, return_type)

def ptn_type_for(nonterminal):
    if isinstance(nonterminal, str):
        if nonterminal.startswith('|'):
            assert nonterminal.endswith('|')
            nont_basename = nonterminal[1:-1]
        else:
            nont_basename = nonterminal
        optionality = ''
    elif isinstance(nonterminal, ANode):
        assert nonterminal.prod.lhs_s == '{nonterminal}'
        [nonterminal_ref] = nonterminal.children
        mo = re.fullmatch(r'\|(\w+)((?:\[[^][]+\])?)((?:_opt)?)\|', nonterminal_ref)
        assert mo
        [nont_basename, params, optionality] = mo.groups()
    else:
        assert 0
    type_name = 'PTN_' + nont_basename + optionality
    type = NamedType(type_name)
    return type

def type_for_TYPE_NAME(type_name):
    assert isinstance(type_name, ANode)
    assert type_name.prod.lhs_s == '{TYPE_NAME}'
    return NamedType(type_name.source_text())

# ------------------------------------------------------------------------------

named_type_hierarchy = {
    'Top_': {
        'Abrupt' : {
            'continue_': {},
            'break_': {},
            'return_': {},
            'throw_': {},
        },
        'Normal': {
            'Absent': { # not sure this is at the right place in the hierarchy.
                'not_passed': {},    # for an optional parameter
                'not_in_record': {}, # for an optional field of a record
                'not_in_node': {},   # for an optional child of a node
                'not_set': {},       # for a metavariable that might not be initialized
                'not_returned': {},  # for when control falls off the end of an operation
            },
            'Tangible_': {
                'Primitive': {
                    'Undefined': {},
                    'Null': {},
                    'Boolean': {},
                    'String': {},
                    'Symbol': {},
                    'Number': {
                        'Integer_': {},
                        #? 'NonNegativeInteger_': {}
                        'OtherNumber_': {},
                    },
                    'BigInt': {},
                },
                'Object': {
                    'Error': {
                        'AggregateError': {},
                        'ReferenceError': {},
                        'SyntaxError': {},
                        'TypeError': {},
                        'RangeError': {},
                        'other_Error_': {},
                    },
                    # 'Proxy': {},
                    # 'RegExp': {},
                    'ArrayBuffer_object_': {},
                    'Array_object_': {},
                    'AsyncGenerator_object_': {},
                    'FinalizationRegistry_object_': {},
                    'Integer_Indexed_object_': {},
                    'Iterator_object_': {},
                    'IteratorResult_object_': {},
                    'Promise_object_': {},
                    'SharedArrayBuffer_object_': {},
                    'String_exotic_object_': {},
                    'TypedArray_object_': {},
                    'WeakMap_object_': {},
                    'WeakRef_object_': {},
                    'WeakSet_object_': {},
                    'function_object_': {
                        'constructor_object_': {}, # XXX This is actually orthogonal to Proxy/Bound/other
                        'Proxy_exotic_object_': {},
                        'bound_function_exotic_object_': {},
                        'other_function_object_': {},
                    },
                    'other_Object_': {},
                },
            },
            'Intangible_': {
                'AssignmentTargetType_': {},
                'Abstract Closure': {}, # hm
                'CharSet': {},
                'ClassElementKind_': {},
                'Data Block': {},
                'FunctionKind1_': {},
                'FunctionKind2_': {},
                'event_pair_': {},
                'IEEE_binary32_': {},
                'IEEE_binary64_': {},
                'Infinity_': {},
                'IterationKind_': {},
                'IteratorKind_': {},
                'LangTypeName_': {},
                'LhsKind_': {},
                'List': {},
                'MatchResult': {
                    'State': {},
                    'match_failure_': {},
                },
                'MathReal_': {
                    'MathInteger_': {},
                    'MathOther_': {},
                },
                'Parse Node' : {
                    'PTN_ForBinding': {},
                    'PTN_Script': {},
                    'PTN_Pattern': {},
                },
                'PropertyKeyKind_': {},
                'Record': {
                    'Agent Record': {},
                    'Agent Events Record': {},
                    'AsyncGeneratorRequest Record': {},
                    'Chosen Value Record': {},
                    'ClassFieldDefinition Record': {}, # PR 1668
                    'Environment Record': {
                        'declarative Environment Record': {
                            'function Environment Record': {},
                            'module Environment Record': {},
                        },
                        'object Environment Record': {},
                        'global Environment Record': {},
                    },
                    'ExportEntry Record': {},
                    'ExportResolveSet_Record_': {},
                    'FinalizationRegistryCellRecord_': {},
                    'GlobalSymbolRegistry Record': {},
                    'ImportEntry Record': {},
                    'ImportMeta_record_': {},
                    'Intrinsics Record': {},
                    'JSON_Stringify_state_record_': {},
                    'JobCallback Record': {},
                    'MapData_record_': {},
                    'Module Record': {
                        'Cyclic Module Record': {
                            'Source Text Module Record': {},
                            'other Cyclic Module Record': {},
                        },
                        'other Module Record': {},
                    },
                    # 'PendingJob': {}, # PR 1597
                    'PrivateField': {}, # PR 1668
                    'Private Name': {}, # PR 1668
                    'PromiseCapability Record': {},
                    'PromiseReaction Record': {},
                    'Property Descriptor': {
                        # subtypes data and accessor and generic?
                    },
                    'Realm Record': {},
                    'ResolvedBinding Record': {},
                    'ResolvingFunctions_record_': {},
                    'Script Record': {},
                    #
                    'boolean_value_record_': {},
                    'candidate execution': {},
                    'CodePointAt_record_': {},
                    'event_': {
                        'Shared Data Block event': {
                            'ReadModifyWriteSharedMemory event': {},
                            'ReadSharedMemory event': {},
                            'WriteSharedMemory event': {},
                        },
                        'Synchronize event': {},
                        'host-specific event': {},
                    },
                    'integer_value_record_': {},
                    'iterator_record_': {},
                    'methodDef_record_': {},
                    'templateMap_entry_': {},
                },
                'Reference': {},
                'Relation': {},
                'Set': {},
                'Shared Data Block': {},
                'SharedMemory_ordering_': {},
                'SlotName_': {},
                'TrimString_where_': {},
                'TypedArray_element_type_': {},
                'Unicode_code_points_': {},
                'WaiterList' : {},
                'agent_signifier_' : {},
                'alg_steps': {},
                'character_': {
                    'code_unit_': {},
                    'code_point_': {},
                },
                'completion_kind_': {},
                'constructor_kind_': {},
                'empty_': {},
                'iteration_result_kind_': {},
                'execution context': {},
                'generator_state_': {},
                'grammar_symbol_': {},
                'host_defined_': {},
                'integrity_level_': {},
                'module_record_status_': {},
                'numeric_primitive_type_': {},
                'proc_': {},
                'promise_state_': {},
                'property_': {
                    'data_property_': {},
                    'accessor_property_': {},
                },
                'settlement_type_': {},
                'this_binding_status_': {},
                'this_mode': {},
                'this_mode2_': {},
                'tuple_': {},
                'other_': {},
            },
        },
    }
}

tnode_for_type_ = {}

class TNode:
    def __init__(self, type, parent):
        self.type = type
        self.parent = parent

        self.children = []

        if parent is None:
            self.level = 0
        else:
            self.level = parent.level + 1
            parent.children.append(self)

        tnode_for_type_[type] = self

def traverse(typesdict, p):
    for (type_name, subtypesdict) in typesdict.items():
    # sorted(typesdict.items(), key=lambda tup: 1 if tup[0] == 'List' else 0):
        assert isinstance(type_name, str)
        t = NamedType(type_name)
        #
        variable_name = 'T_' + type_name.replace(' ', '_')
        globals()[variable_name] = t
        #
        tnode = TNode(t, p)
        traverse(subtypesdict, tnode)

stderr("initializing the type hierarchy...")
traverse(named_type_hierarchy, None)

troot = tnode_for_type_[T_Top_]

def ensure_tnode_for(type):
    assert isinstance(type, Type)
    if type in tnode_for_type_:
        return tnode_for_type_[type]
    else:
        if isinstance(type, NamedType):
            assert 0, type
        elif isinstance(type, ThrowType):
            parent_type = T_throw_
        elif isinstance(type, ListType):
            parent_type = T_List # XXX but this fails to capture subtypes within
        elif isinstance(type, ProcType):
            parent_type = T_proc_
        elif isinstance(type, TupleType):
            parent_type = T_tuple_
        else:
            assert 0, type
        return TNode(type, tnode_for_type_[parent_type])
        # which has the side-effect of adding it to tnode_for_type_

ensure_tnode_for( ListType(T_other_) )
ensure_tnode_for( ProcType((), T_other_) )
ensure_tnode_for( ThrowType(T_other_) )

# ------------------------------------------------------------------------------

T_TBD = TBDType()

T_Continuation    = ProcType([T_State                ], T_MatchResult)
T_Matcher         = ProcType([T_State, T_Continuation], T_MatchResult)
T_RegExpMatcher_  = ProcType([T_String, T_Integer_   ], T_MatchResult)
T_Job             = ProcType([                       ], T_Undefined)

T_ReadModifyWrite_modification_closure = ProcType([ListType(T_Integer_), ListType(T_Integer_)], ListType(T_Integer_))

T_captures_entry_ = ListType(T_character_) | T_Undefined
T_captures_list_  = ListType(T_captures_entry_)

# T_Unicode_code_points_ = ListType(T_code_point_)

def maybe_NamedType(name):
    if name == 'TBD':
        return T_TBD
    elif name == 'Continuation':
        return T_Continuation
    elif name == 'Matcher':
        return T_Matcher
    elif name == 'RegExpMatcher_':
        return T_RegExpMatcher_
    elif name == 'Job Abstract Closure':
        return T_Job
    elif name == 'ReadModifyWrite_modification_closure':
        return T_ReadModifyWrite_modification_closure
    elif name == 'NonNegativeInteger_':
        # There are 5 places where structify yields this parameter type.
        # But as far as STA is concerned, it's just an alias for Integer_.
        return T_Integer_
    else:
        return NamedType(name)

type_tweaks_filename = '_type_tweaks.txt'
# type_tweaks_filename = '_operation_headers/cheater_type_tweaks'
type_tweaks = []
for line in open(type_tweaks_filename, 'r'):
    [op_name, p_name, old_t_str, new_t_str] = re.split(' *; *', line.rstrip())
    type_tweaks.append( (
        op_name,
        p_name,
        parse_type_string(old_t_str),
        parse_type_string(new_t_str),
    ))

# UpdateEmpty: _completionRecord_, *return

# InitializeReferencedBinding: _V_ and _W_ can be Abrupt
# InitializeBoundName return?
# ToPrimitive _PreferredType_
# OrdinaryHasInstance: _C_, _O_
# IteratorNext: _value_
# IteratorStep: return
# LoopContinues: _completion_
# PerformEval: _x_ + return
# RegExpInitialize: _pattern_, _flags_
# RegExpCreate: _P_, _F_
# IteratorDestructuringAssignmentEvaluation: return
# KeyedDestructuringAssignmentEvaluation: return
# LabelledEvaluation: return
# ForBodyEvaluation: return
# ForIn/OfBodyEvaluation: return
# BoundNames: return


# ------------------------------------------------------------------------------

# memoize
def union_of_types(types):
    if len(types) == 0: return T_0

    types1 = set(types)

    # Treat T_TBD like T_0,
    # i.e. the union-type with no member-types.
    # i.e., It has no effect on a union of types.
    types1.discard(T_TBD)

    if len(types1) == 0:
        # It must be that all types were T_TBD
        return T_TBD
    elif len(types1) == 1:
        return types1.pop()

    # ----------------------------

    memtypes = set()
    for t in types1:
        if isinstance(t, UnionType):
            for mt in t.member_types:
                assert not isinstance(mt, UnionType)
                memtypes.add(mt)
        else:
            memtypes.add(t)

    memtypes.discard(T_TBD)
    assert len(memtypes) > 0

    list_memtypes = []
    other_memtypes = []
    for mt in memtypes:
        if mt == T_List or isinstance(mt, ListType):
            list_memtypes.append(mt)
        else:
            other_memtypes.append(mt)

    result_memtypes = union_of_list_memtypes(list_memtypes) + union_of_other_memtypes(other_memtypes)

    assert result_memtypes

    if len(result_memtypes) == 1:
        result = result_memtypes.pop()
    else:
        result = UnionType(result_memtypes)

    # print("union of", ', '.join(str(t) for t in types), " = ", result)

    return result

# ------------------------------------------------------------------------------

def union_of_list_memtypes(list_memtypes):

    if len(list_memtypes) <= 1:
        return list_memtypes

    if T_List in list_memtypes:
        # For the purposes of type-union,
        # T_List is basically "List of TBD",
        # and because len(list_memtypes) >= 2,
        # there must be a more specfic list-type in the set,
        # so ignore T_List.
        list_memtypes.remove(T_List)

    if len(list_memtypes) == 1:
        return list_memtypes

    t = ListType(
        union_of_types([
            mt.element_type
            for mt in list_memtypes
        ])
    )

    return [t]

# ------------------------------------------------------------------------------

def union_of_other_memtypes(memtypes):

    if len(memtypes) <= 1:
        return memtypes

    tnodes = []
    for mt in memtypes:
        assert isinstance(mt, Type), mt
        assert not isinstance(mt, UnionType), mt
        assert not isinstance(mt, ListType), mt
        tnodes.append(ensure_tnode_for(mt))

    assert tnodes

    for tnode in tnodes:
        tnode._include_all = True

    result_members = []

    def recurse(tnode):
        # Return True iff all of tnode is included in the union.

        if hasattr(tnode, '_include_all'): return True

        if tnode.children:

            children_included = [
                recurse(child)
                for child in tnode.children
            ]

            if False and trace_this_op:
                print(tnode.type, "children_included = ", children_included)

            if all(children_included):
                tnode._include_all = True
                return True
            else:
                for child in tnode.children:
                    if hasattr(child, '_include_all'):
                        result_members.append(child.type)
                return False

        else:
            return False

    if recurse(troot):
        result_members.append(troot.type)

    for tnode in tnodes:
        anc = tnode
        while anc is not None:
            if hasattr(anc, '_include_all'): del anc._include_all
            anc = anc.parent

    return result_members

# ------------------------------------------------------------------------------

#    global compare_types_f
#    compare_types_f = shared.open_for_output('compare_types')
#
#compare_types_memo = {}
#
#def compare_types(A, B):
#    assert isinstance(A, Type)
#    assert isinstance(B, Type)
#
#    # if A == T_TBD: return (T_TBD, B, T_TBD)
#    # assert B != T_TBD
#
#    if (A,B) in compare_types_memo:
#        return compare_types_memo[(A,B)]
#
#    A_memtypes = A.set_of_types()
#    B_memtypes = B.set_of_types()
#
#    # A few cases that can be handled quickly:
#    if A_memtypes == B_memtypes:
#        A_intersect_B = A # or B
#        A_minus_B     = T_0
#        B_minus_A     = T_0
#
#    elif A_memtypes <= B_memtypes:
#        A_intersect_B = A
#        A_minus_B     = T_0
#        B_minus_A     = maybe_UnionType(B_memtypes - A_memtypes)
#
#    elif B_memtypes <= A_memtypes:
#        A_intersect_B = B
#        A_minus_B     = maybe_UnionType(A_memtypes - B_memtypes)
#        B_minus_A     = T_0
#
#    else:
#        # The general case:
#
#        for (nm, t) in [('A', A_memtypes), ('B', B_memtypes)]:
#            attr_name = 'amount_in_' + nm
#
#            for memtype in t:
#                # Treat T_TBD like Top
#                if memtype == T_TBD: memtype = T_Top_ # assert 0
#                start_tnode = ensure_tnode_for(memtype)
#                start_tnode.__setattr__(attr_name, 'all')
#                tnode = start_tnode.parent
#                while tnode is not None:
#                    if hasattr(tnode, attr_name):
#                        assert tnode.__getattribute__(attr_name) == 'some'
#                        break
#                    tnode.__setattr__(attr_name, 'some')
#                    tnode = tnode.parent
#
#        A_minus_B_memtypes = []
#        A_intersect_B_memtypes = []
#        B_minus_A_memtypes = []
#
#        def recurse(tnode, an_ancestor_is_all_in_A=False, an_ancestor_is_all_in_B=False):
#            assert not (an_ancestor_is_all_in_A and an_ancestor_is_all_in_B)
#
#            if an_ancestor_is_all_in_A:
#                amount_of_this_in_A = 'all'
#            elif hasattr(tnode, 'amount_in_A'):
#                amount_of_this_in_A = tnode.amount_in_A
#                del tnode.amount_in_A
#            else:
#                amount_of_this_in_A = 'none'
#
#            if an_ancestor_is_all_in_B:
#                amount_of_this_in_B = 'all'
#            elif hasattr(tnode, 'amount_in_B'):
#                amount_of_this_in_B = tnode.amount_in_B
#                del tnode.amount_in_B
#            else:
#                amount_of_this_in_B = 'none'
#
#            if amount_of_this_in_A == 'all' and amount_of_this_in_B == 'all':
#                A_intersect_B_memtypes.append(tnode.type)
#
#            elif amount_of_this_in_A == 'all':
#                if amount_of_this_in_B == 'some':
#                    for child in tnode.children:
#                        recurse(child, an_ancestor_is_all_in_A=True)
#                elif amount_of_this_in_B == 'none':
#                    A_minus_B_memtypes.append(tnode.type)
#                else:
#                    assert 0 # can't happen
#
#            elif amount_of_this_in_B == 'all':
#                if amount_of_this_in_A == 'some':
#                    for child in tnode.children:
#                        recurse(child, an_ancestor_is_all_in_B=True)
#                elif amount_of_this_in_A == 'none':
#                    B_minus_A_memtypes.append(tnode.type)
#                else:
#                    assert 0 # can't happen
#
#            elif amount_of_this_in_A == 'some' or amount_of_this_in_B == 'some':
#                for child in tnode.children:
#                    recurse(child)
#
#            elif amount_of_this_in_A == 'none' and amount_of_this_in_B == 'none':
#                # (Neither tnode nor any of its subtypes
#                # is in either A_memtypes or B_memtypes.)
#                pass
#
#            else:
#                assert 0 # can't happen
#
#        recurse(troot)
#
#        A_minus_B     = maybe_UnionType(A_minus_B_memtypes)
#        A_intersect_B = maybe_UnionType(A_intersect_B_memtypes)
#        B_minus_A     = maybe_UnionType(B_minus_A_memtypes)
#
#    assert isinstance(A_minus_B,     Type)
#    assert isinstance(A_intersect_B, Type)
#    assert isinstance(B_minus_A,     Type)
#
#    print("%s :: %s  ===>  %s  ///  %s  ///  %s" %
#        (A, B, A_minus_B, A_intersect_B, B_minus_A),
#        file=compare_types_f)
#
#    result = (A_minus_B, A_intersect_B, B_minus_A)
#    compare_types_memo[(A,B)] = result
#    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Env:
    def __init__(self):
        self.vars = {}

    def __str__(self):
        return str(self.vars)

    def copy(self):
        e = Env()
        e.vars = self.vars.copy()
        return e

    def equals(self, other):
        return self.vars == other.vars

    def lookup(self, ex):
        return self.vars[ex.source_text()]

    def diff(self, other):
        # Show the difference between two envs. (For debugging.)
        self_keys = set(self.vars.keys())
        other_keys = set(other.vars.keys())

        cats_ = defaultdict(list)

        for key in self.vars.keys() | other.vars.keys():
            if key in self.vars and key in other.vars:
                if self.vars[key] == other.vars[key]:
                    cat = 'entries in both, with same value'
                    line = "`%s`: `%s`" % (key, self.vars[key])
                else:
                    cat = 'entries in both, with different value'
                    line = "`%s`: `%s`  vs  `%s`" % (key, self.vars[key], other.vars[key])
            elif key in self.vars:
                cat = 'entries only in L'
                line = "`%s`: `%s`" % (key, self.vars[key])
            elif key in other.vars:
                cat = 'entries only in R'
                line = "`%s`: `%s`" % (key, other.vars[key])
            else:
                assert 0
            cats_[cat].append(line)

        def show_cat(cat):
            print(cat)
            if cat in cats_:
                for line in cats_[cat]:
                    print("    " + line)
            else:
                print("    (none)")
            print()

        show_cat('entries in both, with same value')
        show_cat('entries in both, with different value')
        show_cat('entries only in L')
        show_cat('entries only in R')

    # ----------------------------------------------------------------

    def plus_new_entry(self, var, t):
        if isinstance(var, str):
            var_name = var
        elif isinstance(var, ANode):
            [var_name] = var.children
        else:
            assert 0

        # assert var_name not in self.vars, var_name
        # disabled assertion dur to _f_ in Number.prototype.toExponential
        if var_name in self.vars:
            add_pass_error(
                var,
                f"plus_new_entry for `{var_name}` when it's already in the env!"
            )

        assert isinstance(t, Type)
        e = self.copy()
        e.vars[var_name] = t
        return e

    def with_var_removed(self, var):
        [var_name] = var.children
        assert var_name in self.vars
        e = self.copy()
        del e.vars[var_name]
        return e

    def augmented_with_return_type(self, return_type):
        e = self.copy()
        e.vars['*return*'] = return_type
        return e

    # ----------------------------------------------------------------

    def assert_expr_is_of_type(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_t, expr_env) = tc_expr(expr, self); assert expr_env is self

        if expr_t == T_TBD:
            add_pass_error(
                expr,
                "type of `%s` is TBD, asserted to be of type `%s`"
                % (expr.source_text(), expected_t)
            )
        elif expr_t.is_a_subtype_of_or_equal_to(expected_t):
            return expr_t
        elif expected_t == T_not_returned and expr_t in [T_Undefined, T_empty_]:
            # todo: why does EnqueueJob return ~empty~ ?
            return expr_t
        else:
            stderr()
            stderr("assert_expr_is_of_type()")
            stderr("expr      :", expr.source_text())
            stderr("expr_t    :", expr_t)
            stderr("expected_t:", expected_t)
            assert 0
            sys.exit(0)

    # --------

    def ensure_expr_is_of_type(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_type, expr_env) = tc_expr(expr, self)

        if expr_type == T_TBD:
            result_env = expr_env.with_expr_type_replaced(expr, expected_t)

        elif expr_type.is_a_subtype_of_or_equal_to(expected_t):
            # great!
            result_env = expr_env

        else:
            expr_text = expr.source_text()
            add_pass_error(
                expr,
                "%s has type %s, but this context expects that it be of type %s"
                % (expr_text, expr_type, expected_t)
            )
            if expr_text == '*null*':
                # Don't try to change the type of *null*!
                result_env = expr_env
            elif expr_text == '_len_' and expr_type == T_Integer_ and expected_t == T_Tangible_:
                # skip this for now
                result_env = expr_env
            else:
                result_env = expr_env.with_expr_type_replaced(expr, expected_t)
        return result_env

    def ensure_A_can_be_element_of_list_B(self, item_ex, list_ex):
        (list_type, list_env) = tc_expr(list_ex, self)
        (item_type, item_env) = tc_expr(item_ex, list_env)

        if (list_type == T_List or list_type == ListType(T_TBD)) and item_type == T_TBD:
            # shrug
            result = item_env

        # ----------------------------------------
        # cases where we change the ST of list_ex:

        elif list_type == T_List or list_type == ListType(T_TBD) or list_type == T_TBD:
            result = item_env.with_expr_type_replaced( list_ex, ListType(item_type))

        elif list_type == ListType(T_String) and item_type == T_Symbol:
            result = item_env.with_expr_type_replaced( list_ex, ListType(T_String | T_Symbol))

        elif list_type == ListType(T_PromiseReaction_Record) | T_Undefined and item_type == T_PromiseReaction_Record:
            result = item_env.with_expr_type_narrowed(list_ex, ListType(T_PromiseReaction_Record))

        # ----------------------------------------
        # cases where we change the ST of item_ex:

        elif item_type == T_TBD:
            result = item_env.with_expr_type_replaced(item_ex, list_type.element_type)

        elif list_type == ListType(T_String) and item_type == ListType(T_code_unit_):
            # TemplateStrings
            result = item_env.with_expr_type_replaced(item_ex, T_String)

        elif list_type == ListType(T_String) and item_type == T_String | T_Null:
            # ParseModule
            result = item_env.with_expr_type_replaced(item_ex, T_String)

        # ----------------------------------------
        # cases where we don't change either ST:

        elif list_type == ListType(T_String) and item_type == T_String | T_Symbol:
            # [[Delete]] for module namespace exotic object _O_:
            # If _P_ is an element of _exports_
            # (if _P_ is a Symbol, it just won't be an element of _exports_)
            result = item_env

#        elif list_type == T_Normal and item_type == T_0:
#            # ArgumentListEvaluation
#            env1 = item_env.with_expr_type_narrowed(list_ex, ListType(T_Tangible_))
#            element_type = T_Tangible_
#            assert item_type.is_a_subtype_of_or_equal_to(element_type)
#            result = env1

        elif list_type == ListType(T_String) and item_type == ListType(T_code_unit_) | T_code_unit_ | T_Undefined:
            # TemplateStrings
            # The "Undefined" alternative can't actially happen,
            # but STA can't see that.
            result = item_env

        elif list_type.is_a_subtype_of_or_equal_to(T_List):
            # use list_type to check type of item_ex
            element_type = list_type.element_type
            assert item_type.is_a_subtype_of_or_equal_to(element_type)
            result = item_env

        else:
            add_pass_error(
                list_ex,
                f"context wants a List type, but got {list_type}"
            )
            result = item_env

        return result

    def with_expr_type_replaced(self, expr, new_t):
        assert isinstance(new_t, Type)
        #
        expr_text = expr.source_text()
        if expr_text in self.vars:
            old_t = self.vars[expr_text]
            assert new_t != old_t

            if (
                old_t == T_TBD and new_t != T_TBD
                or
                old_t == T_not_passed and new_t != T_not_passed
                or
                old_t == T_Top_ and new_t == T_Null | T_String
                # ExportEntriesForModule
                or
                old_t == T_Top_ and new_t == T_Object
                # AtomicLoad
                or
                old_t == T_Top_ and new_t == T_Tangible_
                # GeneratorResumeAbrupt
                or
                old_t == T_List and isinstance(new_t, ListType)
                or
                old_t == T_Tangible_ and new_t in [T_String, T_Boolean, T_Symbol, T_Object] # SameValueNonNumber
                or
                old_t == T_Tangible_ and new_t == T_Number # SameValue, co-ordinated types
                or
                old_t == ListType(T_String) and new_t == ListType(T_String | T_Symbol) # OrdinaryOwnPropertyKeys, maybe others
                #or
                #old_t == T_0 and new_t == T_ResolvedBinding_Record
                ## ResolveExport
                or
                old_t == T_Data_Block | T_Shared_Data_Block and new_t == T_Shared_Data_Block and expr_text == '_toBlock_' # CopyDataBlockBytes, because I can't handle co-ordinated types
                or
                old_t == T_Data_Block | T_Shared_Data_Block | T_Null and (
                    new_t == T_Shared_Data_Block
                        # GetModifySetValueInBuffer, because I can't represent the effect of IsSharedArrayBuffer
                    or
                    new_t == T_Data_Block
                        # SetValueInBuffer, ditto
                )
                or
                old_t == T_Number and new_t == T_Integer_
                    # e.g. ReadModifyWriteSharedMemory{ ... [[ElementSize]]: _elementSize_. ...}
                    # in GetModifySetValueInBuffer
                or
                old_t == ListType(T_PTN_ForBinding) and old_t.is_a_subtype_of_or_equal_to(new_t) # VarScopedDeclarations
                or
                old_t == T_Boolean | T_not_set and new_t == T_Boolean
                # ContainsDuplicateLabels, because of re-use of _hasDuplicates_
                or
                old_t == ListType(ListType(T_code_unit_) | T_String) and new_t == ListType(T_String)
                # TemplateStrings
                or
                old_t == T_Tangible_ | T_not_set and new_t == T_Tangible_
                # CaseBlockEvaluation, will go away with refactoring
                or
                old_t == T_empty_ and new_t == ptn_type_for('MethodDefinition')
                # ClassDefinitionEvaluation
                or
                old_t == T_Normal and new_t == T_methodDef_record_
                # ClassDefinitionEvaluation
                or
                old_t == T_Property_Descriptor | T_Undefined and new_t == T_Property_Descriptor
                # CreateGlobalFunctionBinding
                or
                old_t == ptn_type_for('AssignmentPattern') | T_not_set and new_t == T_Parse_Node
                # ForIn/OfBodyEvaluation
                or
                old_t == T_Boolean | T_Environment_Record | T_Number | T_Object | T_String | T_Symbol | T_Undefined and new_t == T_Object
                # GetValue. (Fix by replacing T_Reference with ReferenceType(base_type)?)
                or
                old_t == T_Abrupt | T_Boolean | T_Intangible_ | T_Null | T_Number | T_Object | T_String | T_Symbol and new_t == T_Environment_Record
                # InitializeBoundName
                or
                old_t == T_Normal and new_t == T_Tangible_
                # PropertyDefinitionEvaluation
                or
                old_t == ListType(T_TBD) and new_t == ListType(T_Tangible_)
                # ArgumentListEvaluation
                or
                old_t | T_Abrupt == new_t
                or
                old_t | T_throw_ == new_t
                or
                old_t == T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation for TemplateLiteral
                or
                expr_text in ['_test_', '_increment_'] and new_t == T_Parse_Node
                or
                old_t == T_Environment_Record | T_Undefined and new_t == T_Environment_Record
                # IteratorBindingInitialization
                or
                old_t == T_String | T_Symbol | T_Undefined and new_t == T_String | T_Symbol
                # ValidateAndApplyPropertyDescriptor
                or
                old_t == ListType(T_code_unit_) and new_t == T_String
                # TemplateStrings
                or
                old_t == T_Tangible_ and new_t == T_function_object_
                # [[Construct]]
                or
                old_t == T_Null | T_Object and new_t == T_Object
                # [[Construct]]
                or
                old_t == T_Tangible_ | T_empty_ and new_t == T_Tangible_
                # ??
                or
                old_t == T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                or old_t == ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of TemplateLiteral : TemplateHead Expression TemplateSpans
                or
                old_t == ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation of TemplateMiddleList : TemplateMiddleList TemplateMiddle Expression
                or
                old_t == T_Tangible_ | T_empty_ and new_t == T_String | T_Symbol
                # DefineMethod
                or
                old_t == ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ and new_t == T_String | T_Symbol
                # DefineMethod
                or
                old_t == T_Integer_ | T_Tangible_ | T_code_unit_ and new_t == T_Integer_ | T_Number | T_code_unit_
                # [[DefineOwnProperty]]
                or
                old_t == T_Tangible_ | T_code_unit_ and new_t == T_Number | T_code_unit_
                or
                old_t == T_String | T_Undefined and new_t == T_String
                # GeneratorResume
                or
                old_t == T_CharSet | ThrowType(T_SyntaxError) and new_t == T_CharSet
                or
                old_t == ListType(T_Tangible_) and new_t == ListType(T_String)
                # InternalizeJSONProperty
                or
                old_t == T_Abrupt | T_Boolean | T_Intangible_ | T_Null | T_Number | T_Object | T_String | T_Symbol and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # SerializeJSONObject
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_)
                # TemplateStrings
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of SubstitutionTemplate
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation of TemplateMiddleList
                or
                old_t == T_Abrupt | T_Tangible_ | T_empty_ and new_t == T_Abrupt | T_Tangible_
                # AsyncGeneratorResumeNext
                or
                old_t == T_Undefined and new_t == T_Object #???
                # Evaluation (YieldExpression)

            ):
                pass
            else:
                stderr()
                stderr("with_expr_type_replaced")
                stderr("expr :", expr_text)
                stderr("old_t:", old_t)
                stderr("new_t:", new_t)
                # assert 0
                # sys.exit(0)
        else:
            assert expr_text in [
                '! CodePointToUTF16CodeUnits(_cp_)',
                '? CaseClauseIsSelected(_C_, _input_)', # Evaluation (CaseBlock)
                '? Get(_obj_, `"length"`)',
                '? GetValue(_defaultValue_)', # DestructuringAssignmentEvaluation, bleah
                '? InnerModuleEvaluation(_requiredModule_, _stack_, _index_)', # InnerModuleEvaluation
                '? InnerModuleLinking(_requiredModule_, _stack_, _index_)', # InnerModuleLinking
                '? IteratorValue(_innerResult_)', # Evaluation of YieldExpression
                '? IteratorValue(_innerReturnResult_)', # Evaluation of YieldExpression
                '? ToPrimitive(_x_)', # Abstract Equality Comparison
                '? ToPrimitive(_y_)', # Abstract Equality Comparison
                '? ToPropertyKey(_lval_)',
                'Call(_return_, _iterator_)', # AsyncIteratorClose
                'CodePointToUTF16CodeUnits(_V_)',
                'StringValue of |Identifier|',
                'ToInteger(_P_)', # [[OwnPropertyKeys]]
                'ToNumber(_x_)', # Abstract Equality Comparison
                'ToNumber(_y_)', # Abstract Equality Comparison
                'ToPrimitive(_x_)',
                'ToPrimitive(_y_)',
                'ToPropertyKey(_lval_)',
                '_cookedStrings_[_index_]', # because of TemplateStrings return type
                '_e_.[[LocalName]]', # ResolveExport
                '_ee_.[[LocalName]]',
                '_module_.[[DFSAncestorIndex]]', # InnerModuleEvaluation
                '_module_.[[DFSIndex]]', # InnerModuleEvaluation
                '_rawStrings_[_index_]', # ResolveExport
                '_requiredModule_.[[DFSAncestorIndex]]', # InnerModuleEvaluation
                '_scriptRecord_.[[Realm]]',
                '_throwawayCapability_.[[Promise]]', # AsyncFunctionAwait
                'the MV of |DecimalDigits|',
                'the MV of the first |DecimalDigits|',
                'the MV of |StrUnsignedDecimalLiteral|',
                'the TV of |TemplateCharacter|',
                'the TV of |TemplateCharacters|',
                'the TV of |NoSubstitutionTemplate|',
                'the VarDeclaredNames of |Statement|',
                'the VarScopedDeclarations of |Statement|',
                'the result of evaluating _body_', # PerformEval
                'the result of evaluating |Assertion|',
                'the result of evaluating |AtomEscape|',
                'the result of evaluating |AtomEscape| with argument _direction_',
                'the result of evaluating |Atom|',
                'the result of evaluating |Atom| with argument _direction_',
                'the result of evaluating |CharacterClassEscape|',
                'the result of evaluating |CharacterEscape|',
                'the result of evaluating |ClassAtom|',
                'the result of evaluating |ClassAtomNoDash|',
                'the result of evaluating |ClassEscape|',
                'the result of evaluating |Disjunction|',
                'the result of evaluating |Disjunction| with argument _direction_',
                'the result of evaluating |LeadSurrogate|',
                'the result of evaluating |NonSurrogate|',
                'the result of evaluating |NonemptyClassRanges|',
                'the result of evaluating |TrailSurrogate|',
                'the result of performing ArrayAccumulation for |ElementList| with arguments _array_ and _nextIndex_',
                'the result of performing ArrayAccumulation for |Elision| with arguments _array_ and _nextIndex_',
                'the result of performing IteratorDestructuringAssignmentEvaluation of |AssignmentRestElement| with _iteratorRecord_ as the argument',
                'the result of performing IteratorDestructuringAssignmentEvaluation of |Elision| with _iteratorRecord_ as the argument', # hm
                '(16 times the MV of the first |HexDigit|) plus the MV of the second |HexDigit|',
                '(0x1000 times the MV of the first |HexDigit|) plus (0x100 times the MV of the second |HexDigit|) plus (0x10 times the MV of the third |HexDigit|) plus the MV of the fourth |HexDigit|',
                '_f_ + 1', # Number.prototype.toExponential
                '_f_ + 1 - _k_', # Number.prototype.toFixed
                '_k_ - _f_', # toFixed
                '_p_ - 1', # toPrecision
                '_p_ - (_e_ + 1)', # toPrecision
                '_srcBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                '_targetBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                'the result of performing NamedEvaluation for |Initializer| with argument _bindingId_',
                '_handler_', # NewPromiseReactionJob
                '_r_.[[Value]]',
            ], expr_text.encode('unicode_escape')
        #
        e = self.copy()
        e.vars[expr_text] = new_t
        return e

    def set_A_to_B(self, settable, expr):
        (settable_type, env1) = tc_expr(settable, self)
        (expr_type,     env2) = tc_expr(expr,     env1)

        if settable_type == T_TBD and expr_type == T_TBD:
            assert 0

        elif settable_type == T_TBD:
            # flow type info from expr to settable
            return self.with_expr_type_replaced(settable, expr_type)

        elif expr_type == T_TBD:
            # flow type info from settable to expr
            # this is questionable
            return self.with_expr_type_replaced(expr, settable_type)

        elif expr_type == settable_type:
            return env2

        elif expr_type == T_List and isinstance(settable_type, ListType):
            # E.g., expr is an empty List constructor
            # XXX Still need this?
            return env2

        else:
            # ??:
            # settable_type is mostly irrelevant,
            # unless we distinguish the type that a settable is *allowed* to have,
            # versus the type that it happens to have right now.
            #
            # parameters:
            #     - _iSL_ (optional) List of SlotName_
            #   1.If _iSL_ was not provided, set _iSL_ to a new empty List
            # Setting _iSL_ does change the type that it has after that command,
            # but it shouldn't change the declared type of the parameter.
            # But we use exit envs to infer changes to the parameter types.
            # (which makes sense when their declared type is TBD, or maybe just 'List',
            # but not so much otherwise.

            # XXX If the settable is a DOTTING, we should disallow
            # an expr_t that is outside the allowed type of the dotting

            settable_text = settable.source_text()
            if expr_type.is_a_subtype_of_or_equal_to(settable_type):
                # A change, but probably not worth mentioning
                pass
            elif settable_type == T_not_passed:
                # "If _foo_ was not passed, set _foo_ to X."
                # Not worth warning about type-change.
                pass
            else:
                add_pass_error(
                    settable,
                    "warning: Set `%s` changes type from `%s` to `%s`" %
                    (settable_text, settable_type, expr_type)
                )
            e = env2.copy()
            e.vars[settable_text] = expr_type
            return e

    # ----------------------------------------------------------------

    def with_expr_type_narrowed(self, expr, narrower_t):
        assert isinstance(narrower_t, Type)
        (expr_t, env1) = tc_expr(expr, self)

        if expr_t.is_a_subtype_of_or_equal_to(narrower_t):
            # expr is already narrower than required.
            return env1

        # Treat T_TBD like Top:
        if expr_t == T_TBD:
            pass
        elif narrower_t.is_a_subtype_of_or_equal_to(expr_t):
            pass
        elif expr_t == T_Number and narrower_t == T_Integer_:
            # `DateFromTime(_t_) is 1`
            pass
        else:
            stderr("expr %r of type %s cannot be narrowed to %s" % (expr.source_text(), expr_t, narrower_t))
            assert 0
        #
        expr_text = expr.source_text()
        e = env1.copy()
        e.vars[expr_text] = narrower_t
        return e

    # ----------------------------------------------------------------

    def with_type_test(self, expr, copula, target_t, asserting):
        # Returns a pair of Envs:
        # one in which the the type-test is true, and one in which it's false.
        # i.e.,
        # - one in which the expr's current type is narrowed to be <: target_t; and
        # - one in which its type is narrowed to have no intersection with target_t
        # (either respectively or anti-respectively, depending on copula.)

        expr_text = expr.source_text()

        (expr_t, env1) = tc_expr(expr, self)

        # assert env1 is self
        # No, e.g. expr_text is '_R_.[[Value]]', where the out-env
        # has a narrower binding for _R_.

        assert target_t != T_TBD

        if asserting and expr_t == T_TBD:
            if copula == 'is a':
                true_env = env1.copy()
                true_env.vars[expr_text] = target_t
                false_env = None
                return (true_env, false_env)
            else:
                # XXX wah
                return (env1, env1)

            # pdb.set_trace()

        (part_inside_target_t, part_outside_target_t) = expr_t.split_by(target_t)

        assert isinstance(part_outside_target_t, Type)
        assert isinstance(part_inside_target_t, Type)

        if asserting:
            if copula == 'is a':
                # We are asserting that the value of `expr` is of the target type.
                # So it'd be nice if the static type of `expr` were a subtype of the target type.
                if part_inside_target_t == T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't be a `%s`"
                        % (expr_text, expr_t, target_t)
                    )

                if part_outside_target_t != T_0:
                    add_pass_error(
                        expr,
                        "STA fails to confirm that %s is a %s; could also be %s" %
                        (expr_text, target_t, part_outside_target_t)
                    )
                    # e.g. a parameter type starts as TBD.
                    # but because the Assert will only propagate the 'true' env,
                    # this error will probably disappear in a later pass.


            elif copula == 'isnt a':
                # We expect that the static type of the expr has no intersection with the target type.

                if part_inside_target_t != T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't confirm the assertion -- value might be `%s`"
                        % (expr_text, expr_t, part_inside_target_t)
                    )
                assert part_outside_target_t != T_0
            else:
                assert 0, copula
        else:
            # Outside of an assertion,
            # you're presumably doing the type-test
            # with the expectation that either outcome is possible.
            if part_outside_target_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so must be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it must be" % (
                        expr_text, target_t)
                )
                # ResolveExport _starResolution_ loop thing

            if part_inside_target_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so can't be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it can't be" % (
                        expr_text, target_t)
                )
                # Perhaps a parameter-type was too restrictive.

        intersect_env = env1.copy()
        nointersect_env = env1.copy()
        intersect_env.vars[expr_text] = part_inside_target_t
        nointersect_env.vars[expr_text] = part_outside_target_t
        # if expr_text == '_Input_' and part_inside_target_t == T_List: assert 0
        # if expr_text == '_Input_' and part_outside_target_t == T_List: assert 0

        if copula == 'is a':
            return (intersect_env, nointersect_env)
        else:
            return (nointersect_env, intersect_env)

    def reduce(self, header_names):
        e = Env()
        for (vn, vt) in self.vars.items():
            if vn in header_names:
                e.vars[vn] = vt
        return e

# ------------------------------------------------------------------------------

def env_and(env1, env2):
    # Return an Env that expresses that both env1 and env2 hold.
    return envs_and([env1, env2])

def envs_and(envs):
    if len(envs) == 0: assert 0
    if len(envs) == 1: return envs[0]

    # optimization:
    if len(envs) == 2 and envs[0].vars == envs[1].vars: return envs[0]

    e = Env()
    vars = set.intersection(*[ set(env.vars.keys()) for env in envs ])
    for expr_text in vars:
        ts = [ env.vars[expr_text] for env in envs ]
        ts = [ t for t in ts if t != T_TBD ]
        if ts == []:
            intersection_t = T_TBD
        else:
            intersection_t = ts[0]
            for t in ts[1:]:
                (intersection_t, _) = intersection_t.split_by(t)
        e.vars[expr_text] = intersection_t
    return e

def env_or(env1, env2):
    # Return an Env that expresses that either env1 or env2 (or both) hold.
    return envs_or([env1, env2])

def envs_or(envs):
    envs = [env for env in envs if env is not None]
    if len(envs) == 0: return None
    if len(envs) == 1: return envs[0]

    e = Env()

    all_vars = set()
    for env in envs:
        for var_name in env.vars.keys():
            all_vars.add(var_name)

    for var_name in sorted(all_vars):
        e.vars[var_name] = union_of_types([
            env.vars[var_name] if var_name in env.vars else T_not_set
            for env in envs
        ])

    return e

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_static_type_analysis(levels):

    # atexit.register(write_modified_spec)
    # This was useful when I was gradually building up the set of STA rules,
    # because even if the STA-run ended in an exception (which was usual),
    # I would still get a spec_w_errors written, which might show a little more progress.
    # Now, if STA ends in an exception, spec_w_errors would probably be of no use.

    global split_types_f
    split_types_f = shared.open_for_output('split_types')

    global sta_misc_f
    sta_misc_f = shared.open_for_output('sta_misc')

    global g_level_prefix
    for (L, clusters_on_level_L) in enumerate(levels):
        print()
        print("X" * 60)
        print("X" * 60)
        print("level", L)
        time.sleep(1)
        g_level_prefix = '[%d] ' % L
        n_clusters_this_level = len(clusters_on_level_L)
        for (c, cluster) in enumerate(clusters_on_level_L):
            print()
            print("X" * 50)
            print("level %d, cluster %d/%d (%d ops):" %
                (L, c, n_clusters_this_level, len(cluster.members))
            )
            print()

            pass_num = 0
            while True:
                pass_num += 1
                print()
                print("=" * 40)
                print("level %d : cluster %d/%d : pass #%d..."
                    % (L, c, n_clusters_this_level, pass_num))
                if pass_num == 5:
                    print("giving up")
                    sys.exit(1)
                global pass_errors
                pass_errors = []
                n_ops_changed = 0
                for op_name in cluster.members:
                    changed = tc_operation(op_name)
                    if changed: n_ops_changed += 1
                print("%d operations changed" % n_ops_changed)
                if n_ops_changed > 0:
                    # The cluster's static types haven't settled yet.
                    if pass_errors:
                        print("discarding %d errors" % len(pass_errors))
                else:
                    # The cluster's static types have hit a fixed point.
                    print("achieved fixed point after %d passes" % pass_num)
                    if pass_errors:
                        print("accepting %d errors" % len(pass_errors))
                        for (anode, msg) in pass_errors:
                            install_error(anode, msg)
                    break

        # if L == 1: break

    print()
    print("Finished static analysis!")
    print()

    write_modified_spec(mode = 'messages in algs and dls')
    write_modified_spec(mode = 'dls w revised info')

    # Type-check loops better.

    # Drop the warning for when 'Set' changes the type?

    # For operations with multiple defns (SDOs and CMs),
    # need to remember the return type of each individual defn,
    # then use knowledge of the type of the 'thing'
    # to get the set of defns that might be invoked,
    # and thus a narrower result type than currently.

    # So need to know the grammar.
    # (a) to find that set of defns (note chain rules), and
    # (b) to check {PROD_REF}s like "the second |Expression|".

    # Get rid of Normal?
    # Get rid of Intangible?
    # Introduce Present/Absent dichotomy?
    # Introduce more subtypes?

    # Algorithms for built-ins?

    # Distinguish the declared type (or maximum type) of a variable
    # versus its current type.

# ------------------------------------------------------------------------------

g_level_prefix = '[-] '
pass_errors = []

def add_pass_error(anode, msg):
    global pass_errors
    assert isinstance(anode, ANode)
    print("??:", msg.encode('unicode_escape'))
    pass_errors.append((anode, g_level_prefix + msg))

def install_error(anode, msg):
    if not hasattr(anode, 'parent'):
        # It's a fake node.
        # Just attach the msg to the node.
        if not hasattr(anode, 'errors'):
            anode.errors = []
        anode.errors.append(msg)
    else:
        # It's a real node.
        #
        # We *could* just attach the msg to the node,
        # but then at each line, we'd need to get all the nodes
        # that pertain to that line (i.e., end on it),
        # and that'd be a pain?

        (sl, sc) = shared.convert_posn_to_linecol(anode.start_posn)
        (el, ec) = shared.convert_posn_to_linecol(anode.end_posn)
        if sl == el:
            thing = (sc, ec, msg)
        else:
            stderr("Node spans multiple lines: (%d,%d) to (%d,%d)" % (sl,sc,el,ec))
            thing = (0, ec, msg)
        spec.info_for_line_[el].msgs.append(thing)

# ------------------------------------------------------------------------------

def write_modified_spec(mode = 'messages in algs and dls'):
    assert mode in ['dls w initial info', 'messages in algs and dls', 'dls w revised info']

    if mode == 'dls w initial info':
        filename = 'spec_w_eoh'
    elif mode == 'messages in algs and dls':
        filename = 'spec_w_errors'
    else:
        filename = 'spec_w_edits'
    stderr(f"printing {filename} ...")

    f = shared.open_for_output(filename)

    for line_info in spec.info_for_line_[1:]:

        if not line_info.suppress:
            print(spec.text[line_info.start_posn:line_info.end_posn], file=f)

        if line_info.afters:
            indentation = line_info.indentation
            if indentation == 0:
                # somewhat kludgey
                indentation = spec.info_for_line_[line_info.line_num-1].indentation

            for after_thing in line_info.afters:
                for line in after_thing.lines(indentation, mode):
                    print(line, file=f)

        if mode == 'messages in algs and dls':
            # For each anode that ends on this line,
            # show any messages relating to that anode.

            # For things on the same line, secondary sort by *end*-column.
            for (sc,ec,msg) in sorted(line_info.msgs, key=lambda t: t[1]):
                caret_line = '-' * (sc-1) + '^' * (ec-sc)
                print(caret_line, file=f)
                print('>>> ' + msg, file=f)
                print(file=f)

    f.close()

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

def mytrace(env):
    if env is None:
        print("resulting env is None")
    else:
        # print("resulting env:", env)
        for var_name in ['_argumentList_']:
            print("---> %s : %s" % (var_name, env.vars.get(var_name, "(not set)")))
            # assert 'LhsKind' not in str(env.vars.get(var_name, "(not set)"))

def tc_operation(op_name):
    print()
    print('-' * 30)
    print(op_name)

    # if op_name == '[[Call]]': pdb.set_trace()

    if op_name in built_in_ops:
        print('skipping built-in')
        return False # no change

    if op_name not in operation_named_:
        print("skipping for some other reason?")
        return False

    global trace_this_op
    trace_this_op = False
    trace_this_op = (op_name in [
        'xTypedArrayCreate'
    ])
    # and you may want to tweak mytrace just above

    op = operation_named_[op_name]

    any_change = False
    for header in op.headers:
        c = tc_header(header)
        if c: any_change = True
    
    if any_change:
        op.summarize_headers()

    if trace_this_op:
        pass
        # need to do this if tracing doesn't cause pause
        pdb.set_trace()
        # stderr("ABORTING BECAUSE trace_this_op IS SET.")
        # sys.exit(1)

    return any_change

# --------------------------------

def tc_header(header):

    init_env = header.make_env()

    if header.t_defns == []:
        return False

    final_env = tc_proc(header.name, header.t_defns, init_env)

    assert final_env is not None

    for (pn, final_t) in final_env.vars.items():
        if final_t == T_TBD:
            add_pass_error(
                header.fake_node_for_[pn],
                "after STA, the type of `%s` is still TBD" % pn
            )

    if init_env.vars == final_env.vars:
        # no change
        return False
    else:
        # Something is different between init_env and final_env,
        # but that doesn't necessarily mean that we're going to change header types
        changed_op_info = False
        for pn in sorted(init_env.vars.keys()):
            init_t = init_env.vars[pn]
            final_t = final_env.vars[pn]

            # if final_t == T_Top_: final_t = T_TBD

            # if init_t == T_TBD and final_t == T_TBD:
            #     add_pass_error(
            #         header.fake_node_for_[pn],
            #         'param %r is still TBD' % (pn,)
            #     )

            # if isinstance(final_t, UnionType) and len(final_t.member_types) >= 12:
            #     print("%s : %s : # member_types = %d" % (header.name, pn, len(final_t.member_types)))

            if init_t == final_t: continue

            # if header.name == 'RequireInternalSlot': pdb.set_trace()
            if (
                # cases in which we don't want to change header types:
                init_t == ListType(T_code_unit_) and final_t == T_code_unit_ | ListType(T_code_unit_)
                or
                final_t not in [T_TBD, T_0] and init_t == final_t | T_not_passed
                # ObjectCreate's _internalSlotsList_
                # Call's _argumentsList_
                or
                init_t == T_String | T_Symbol and final_t == T_String
                # SetFunctionName
                or
                init_t == T_Abrupt | T_Tangible_ | T_empty_ and final_t == ListType(T_code_unit_) | T_Top_
                # Evaluation
                or
                header.name == 'GetMethod'
                or
                header.name == 'SetRealmGlobalObject' and pn == '_thisValue_' and init_t == T_Tangible_
                or
                header.name == 'SetRealmGlobalObject' and pn == '_globalObj_' and init_t == T_Object | T_Undefined
                or
                header.name == 'CodePointToUTF16CodeUnits' and pn == '*return*' and init_t == ListType(T_code_unit_)
                or
                header.name == 'PerformPromiseThen' and pn in ['_onFulfilled_', '_onRejected_'] and init_t == T_Tangible_
                or
                header.name == 'TemplateStrings' and pn == '*return*' and init_t == ListType(T_String)
                or
                header.name == 'Construct' and pn == '_newTarget_' and init_t == T_Tangible_ | T_not_passed
                or
                header.name == 'OrdinaryHasInstance' and pn == '_O_'
                or
                header.name == 'GetIterator' and pn == '_method_'
                or
                header.name == 'ResolveBinding' and pn == '_env_'
                or
                header.name == 'ToLength' and pn == '*return*' and init_t == T_Integer_ | ThrowType(T_TypeError)
                # STA isn't smart enough to detect that the normal return is always integer,
                # wants to change it to Number
                or
                header.name == 'PerformPromiseThen' and pn == '_resultCapability_'
                # STA wants to add T_Undefined, which is in the body type, but not the param type
                or
                header.name == 'FlattenIntoArray' and pn == '*return*' and init_t == T_Integer_ | T_throw_ and final_t == T_throw_
                # not sure why STA isn't picking up Integer
                or
                # PR 1668
                header.name == 'SetFunctionName' and pn == '_name_' and init_t == T_Private_Name | T_String | T_Symbol and final_t == T_String
                or
                # PR 1668?
                (
                    # This is a somewhat hacky way to prevent 'throw_' being widened to 'Abrupt'
                    # in the return type of various evaluation-relevant SDOs.
                    header.name in [
                        'BindingClassDeclarationEvaluation',
                        'ClassDefinitionEvaluation',
                        'ClassElementEvaluation',
                        'ClassFieldDefinitionEvaluation',
                        'DefineMethod',
                        'NamedEvaluation',
                        'PropertyDefinitionEvaluation',
                    ]
                    and
                    pn == '*return*'
                    and
                    T_throw_.is_a_subtype_of_or_equal_to(init_t)
                    and
                    not T_continue_.is_a_subtype_of_or_equal_to(init_t)
                    and
                    T_continue_.is_a_subtype_of_or_equal_to(final_t)
                )
                or
                header.name == 'MakeConstructor' and pn == '_F_' and init_t == T_function_object_ 
                or
                header.name == 'String.prototype.localeCompare' and pn == '*return*'
                # The algo is incomplete, so doesn't result in a reasonable return type.
                or
                header.name == '[[Call]]' and pn == '*return*'
                or
                header.name == '[[Construct]]' and pn == '*return*'
                or
                header.name == 'StringToCodePoints' and pn == '*return*'
                or
                header.name == 'CodePointToUTF16CodeUnits' and pn == '_cp_'
            ):
                # -------------------------
                # Don't change header types
                continue

            elif (
                # cases in which we *do* want to change header types:
                # ----
                init_t == T_TBD
                or
                init_t == T_TBD | T_not_passed
                or
                init_t == ListType(T_TBD)
                or
                init_t == T_List and isinstance(final_t, ListType)
                # ----
                or
                init_t.is_a_subtype_of_or_equal_to(final_t)
                # This pass just widened the type.
                # ------
                or
                final_t.is_a_subtype_of_or_equal_to(init_t) and (
                    header.name == 'InstantiateFunctionObject'
                    or
                    header.name == 'GetThisBinding' and init_t == T_Tangible_ | ThrowType(T_ReferenceError)
                    or
                    header.name == 'WithBaseObject' and init_t == T_Object | T_Undefined
                    or
                    header.name == 'SameValueNonNumeric' and init_t == T_Tangible_
                    or
                    header.name == 'SetMutableBinding' and pn == '*return*'
                    or
                    header.name.endswith('DeclarationInstantiation') and pn == '_env_' and init_t == T_Environment_Record
                )
                # This pass just narrowed the type.
                # ----
                or
                init_t == T_Tangible_ and header.name == 'SameValueNonNumber'
                or
                init_t == T_Tangible_ and final_t == T_Object | T_Undefined and header.name == 'PrepareForOrdinaryCall'
                # eoh is just wrong
                or
                init_t == T_Tangible_ and final_t == T_Null | T_Object and header.name == 'OrdinarySetPrototypeOf'
                # eoh is just wrong
                or
                init_t == T_Normal and final_t == T_function_object_
                or
                header.name == 'BindingClassDeclarationEvaluation' and pn == '*return*' and init_t == T_Object and final_t == T_function_object_ | T_throw_
                or
                header.name == 'MakeConstructor' and init_t == T_function_object_ and final_t == T_constructor_object_
                or
                header.name == 'SetFunctionLength' and pn == '_length_' and init_t == T_Number and final_t == T_Integer_
                or
                header.name == 'RequireInternalSlot' and pn == '*return*' and init_t == T_throw_ and final_t == T_not_returned | ThrowType(T_TypeError)
                or
                header.name in ['Math.clz32', 'Math.imul'] and pn == '*return*' and init_t == T_Number and final_t == T_Integer_ | ThrowType(T_TypeError)
                or
                header.name == 'NewPromiseReactionJob' and pn == '*return*' and init_t == T_Job and final_t == T_Record
                or
                header.name == 'CodePointsToString' and pn == '_text_' and init_t == T_Unicode_code_points_ and final_t == ListType(T_code_point_)

                # eoh is just wrong, because preamble is misleading

                # or
                # header.name == 'CreatePerIterationEnvironment' and init_t == T_Undefined | T_throw_ and final_t == T_Undefined | ThrowType(T_ReferenceError)
                # # cheater artifact
                # or
                # header.name == 'InitializeReferencedBinding' and init_t == T_Boolean | T_empty_ | T_throw_ and final_t == T_empty_ | T_throw_
                # # cheater artifact
                # or
                # header.name == 'PutValue' and init_t == T_Boolean | T_Undefined | T_empty_ | T_throw_ and final_t == T_Boolean | T_Undefined | T_throw_
                # # cheater artifact
                # or
                # header.name == 'InitializeBoundName' and init_t == T_Boolean | T_Undefined | T_empty_ | T_throw_ and final_t == T_Boolean | T_Undefined | T_throw_
            ):
                # fall through to change the header types
                pass
            else:
                assert 0, (header.name, pn, str(init_t), str(final_t))
                # We should deal with this case above.

            header.change_declared_type(pn, final_t)

            changed_op_info = True

        return changed_op_info

# ------------------------------------------------------------------------------

proc_return_envs_stack = []

def tc_proc(op_name, defns, init_env):
    assert defns

    header_names = sorted(init_env.vars.keys())

    # XXX This is a hack until I can do a better job of analyzing numeric exprs.
    if op_name and '::' in op_name:
        stderr("    hack!")
        assert len(defns) == 1
        [(base_type, body)] = defns

        final_env = Env()
        for name in header_names:
            if name == '*return*':
                if op_name in [
                    '::equal',
                    '::sameValue',
                    '::sameValueZero',
                ]:
                    t = T_Boolean
                elif op_name == '::lessThan':
                    t = T_Boolean | T_Undefined
                elif op_name == '::toString':
                    t = T_String
                else:
                    t = base_type
                if op_name in [
                    '::exponentiate',
                    '::divide',
                    '::remainder',
                ]:
                    t |= ThrowType(T_RangeError)
                elif op_name == '::unsignedRightShift':
                    t |= ThrowType(T_TypeError) 
            else:
                t = base_type
            final_env.vars[name] = t
        return final_env

    proc_return_envs_stack.append(set())

    for (i, (discriminator, body)) in enumerate(defns):
        if op_name is not None:
            print()
            print('-' * 20)
            print("%s : defn #%d/%d:" % (op_name, i+1, len(defns)))

        # global trace_this_op
        # trace_this_op = (op_name == 'SV' and i == 27)

        if discriminator:
            if isinstance(discriminator, Type):
                print(discriminator)
            elif hasattr(discriminator, 'source_text'):
                print(discriminator.source_text())
            else:
                assert 0
        else:
            print('(no discriminator)')
        print()

        if body.prod.lhs_s in ['{EMU_ALG_BODY}', '{IAO_BODY}', '{IND_COMMANDS}']:
            # kludge:
            if (
                isinstance(discriminator, HTML.HNode)
                and
                discriminator.source_text() == '<emu-grammar>A : A @ B</emu-grammar>'
            ):
                init_env1 = init_env.plus_new_entry('_A_', T_Parse_Node).plus_new_entry('_B_', T_Parse_Node)
            else:
                init_env1 = init_env
            assert tc_nonvalue(body, init_env1) is None
        elif body.prod.lhs_s in ['{EXPR}', '{NAMED_OPERATION_INVOCATION}']:
            (out_t, out_env) = tc_expr(body, init_env)
            proc_add_return(out_env, out_t, body)
        else:
            assert 0, body.prod.lhs_s

        # if trace_this_op: pdb.set_trace()

    proc_return_envs = proc_return_envs_stack.pop()

    rr_envs = []
    for return_env in proc_return_envs:
        rr_envs.append(return_env.reduce(header_names))
    final_env = envs_or(rr_envs)

    assert final_env is not None

    if T_Top_.is_a_subtype_of_or_equal_to(final_env.vars['*return*']):
        print()
        for e in rr_envs:
            print(e.vars['*return*'])
        assert 0, final_env.vars['*return*']

    return final_env

def proc_add_return(env_at_return_point, type_of_returned_value, node):
    if trace_this_op:
        print("Type of returned value:", type_of_returned_value)
        if T_Abrupt.is_a_subtype_of_or_equal_to(type_of_returned_value):
            input('hit return to continue ')

    # (or intersect Absent with type_of_returned_value)
#    rt_memtypes = type_of_returned_value.set_of_types()
#    for t in [T_not_set, T_not_passed, T_not_there]:
#        # if t.is_a_subtype_of_or_equal_to(type_of_returned_value):
#        if t in rt_memtypes:
#            add_pass_error(
#                ????,
#                "warning: static type of return value includes `%s`" % str(t)
#            )
    # or, eventually, check that the return value conforms to the proc's declared return

    if type_of_returned_value in [T_Top_, T_Normal]: # , T_TBD]:
        assert 0, str(type_of_returned_value)

    aug_env = env_at_return_point.augmented_with_return_type(type_of_returned_value)

    if 1:
        for (pn, ptype) in sorted(aug_env.vars.items()):
            # if isinstance(ptype, UnionType) and len(ptype.member_types) >= 14:
            #     print("`%s` : # member_types = %d" % (pn, len(ptype.member_types)))
            #     if len(ptype.member_types) == 41: assert 0

            if pn == '*return*' and T_not_returned.is_a_subtype_of_or_equal_to(ptype) and ptype != T_Abrupt | ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ | T_not_returned:
                add_pass_error(
                    node,
                    "At exit, ST of `%s` is `%s`" % (pn, ptype)
                )

    proc_return_envs_stack[-1].add(aug_env)

# ------------------------------------------------------------------------------

def tc_nonvalue(anode, env0):
    # Return the env that this construct delivers to the 'next' thing
    # (i.e. when/if control leaves this construct 'normally')
    # If control never leaves this construct normally
    # (e.g., it's a Return command), return None.

    if trace_this_op:
        trace_line = anode.source_text()
        trace_line = re.sub(r'\n *', r'\\n ', trace_line)
        trace_line = trace_line[0:80]
        print()
        print("Entering nv:", anode.prod.lhs_s, trace_line)
        mytrace(env0)

    assert isinstance(anode, ANode)
    assert env0 is None or isinstance(env0, Env)
    # But if it's None, you're not going to be able to do much!

    # if anode.prod.lhs_s == '{COMMAND}': stderr('>>>', anode.source_text())

    p = str(anode.prod)
    children = anode.children

    if p in [
        r'{IND_COMMANDS} : {_indent_}{COMMANDS}{_outdent_}',
        r'{COMMANDS} : {_NL_N} {COMMAND}',
        r'{COMMAND} : {IF_CLOSED}',
        r'{COMMAND} : {IF_OTHER}',
        r'{ELSE_PART} : Else, {SMALL_COMMAND}.',
        r'{ELSE_PART} : Else,{IND_COMMANDS}',
        r'{ELSE_PART} : Otherwise, {SMALL_COMMAND}.',
        r"{COMMAND} : Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error detection:{IND_COMMANDS}",

        r"{COMMAND} : Optionally, {SMALL_COMMAND}.",
    ]:
        [child] = children
        result = tc_nonvalue(child, env0)

    elif p == r"{ELSE_PART} : Else, {CONDITION_1}. {COMMAND}":
        [cond, comm] = children
        (t_env, f_env) = tc_cond(cond, env0, asserting=True)
        result = tc_nonvalue(comm, t_env)

    elif p == r'{EMU_ALG_BODY} : {IND_COMMANDS}{nlai}':
        [ind_commands] = children
        env1 = tc_nonvalue(ind_commands, env0)
        if env1 is not None:
            # Control falls off the end of the algorithm.
            proc_add_return(env1, T_not_returned, ind_commands)
            # spec says we should assume Undefined (wait, does it?), but I don't feel like it.
            result = None
        else:
            # All control paths end with a 'Return'
            result = None

    elif p == r'{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}':
        [commands, command] = children
        env1 = tc_nonvalue(commands, env0)
        env2 = tc_nonvalue(command, env1)
        result = env2

    # ---------------------------------
    # constructs that create a metavariable

    # Let {var} be ...

    elif p in [
        r"{COMMAND} : Let {var} be {EXPR}. (It may be evaluated repeatedly.)",
        # r"{COMMAND} : Let {var} be {EXPR}. Remove that record from {var}.", # PR 1597
        r"{COMMAND} : Let {var} be {EXPR}. This alias will be used throughout the algorithms in {h_emu_xref}.",
        # r"{COMMAND} : Let {var} be {EXPR}. {note}", # obsoleted by PR 1831
        r"{COMMAND} : Let {var} be {EXPR}.",
        r"{COMMAND} : Let {var} be {MULTILINE_EXPR}",
        r"{SMALL_COMMAND} : let {var} be {EXPR}",
        r"{SMALL_COMMAND} : let {var} be {EXPR}, indicating that an ordinary object should be created as the global object",
        r"{SMALL_COMMAND} : let {var} be {EXPR}, indicating that {var}'s global `this` binding should be the global object",
    ]:
        [var, expr] = children[0:2]
        [var_name] = var.children

        (expr_t, env1) = tc_expr(expr, env0)

        if var_name in env0.vars:
            add_pass_error(
                anode,
                "re-Let on existing var `%s`. Use Set?" % var_name
            )
            var_t = env0.vars[var_name]
            if expr_t == var_t:
                # but at least we're not changing the type
                result = env1
            elif expr_t == T_TBD:
                result = env1
                add_pass_error(
                    anode,
                    "... also, ignoring the attempt to change the type of var to %s" % str(expr_t)
                )
            elif var_name in ['_v_', '_value_'] and var_t in [T_Normal, T_Tangible_ | T_not_set] and expr_t == T_Undefined:
                # IteratorBindingInitialization, IteratorDestructuringAssignmentEvaluation, others?:
                # This isn't a re-Let,
                # because it's never the case that _v_ is already defined at this point,
                # but my STA isn't smart enough to know that.
                add_pass_error(
                    anode,
                    "... actually, it isn't, but STA isn't smart enough"
                )
                result = env1
            elif expr_t.is_a_subtype_of_or_equal_to(var_t):
                add_pass_error(
                    anode,
                    "... also, this narrows the type of var from %s to %s" % (var_t, expr_t)
                )
                result = env1.with_expr_type_narrowed(var, expr_t)
            else:
                add_pass_error(
                    anode,
                    "... also, this changes the type of var from %s to %s" % (var_t, expr_t)
                )
                result = env1.with_expr_type_replaced(var, expr_t)
        else:
            # The normal case.
            result = env1.plus_new_entry(var, expr_t)

    elif p in [
        r"{COMMAND} : Let {var} be {EXPR}. Because {var} and {var} are primitive values evaluation order is not important.",
        r"{COMMAND} : Let {var} be {EXPR}. (This is the same value as {h_emu_xref}'s {var}.)",
    ]:
        [let_var, expr] = children[0:2]
        (t, env1) = tc_expr(expr, env0)
        result = env1.plus_new_entry(let_var, t)

    elif p in [
        r"{COMMAND} : Let {var} be equivalent to a function that throws {var}.",
        r"{COMMAND} : Let {var} be equivalent to a function that returns {var}.",
    ]:
        [let_var, rvar] = children
        env0.assert_expr_is_of_type(rvar, T_Tangible_)
        result = env0.plus_new_entry(let_var, T_function_object_)

    elif p == r"{COMMAND} : Let {var} be {EXPR}. (However, if {var} is 10 and {var} contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit, at the option of the implementation; and if {var} is not 2, 4, 8, 10, 16, or 32, then {var} may be an implementation-approximated value representing the mathematical integer value that is represented by {var} in radix-{var} notation.)":
        [let_var, expr, rvar, zvar, rvar2, let_var2, zvar2, rvar3] = children
        assert same_source_text(let_var, let_var2)
        assert same_source_text(rvar, rvar2)
        assert same_source_text(rvar, rvar3)
        assert same_source_text(zvar, zvar2)
        (t, env1) = tc_expr(expr, env0)
        result = env1.plus_new_entry(let_var, t)

    elif p == r'{COMMAND} : Let {var} be {EXPR}, and let {var} be {EXPR}.':
        [let_var1, expr1, let_var2, expr2] = children
        (t1, env1) = tc_expr(expr1, env0) # ; assert env1 is env0 disable assert due to toFixed
        (t2, env2) = tc_expr(expr2, env1) # ; assert env2 is env0 disable assert due to toExponential
        result = env2.plus_new_entry(let_var1, t1).plus_new_entry(let_var2, t2)

    elif p == r"{COMMAND} : Let {var} be the smallest nonnegative integer such that {CONDITION}.":
        [var, cond] = children
        env_for_cond = env0.plus_new_entry(var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, env_for_cond); assert t_env.equals(env_for_cond); assert f_env.equals(env_for_cond)
        result = t_env

    elif p in [
        r"{COMMAND} : Let {var} be the smallest nonnegative integer such that {CONDITION}. (There must be such a {var}, for neither String is a prefix of the other.)",
    ]:
        [let_var, cond] = children[0:2]
        env_for_cond = env0.plus_new_entry(let_var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        result = t_env

    elif p == r"{COMMAND} : Let {var} be an integer for which {NUM_EXPR} is as close to zero as possible. If there are two such {var}, pick the larger {var}.":
        [let_var, num_expr, var2, var3] = children
        assert same_source_text(var2, let_var)
        assert same_source_text(var3, let_var)
        new_env = env0.plus_new_entry(let_var, T_Integer_)
        new_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        result = new_env

#    elif p == r'{COMMAND} : Let {SAB_FUNCTION} be {EX}.':
#        [sab_fn, ex] = children
#        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
#        # result = env0.plus_new_entry(sab_fn, ex_t) # XXX doesn't work
#        result = env1

    # Let {var} and {var} ... be ...

    elif p == r"{COMMAND} : Let {var} and {var} be {LITERAL}.":
        [alet, blet, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        result = env0.plus_new_entry(alet, lit_type).plus_new_entry(blet, lit_type)

# PR 1692 obsoleted
#    elif p == r"{COMMAND} : Let {var} and {var} be new Synchronize events.":
#        [alet, blet] = children
#        result = env0.plus_new_entry(alet, T_Synchronize_event).plus_new_entry(blet, T_Synchronize_event)

    elif p == r"{COMMAND} : Let {var} and {var} be the indirection values provided when this binding for {var} was created.":
        [m_var, n2_var, n_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        result = env0.plus_new_entry(m_var, T_Module_Record).plus_new_entry(n2_var, T_String)

    elif p == r"{COMMAND} : Let {var} and {var} be integers such that {CONDITION} and for which {NUM_EXPR} is as close to zero as possible. If there are two such sets of {var} and {var}, pick the {var} and {var} for which {PRODUCT} is larger.":
        [e_var, n_var, cond, num_expr, e_var2, n_var2, e_var3, n_var3, product] = children
        assert same_source_text(e_var2, e_var)
        assert same_source_text(e_var3, e_var)
        assert same_source_text(n_var2, n_var)
        assert same_source_text(n_var3, n_var)
        new_env = env0.plus_new_entry(e_var, T_Integer_).plus_new_entry(n_var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, new_env)
        t_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        t_env.assert_expr_is_of_type(product, T_MathReal_)
        result = t_env

    elif p in [
        r"{SMALL_COMMAND} : let {var}, {var}, and {var} be integers such that {CONDITION}. Note that {var} is the number of digits in the decimal representation of {var}, that {var} is not divisible by {NUM_LITERAL}, and that the least significant digit of {var} is not necessarily uniquely determined by these criteria",
        r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. Note that the decimal representation of {var} has {SUM} digits, {var} is not divisible by 10, and the least significant digit of {var} is not necessarily uniquely determined by these criteria.",
    ]:
        [vara, varb, varc, cond] = children[0:4]
        env_for_cond = (
            env0.plus_new_entry(vara, T_Integer_)
                .plus_new_entry(varb, T_Integer_)
                .plus_new_entry(varc, T_Integer_)
        )
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        result = env_for_cond

    # ---

    elif p in [
        r"{COMMAND} : Remove the first element from {var} and let {var} be the value of that element.",
        r"{COMMAND} : Remove the first element from {var} and let {var} be the value of the element.",
    ]:
        [list_var, item_var] = children
        list_type = env0.assert_expr_is_of_type(list_var, T_List)
        result = env0.plus_new_entry(item_var, list_type.element_type)

    elif p == r"{COMMAND} : Let {var} be the first element of {var} and remove that element from {var}.":
        [item_var, list_var, list_var2] = children
        assert same_source_text(list_var, list_var2)
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_Tangible_)) # XXX over-specific
        result = env1.plus_new_entry(item_var, T_Tangible_)

    elif p == r"{COMMAND} : Resume the suspended evaluation of {var}. Let {var} be the value returned by the resumed computation.":
        [ctx_var, b_var] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        result = env0.plus_new_entry(b_var, T_Tangible_ | T_return_ | T_throw_)

    elif p in [
        r"{COMMAND} : Resume the suspended evaluation of {var} using {EX} as the result of the operation that suspended it. Let {var} be the completion record returned by the resumed computation.",
        r"{COMMAND} : Resume the suspended evaluation of {var} using {EX} as the result of the operation that suspended it. Let {var} be the value returned by the resumed computation.",
    ]:
        [ctx_var, resa_ex, resb_var] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, T_Tangible_ | T_return_ | T_throw_)
        result = env1.plus_new_entry(resb_var, T_Tangible_)

    elif p == r"{COMMAND} : {var} is an index into the {var} character list, derived from {var}, matched by {var}. Let {var} be the smallest index into {var} that corresponds to the character at element {var} of {var}. If {var} is greater than or equal to the number of elements in {var}, then {var} is the number of code units in {var}.":
        # Once, in RegExpBuiltinExec
        # This step is quite odd, because it refers to _Input_,
        # which you wouldn't think would still exist.
        # (It gets defined in the invocation of _matcher_, i.e. of _R_.[[RegExpMatcher]],
        # i.e., of the internal closure returned by the algorithm
        # associated with <emu-grammar>Pattern :: Disjunction</emu-grammar>)
        # todo: move this step to that closure.
        result = env0.plus_new_entry('_eUTF_', T_Integer_)

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain an? {TYPE_NAME} {var}.":
        [prod_ref, res_type_name, res_var] = children
        res_t = {
            'Matcher'         : T_Matcher,
            'CharSet'         : T_CharSet,
            'character'       : T_character_,
            'integer'         : T_Integer_,
        }[res_type_name.source_text()]
        result = env0.plus_new_entry(res_var, res_t)

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain the three results: an integer {var}, an integer (or &infin;) {var}, and Boolean {var}.":
        [prod_ref, i_var, ii_var, b_var] = children
        result = (env0
            .plus_new_entry(i_var, T_Integer_)
            .plus_new_entry(ii_var, T_Integer_)
            .plus_new_entry(b_var, T_Boolean)
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain the two results: an integer {var} and an integer (or &infin;) {var}.":
        [prod_ref, i_var, ii_var] = children
        result = (env0
            .plus_new_entry(i_var, T_Integer_)
            .plus_new_entry(ii_var, T_Integer_)
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain an? {TYPE_NAME} {var} and a Boolean {var}.":
        [prod_ref, a_type, a_var, b_var] = children
        result = ( 
            env0
            .plus_new_entry(a_var, parse_type_string(a_type.source_text()))
            .plus_new_entry(b_var, T_Boolean)
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} with {PRODUCT} as its {var} argument to obtain an? {TYPE_NAME} {var}.":
        [prod_ref, product, p, r_type, r_var] = children
        assert p.source_text() == '_direction_'
        env0.assert_expr_is_of_type(product, T_Integer_)
        result = (
            env0
            .plus_new_entry(r_var, parse_type_string(r_type.source_text()))
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} with argument {var} to obtain an? {TYPE_NAME} {var}.":
        [prod_ref, arg, r_type, r_var] = children
        assert arg.source_text() == '_direction_'
        env0.assert_expr_is_of_type(arg, T_Integer_)
        result = (
            env0
            .plus_new_entry(r_var, parse_type_string(r_type.source_text()))
        )

    elif p == r"{COMMAND} : Find a value {var} such that {CONDITION}; but if this is not possible (because some argument is out of range), return {LITERAL}.":
        [var, cond, literal] = children
        # once, in MakeDay
        env0.assert_expr_is_of_type(literal, T_Number)
        env1 = env0.plus_new_entry(var, T_Number)
        (t_env, f_env) = tc_cond(cond, env1)
        proc_add_return(env1, T_Number, literal)
        result = env1

    elif p == r'{COMMAND} : Call {PREFIX_PAREN} and let {var} be its result.':
        [prefix_paren, let_var] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        result = env1.plus_new_entry(let_var, t)

    elif p in [
        # r'{COMMAND} : Call {PREFIX_PAREN} and let {var} be the resulting Boolean value.', obs by PR 1797
        r'{COMMAND} : Call {PREFIX_PAREN} and let {var} be the Boolean result.',
    ]:
        [prefix_paren, let_var] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        assert t == T_Boolean
        result = env1.plus_new_entry(let_var, t)

    elif p == r'{COMMAND} : Call {PREFIX_PAREN} and let {var} be the resulting CharSet.':
        [prefix_paren, let_var] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        assert t == T_CharSet
        result = env1.plus_new_entry(let_var, t)

    elif p == r"{COMMAND} : Search {var} for the first occurrence of {var} and let {var} be the index within {var} of the first code unit of the matched substring and let {var} be {var}. If no occurrences of {var} were found, return {var}.":
        [s_var, needle, leta_var, s_var2, letb_var, needle2, needle3, s_var3] = children
        assert same_source_text(s_var, s_var2)
        assert same_source_text(s_var, s_var3)
        assert same_source_text(needle, needle2)
        assert same_source_text(needle, needle3)
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(needle, T_String)
        proc_add_return(env0, T_String, s_var3)
        result = env0.plus_new_entry(leta_var, T_Integer_).plus_new_entry(letb_var, T_String)

    elif p == r"{COMMAND} : Evaluate {PP_NAMED_OPERATION_INVOCATION} to obtain a code unit {var}.":
        [noi, v] = children
        env0.assert_expr_is_of_type(noi, ListType(T_code_unit_))
        result = env0.plus_new_entry(v, T_code_unit_)

    # ---
    # parse

    elif p == r'{COMMAND} : Parse {var} using {nonterminal} as the goal symbol and analyse the parse result for any Early Error conditions. If the parse was successful and no early errors were found, let {var} be the resulting parse tree. Otherwise, let {var} be a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors. Parsing and early error detection may be interweaved in an implementation-defined manner. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present.':
        [source_var, nonterminal, result_var1, result_var2, error_type1] = children
        env1 = env0.ensure_expr_is_of_type(source_var, T_Unicode_code_points_)
        assert env1 is env0
        assert result_var1.children == result_var2.children
        error_type1_name = error_type1.source_text()[1:-1]
        result_type = ptn_type_for(nonterminal) | ListType(NamedType(error_type1_name))
        result = env1.plus_new_entry(result_var1, result_type)
        # but no result variable, hm.

#    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref} and interpreting each of its 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements. The goal symbol for the parse is {nonterminal}. If the result of parsing contains a {nonterminal}, reparse with the goal symbol {nonterminal} and use this result instead. Throw a {ERROR_TYPE} exception if {var} did not conform to the grammar, if any elements of {var} were not matched by the parse, or if any Early Error conditions exist.":
#        [var, emu_xref, goal_nont, other_nont, goal_nont2, error_type, var2, var3] = children
#        assert var.children == var2.children
#        assert var.children == var3.children
#        env0.assert_expr_is_of_type(var, T_String)
#        error_type_name = error_type.source_text()[1:-1]
#        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
#        result = env0
#        # but no result variable, hm.
# ^ obsoleted by PR 1552

#    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref}. The goal symbol for the parse is {nonterminal}. If the result of parsing contains a {nonterminal}, reparse with the goal symbol {nonterminal} and use this result instead. Throw a {ERROR_TYPE} exception if {var} did not conform to the grammar, if any elements of {var} were not matched by the parse, or if any Early Error conditions exist.":
#        [var, emu_xref, goal_nont, other_nont, goal_nont2, error_type, var2, var3] = children
#        assert var.children == var2.children
#        assert var.children == var3.children
#        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
#        error_type_name = error_type.source_text()[1:-1]
#        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
#        result = env0
#        # but no result variable, hm.
# ^ obsoleted by PR 1866

    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref}. The goal symbol for the parse is {nonterminal}. If the result of parsing contains a {nonterminal}, reparse with the goal symbol {nonterminal} and use this result instead.":
        [var, emu_xref, goal_nont, other_nont, goal_nont2] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Unicode_code_points_)
        result = env1
        # but no result variable, hm.

#    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref} and interpreting {var} as UTF-16 encoded Unicode code points ({h_emu_xref}). The goal symbol for the parse is {nonterminal}. Throw a {ERROR_TYPE} exception if {var} did not conform to the grammar, if any elements of {var} were not matched by the parse, or if any Early Error conditions exist.":
#        [var, emu_xref, var2, emu_xref2, goal_nont, error_type, var3, var4] = children
#        assert var.children == var2.children
#        assert var.children == var3.children
#        assert var.children == var4.children
#        env0.assert_expr_is_of_type(var, T_String)
#        error_type_name = error_type.source_text()[1:-1]
#        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
#        result = env0
#        # but no result variable, hm.
# ^ obsoleted by PR 1552

#    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref}. The goal symbol for the parse is {nonterminal}. Throw a {ERROR_TYPE} exception if {var} did not conform to the grammar, if any elements of {var} were not matched by the parse, or if any Early Error conditions exist.":
#        [var, emu_xref, goal_nont, error_type, var3, var4] = children
#        assert var.children == var3.children
#        assert var.children == var4.children
#        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
#        error_type_name = error_type.source_text()[1:-1]
#        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
#        result = env0
#        # but no result variable, hm.
# ^ obsoleted by PR 1866

#    elif p == r"{COMMAND} : Parse {var} interpreted as UTF-16 encoded Unicode points ({h_emu_xref}) as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if {var} is not a valid JSON text as defined in that specification.":
#        [svar, emu_xref, error_type, svar2] = children
#        assert same_source_text(svar, svar2)
#        env0.assert_expr_is_of_type(svar, T_String)
#        result = env0
# ^ obsoleted by PR 1552

    elif p == r"{COMMAND} : Parse {PP_NAMED_OPERATION_INVOCATION} as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if it is not a valid JSON text as defined in that specification.":
        [noi, error_type] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        result = env0

#    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref}. The goal symbol for the parse is {nonterminal}. If the result of parsing contains a {nonterminal}, reparse with the goal symbol {nonterminal}. If {var} did not conform to the grammar, if any elements of {var} were not matched by the parse, or if any Early Error conditions exist, return {LITERAL}. Otherwise, return {LITERAL}.":
#        [var, emu_xref, goal_nont, contained_nont, foal_nont2, var2, var3, lita, litb] = children
#        assert var.children == var2.children
#        assert var.children == var3.children
#        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
#        env0.assert_expr_is_of_type(lita, T_Boolean)
#        env0.assert_expr_is_of_type(litb, T_Boolean)
#        proc_add_return(env0, T_Boolean, lita)
#        proc_add_return(env0, T_Boolean, litb)
#        result = None
# ^ obsoleted by PR 1866

#    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref}. The goal symbol for the parse is {nonterminal}. If {var} did not conform to the grammar, if any elements of {var} were not matched by the parse, or if any Early Error conditions exist, return {LITERAL}. Otherwise, return {LITERAL}.":
#        [var, emu_xref, goal_nont, var2, var3, lita, litb] = children
#        assert var.children == var2.children
#        assert var.children == var3.children
#        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
#        env0.assert_expr_is_of_type(lita, T_Boolean)
#        env0.assert_expr_is_of_type(litb, T_Boolean)
#        proc_add_return(env0, T_Boolean, lita)
#        proc_add_return(env0, T_Boolean, litb)
#        result = None
# ^ obsoleted by PR 1866

    elif p == r"{COMMAND} : Parse {var} using the grammars in {h_emu_xref}. The goal symbol for the parse is {nonterminal}.":
        [var, emu_xref, goal_nont] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Unicode_code_points_)
        result = env1

    # ----------------------------------
    # IF stuff

    elif p in [
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise, {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}.',
        r"{IF_CLOSED} : If {CONDITION}&mdash;note that these mathematical values are both finite and not both zero&mdash;{SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}.",
    ]:
        [cond, t_command, f_command] = children
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        result = env_or(t_benv, f_benv)

#    elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; but if {CONDITION}, {SMALL_COMMAND}.":
#        [cond, t_command, cond2, f_command] = children
#        assert cond2.source_text() == 'there is no such integer _k_'
#        # so "but if {CONDITION}" = "else"
#        (t_env, f_env) = tc_cond(cond, env0)
#        t_benv = tc_nonvalue(t_command, t_env)
#        f_benv = tc_nonvalue(f_command, f_env)
#        result = env_or(t_benv, f_benv)
# ^ obsoleted by PR #2009

    elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}. {var} will be used throughout the algorithms in {h_emu_xref}. Each element of {var} is considered to be a character.":
        [cond, t_command, f_command, _, _, _] = children
        (t_env, f_env) = tc_cond(cond, env0)
        t_env2 = tc_nonvalue(t_command, t_env)
        f_env2 = tc_nonvalue(f_command, f_env)
        result = env_or(t_env2, f_env2)

    elif p == r'{IF_OTHER} : {IF_OPEN}{IF_TAIL}':
        [if_open, if_tail] = children

        benvs = []

        if if_open.prod.rhs_s in [
            r'If {CONDITION}, {SMALL_COMMAND}.',
            r'If {CONDITION}, then {SMALL_COMMAND}.',
            r'If {CONDITION}, then{IND_COMMANDS}',
            r'If {CONDITION}, {MULTILINE_SMALL_COMMAND}',
        ]:
            [condition, then_part] = if_open.children[0:2]
            (t_env, f_env) = tc_cond(condition, env0)
            benvs.append( tc_nonvalue(then_part, t_env) )
        else:
            assert 0, str(if_open.prod)

        while True:
            if if_tail.prod.rhs_s == '{_NL_N} {ELSEIF_PART}{IF_TAIL}':
                [elseif_part, next_if_tail] = if_tail.children
                [condition, then_part] = elseif_part.children
                (t_env, f_env) = tc_cond(condition, f_env)
                benvs.append( tc_nonvalue(then_part, t_env) )
                if_tail = next_if_tail

            elif if_tail.prod.rhs_s == '{_NL_N} {ELSE_PART}':
                [else_part] = if_tail.children
                benvs.append( tc_nonvalue(else_part, f_env) )
                break

            elif if_tail.prod.rhs_s == '{EPSILON}':
                [] = if_tail.children
                # This is like "Else, nothing"
                benvs.append( f_env )
                break

            else:
                assert 0

        result = envs_or(benvs)

        if if_open.source_text() == 'If |BooleanLiteral| is the token `true`, return *true*.':
            # After this step, the possibilities for BooleanLiteral have been exhausted,
            # but that's not obvious from the code.
            # todo: change "If" to "Else"?
            result = None

#    elif p in [
#        r'{ELSE_PART} : Else {CONDITION},{IND_COMMANDS}',
#        r"{ELSE_PART} : Else {CONDITION}, {SMALL_COMMAND}.",
#    ]:
#        [cond, commands] = children
#        (t_env, f_env) = tc_cond(cond, env0, asserting=True)
#        # throw away f_env
#        result = tc_nonvalue(commands, t_env)

    # ----------------------------------
    # Returning (normally or abruptly)

    elif p in [
        # r"{COMMAND} : Return {EXPR}. This call will always return *true*.", # PR #1924
        r"{COMMAND} : Return {EXPR}.",
        r"{COMMAND} : Return {MULTILINE_EXPR}",
        r"{MULTILINE_SMALL_COMMAND} : return {MULTILINE_EXPR}",
        r"{IAO_BODY} : Returns {EXPR}.",
        r"{SMALL_COMMAND} : return {EXPR}",
    ]:
        [expr] = children
        (t1, env1) = tc_expr(expr, env0)
        # assert env1 is env0
        if False and trace_this_op:
            print("Return command's expr has type", t1)
        proc_add_return(env1, t1, anode)
        result = None

    elif p == r"{COMMAND} : Return.":
        [] = children
        # A "return" statement without a value in an algorithm step
        # means the same thing as: Return NormalCompletion(*undefined*).
        proc_add_return(env0, T_Undefined, anode)
        result = None


    elif p == r'{COMMAND} : Call {PREFIX_PAREN} and return its result.':
        [prefix_paren] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        proc_add_return(env1, t, anode)
        result = None

    elif p == r'{COMMAND} : Call {PREFIX_PAREN} and return its Matcher result.':
        [prefix_paren] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        assert t == T_Matcher
        proc_add_return(env1, t, anode)
        result = None

    elif p == r'{IAO_BODY} : Returns {LITERAL} if {CONDITION}; otherwise returns {LITERAL}.':
        [t_lit, cond, f_lit] = children
        (t_env, f_env) = tc_cond(cond, env0)
        (t_lit_type, _) = tc_expr(t_lit, env0)
        (f_lit_type, _) = tc_expr(f_lit, env0)
        proc_add_return(t_env, t_lit_type, t_lit)
        proc_add_return(f_env, f_lit_type, f_lit)
        result = None

    elif p in [
        r"{COMMAND} : Throw a {ERROR_TYPE} exception.",
        r"{SMALL_COMMAND} : throw a {ERROR_TYPE} exception because the structure is cyclical",
        r'{SMALL_COMMAND} : throw a {ERROR_TYPE} exception',
    ]:
        [error_type] = children
        error_type_name = error_type.source_text()[1:-1]
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), anode)
        result = None

    # ----------------------------------
    # Iteration

    elif p in [
        r'{COMMAND} : Repeat,{IND_COMMANDS}',
        r"{MULTILINE_SMALL_COMMAND} : repeat:{IND_COMMANDS}",
    ]:
        [commands] = children

        env_at_bottom = tc_nonvalue(commands, env0)

        # The only way to leave a condition-less Repeat
        # is via a Return command,
        # so there can't be anything (except maybe a NOTE) after the loop.
        result = None

        # XXX Should repeat the analysis, feeding the bottom env to the top,
        # XXX until no change.
        # XXX (and likewise with other loops)


    elif p in [
        r'{COMMAND} : Repeat, while {CONDITION},{IND_COMMANDS}',
        r"{COMMAND} : Repeat, until {CONDITION},{IND_COMMANDS}",
    ]:
        [cond, commands] = children
        (t_env, f_env) = tc_cond(cond, env0)

        if 'while' in p:
            (stay_env, exit_env) = (t_env, f_env)
        elif 'until' in p:
            (stay_env, exit_env) = (f_env, t_env)
        else:
            assert 0

        bottom_env = tc_nonvalue(commands, stay_env)
        reduced_bottom_env = bottom_env.reduce(stay_env.vars.keys())
        # assert reduced_bottom_env.equals(stay_env)
        result = exit_env

        # hack!:
        if cond.source_text() == '_matchSucceeded_ is *false*': # in RegExpBuiltinExec
            # This case requires that variable _r_, introduced within the loop,
            # survive the loop.
            # (It doesn't have to survive from one iteration to the next,
            # just from the last iteration to after.)
            result = result.plus_new_entry('_r_', T_State)

    elif p == r"{COMMAND} : While {CONDITION}, an implementation may perform the following steps:{IND_COMMANDS}":
        [cond, commands] = children
        (t_env, f_env) = tc_cond(cond, env0)
        bottom_env = tc_nonvalue(commands, t_env)
        reduced_bottom_env = bottom_env.reduce(t_env.vars.keys())
        result = f_env

    elif p in [
        r'{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}',
        r'{COMMAND} : For each {EACH_THING}, {SMALL_COMMAND}.',
        r"{COMMAND} : Repeat, for each {EACH_THING},?{IND_COMMANDS}",
    ]:
        [each_thing, commands] = children

        # generic list:
        if each_thing.prod.rhs_s in [
            r"element {var} in {DOTTING}",
            r"element {var} in {var}",
            r"element {var} of {EX}",
            r"element {var} of {var} in List order",
            r"element {var} of {var}, in ascending index order",
            r"{var} from {var} in list order",
            r"{var} in {var} in List order",
            r"{var} in {var}",
            r"{var} in {var}, in original insertion order",
            r"{var} in {var}, in reverse list order",
            r"{var} of {var}",
            r"{var} of {var} in List order",
            r"{var} that is an element of {var}",
            r"{var} that is an element of {var}, in original insertion order",
        ]:
            [loop_var, collection_expr] = each_thing.children
            (list_type, env1) = tc_expr(collection_expr, env0); assert env1 is env0
            if list_type == T_List:
                # want to assert that this doesn't happen,
                # but _kept_ in %TypedArray%.prototype.filter
                element_type = T_TBD
            elif list_type == T_TBD:
                element_type = T_TBD
            else:
                assert isinstance(list_type, ListType), list_type
                element_type = list_type.element_type
            env_for_commands = env1.plus_new_entry(loop_var, element_type)

        # ---------------------
        # list of specific type:

        elif each_thing.prod.rhs_s == r"Agent Events Record {var} in {DOTTING}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_Agent_Events_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_Agent_Events_Record)

        elif each_thing.prod.rhs_s == r"event {var} in {DOTTING}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_event_))
            env_for_commands = env1.plus_new_entry(loop_var, T_event_)

        elif each_thing.prod.rhs_s == r"ExportEntry Record {var} in {EX}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_ExportEntry_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_ExportEntry_Record)

        elif each_thing.prod.rhs_s == r"Record { {DSBN}, {DSBN} } {var} in {var}":
            [dsbn1, dsbn2, loop_var, collection_expr] = each_thing.children
            assert dsbn1.source_text() == '[[Module]]'
            assert dsbn2.source_text() == '[[ExportName]]'
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_ExportResolveSet_Record_))
            env_for_commands = env1.plus_new_entry(loop_var, T_ExportResolveSet_Record_)

        elif each_thing.prod.rhs_s in [
            r"Record { {DSBN}, {DSBN} } {var} that is an element of {var}",
            r"Record { {DSBN}, {DSBN} } {var} that is an element of {var}, in original key insertion order",
        ]:
            [dsbn1, dsbn2, loop_var, collection_expr] = each_thing.children
            assert dsbn1.source_text() == '[[Key]]'
            assert dsbn2.source_text() == '[[Value]]'
            # hack:
            if collection_expr.source_text() == '_importMetaValues_':
                element_type = T_ImportMeta_record_ # PR 1892
            elif collection_expr.source_text() == '_entries_':
                element_type = T_MapData_record_
            else:
                assert 0, collection_expr
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(element_type))
            env_for_commands = env1.plus_new_entry(loop_var, element_type)

        elif each_thing.prod.rhs_s == r"Record { {DSBN}, {DSBN}, {DSBN} } {var} that is an element of {DOTTING}":
            [dsbn1, dsbn2, dsbn3, loop_var, collection_expr] = each_thing.children
            assert dsbn1.source_text() == '[[WeakRefTarget]]'
            assert dsbn2.source_text() == '[[HeldValue]]'
            assert dsbn3.source_text() == '[[UnregisterToken]]'
            element_type = T_FinalizationRegistryCellRecord_
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(element_type))
            env_for_commands = env1.plus_new_entry(loop_var, element_type)

        elif each_thing.prod.rhs_s == 'ImportEntry Record {var} in {EX}':
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_ImportEntry_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_ImportEntry_Record)

        elif each_thing.prod.rhs_s == r"Parse Node {var} in {var}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_Parse_Node))
            env_for_commands = env1.plus_new_entry(loop_var, T_Parse_Node)

        elif each_thing.prod.rhs_s == r"String {var} that is an element of {EX}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_String))
            env_for_commands = env1.plus_new_entry(loop_var, T_String)

        elif each_thing.prod.rhs_s == r"Cyclic Module Record {var} in {var}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_Cyclic_Module_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_Cyclic_Module_Record)

        elif each_thing.prod.rhs_s in [
            r"{nonterminal} {var} in {var}",
            r"{nonterminal} {var} in {var} (NOTE: this is another complete iteration of {PROD_REF})",
            r"{nonterminal} {var} in order from {var}",
        ]:
            [nont, loop_var, collection_expr] = each_thing.children[0:3]
            env0.assert_expr_is_of_type(collection_expr, ListType(T_Parse_Node))
            env_for_commands = env0.plus_new_entry(loop_var, ptn_type_for(nont))

        elif each_thing.prod.rhs_s in [
            r"String {var} in {PP_NAMED_OPERATION_INVOCATION}",
            r"String {var} in {var}, in list order",
            r"String {var} in {var}",
            r"string {var} in {var}",
        ]:
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_String))
            env_for_commands = env1.plus_new_entry(loop_var, T_String)

        elif each_thing.prod.rhs_s == 'code point {var} in {var}':
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, T_Unicode_code_points_)
            env_for_commands = env1.plus_new_entry(loop_var, T_code_point_)

        elif each_thing.prod.rhs_s == 'code point {var} in {PP_NAMED_OPERATION_INVOCATION}':
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, T_Unicode_code_points_)
            env_for_commands = env1.plus_new_entry(loop_var, T_code_point_)

        # explicit-exotics:
        elif each_thing.prod.rhs_s == r"internal slot in {var}":
            [collection_expr] = each_thing.children
            loop_var = None # todo: no loop variable!
            env0.assert_expr_is_of_type(collection_expr, ListType(T_SlotName_))
            env_for_commands = env0

        # ------------------------
        # property keys of an object:

        elif each_thing.prod.rhs_s == r"own property key {var} of {var} that is an array index, whose numeric value is greater than or equal to {var}, in descending numeric index order":
            [loop_var, obj_var, lo_var] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env0.assert_expr_is_of_type(lo_var, T_Number)
            env_for_commands = env0.plus_new_entry(loop_var, T_String)

#         elif each_thing.prod.rhs_s in [
#             r"own property key {var} of {var} that is an array index, in ascending numeric index order",
#             r"own property key {var} of {var} that is a String but is not an array index, in ascending chronological order of property creation",
#         ]:
#             [loop_var, obj_var] = each_thing.children
#             env0.assert_expr_is_of_type(obj_var, T_Object)
#             env_for_commands = env0.plus_new_entry(loop_var, T_String)
# 
#         elif each_thing.prod.rhs_s == r"own property key {var} of {var} that is a Symbol, in ascending chronological order of property creation":
#             [loop_var, obj_var] = each_thing.children
#             env0.assert_expr_is_of_type(obj_var, T_Object)
#             env_for_commands = env0.plus_new_entry(loop_var, T_Symbol)
# ^ obsoleted by the merge of PR #1923

        elif each_thing.prod.rhs_s in [
            r"own property key {var} of {var} such that {CONDITION}, in ascending numeric index order",
            r"own property key {var} of {var} such that {CONDITION}, in ascending chronological order of property creation",
        ]:
            [loop_var, obj_var, condition] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env1 = env0.plus_new_entry(loop_var, T_String | T_Symbol)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"property of the Global Object specified in clause {h_emu_xref}":
            [emu_xref] = each_thing.children
            # no loop_var!
            env_for_commands = env0

        # -----------------------
        # other collections:

        elif each_thing.prod.rhs_s == r"event {var} in {PP_NAMED_OPERATION_INVOCATION}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, T_Set)
            env_for_commands = env1.plus_new_entry(loop_var, T_event_)

        elif each_thing.prod.rhs_s == r"index {var} of {var}":
            [loop_var, collection_var] = each_thing.children
            env0.assert_expr_is_of_type(collection_var, T_Shared_Data_Block)
            env_for_commands = env0.plus_new_entry(loop_var, T_Integer_)

        elif each_thing.prod.rhs_s == r"ReadSharedMemory or ReadModifyWriteSharedMemory event {var} in SharedDataBlockEventSet({var})":
            [loop_var, collection_var] = each_thing.children
            env0.assert_expr_is_of_type(collection_var, T_candidate_execution)
            env_for_commands = env0.plus_new_entry(loop_var, T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event)

        elif each_thing.prod.rhs_s == r"field of {var} that is present":
            [desc_var] = each_thing.children
            loop_var = None # todo: no loop variable!
            env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
            env_for_commands = env0

        elif each_thing.prod.rhs_s == r"binding named {var} in {EX}":
            # PR 1668
            # XXX Really, it's more like:
            # For each binding _B_ in {EX}, do
            #     Let _N_ be the name for which _B_ is a binding.
            [name_var, envrec_ex] = each_thing.children
            env0.assert_expr_is_of_type(envrec_ex, T_Environment_Record)
            env_for_commands = env0.plus_new_entry(name_var, T_String)

        # things from a large (possibly infinite) set, those that satisfy a condition:

        elif each_thing.prod.rhs_s in [
            r"integer {var} that satisfies {CONDITION}",
            r"integer {var} such that {CONDITION}",
        ]:
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Integer_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"integer {var} starting with 0 such that {CONDITION}, in ascending order":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Integer_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"event {var} such that {CONDITION}":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Shared_Data_Block_event)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"FinalizationRegistry {var} such that {CONDITION}":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_FinalizationRegistry_object_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"WeakMap {var} such that {CONDITION}":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_WeakMap_object_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"WeakRef {var} such that {CONDITION}":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_WeakRef_object_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"WeakSet {var} such that {CONDITION}":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_WeakSet_object_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"character {var} not in set {var} where {PP_NAMED_OPERATION_INVOCATION} is in {var}":
            [loop_var, charset_var, noi, charset_var2] = each_thing.children
            assert charset_var.children == charset_var2.children
            env0.assert_expr_is_of_type(charset_var, T_CharSet)
            env1 = env0.plus_new_entry(loop_var, T_character_)
            env1.assert_expr_is_of_type(noi, T_character_)
            env_for_commands = env1


        # elif each_thing.prod.rhs_s == r"WriteSharedMemory or ReadModifyWriteSharedMemory event {var} in SharedDataBlockEventSet({var})":
        # elif each_thing.prod.rhs_s == r"child node {var} of this Parse Node":
        # elif each_thing.prod.rhs_s == r"code point {var} in {var}, in order":
        # elif each_thing.prod.rhs_s == r"element {var} in {NAMED_OPERATION_INVOCATION}":
        # elif each_thing.prod.rhs_s == r"event {var} in {var}":
        # elif each_thing.prod.rhs_s == r"integer {var} in the range 0&le;{var}&lt; {var}":
        # elif each_thing.prod.rhs_s == r"pair of events {var} and {var} in EventSet({var})":
        # elif each_thing.prod.rhs_s == r"pair of events {var} and {var} in HostEventSet({var})":
        # elif each_thing.prod.rhs_s == r"pair of events {var} and {var} in SharedDataBlockEventSet({var})":
        # elif each_thing.prod.rhs_s == r"pair of events {var} and {var} in SharedDataBlockEventSet({var}) such that {CONDITION}":
        # elif each_thing.prod.rhs_s == r"record {var} in {var}":
        # elif each_thing.prod.rhs_s == r"{nonterminal} {var} that is directly contained in the {nonterminal} of a {nonterminal}, {nonterminal}, or {nonterminal}":
        # elif each_thing.prod.rhs_s == r"{nonterminal} {var} that is directly contained in the {nonterminal} of a {nonterminal}, {nonterminal}, or {nonterminal} Contained within {var}":

        else:
            stderr()
            stderr("each_thing:")
            stderr('        elif each_thing.prod.rhs_s == r"%s":' % each_thing.prod.rhs_s)
            sys.exit(0)

        env_after_commands = tc_nonvalue(commands, env_for_commands)
        # XXX do I need to feed this back somehow?

        # Assume the loop-var doesn't survive the loop
        # if loop_var:
        #     result = env_after_commands.with_var_removed(loop_var)
        # else:
        #     result = env_after_commands

        # The only variables that 'exit' the loop are those that existed beforehand.
        if env_after_commands is None:
            # happens in Coherent Reads
            result = None
        else:
            names = env0.vars.keys()
            result = env_after_commands.reduce(names)

    # ----------------------------------
    # Assert

    elif p in [
        r'{COMMAND} : Assert: {CONDITION}.',
        r"{SMALL_COMMAND} : Assert: {CONDITION}",
    ]:
        [condition] = children
        (t_env, f_env) = tc_cond(condition, env0, asserting=True)
        # throw away f_env
        result = t_env

    elif p in [
        r"{COMMAND} : Assert: If {CONDITION}, then {CONDITION}.",
        r"{COMMAND} : Assert: If {CONDITION}, {CONDITION}.",
    ]:
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, t1_env, asserting=True)
        result = env_or(f1_env, t2_env)

    elif p == r"{COMMAND} : Assert: Unless {CONDITION_1}, {CONDITION}.":
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, f1_env, asserting=True)
        result = env_or(t1_env, t2_env)

    elif p == r"{COMMAND} : Assert: {CONDITION_1} if and only if {CONDITION_1}.":
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, env0)
        result = env_or(
            env_and(t1_env, t2_env),
            env_and(f1_env, f2_env)
        )

    elif p == r"{COMMAND} : Assert: {CONDITION_1} if {CONDITION_1}; otherwise, {CONDITION_1}.":
        [cond_t, cond_x, cond_f] = children
        (xt_env, xf_env) = tc_cond(cond_x, env0)
        (tt_env, tf_env) = tc_cond(cond_t, xt_env, asserting=True)
        (ft_env, ff_env) = tc_cond(cond_f, xf_env, asserting=True)
        result = env_or(tt_env, ft_env)

    # ----------------------------------
    # execution context

    elif p == r'{COMMAND} : Pop {var} from the execution context stack. The execution context now on the top of the stack becomes the running execution context.':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_execution_context)

    elif p == r'{COMMAND} : Push {var} onto the execution context stack; {var} is now the running execution context.':
        [var1, var2] = children
        assert var1.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var1, T_execution_context)
        result = env1

    elif p == r'{COMMAND} : Remove {var} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Remove {var} from the execution context stack and restore {var} as the running execution context.":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        env0.assert_expr_is_of_type(bvar, T_execution_context)
        result = env0

    # PR 1670:
    elif p == r"{COMMAND} : Remove {var} from the execution context stack.":
        [avar] = children    
        env0.assert_expr_is_of_type(avar, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Resume the context that is now on the top of the execution context stack as the running execution context.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Resume the suspended evaluation of {var} using {EX} as the result of the operation that suspended it.":
        [ctx_var, res_ex] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env0.assert_expr_is_of_type(res_ex, T_Tangible_ | T_return_ | T_throw_)
        result = env0

    elif p == r"{COMMAND} : Suspend {var} and remove it from the execution context stack.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p in [
        r"{COMMAND} : Suspend the currently running execution context.",
        # r"{COMMAND} : Suspend the running execution context and remove it from the execution context stack.", # PR 1597
    ]:
        [] = children
        result = env0

    elif p == r'{SMALL_COMMAND} : suspend {var}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Suspend {var}.':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_execution_context)

    elif p == r"{COMMAND} : Set {SETTABLE} such that when evaluation is resumed for that execution context the following steps will be performed:{IND_COMMANDS}":
        [settable, commands] = children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env0)
        result = env0

    elif p == r'{COMMAND} : Set {SETTABLE} such that when evaluation is resumed with a Completion {var} the following steps will be performed:{IND_COMMANDS}':
        [settable, comp_var, commands] = children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        #
        env_for_commands = env0.plus_new_entry(comp_var, T_Tangible_ | T_throw_)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env_for_commands)
        #
        result = env0

    elif p == r"{COMMAND} : Perform any necessary implementation-defined initialization of {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Once a generator enters the {tilded_word} state it never leaves it and its associated execution context is never resumed. Any execution state associated with {var} can be discarded at this point.':
        [tw, var] = children
        assert tw.source_text() == '~completed~'
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    # ----------------------------------

    elif p in [
        r'{COMMAND} : Set {SETTABLE} to {EXPR}.',
        r'{COMMAND} : Set {SETTABLE} to {MULTILINE_EXPR}',
        r'{SMALL_COMMAND} : set {SETTABLE} to {EXPR}',
    ]:
        [settable, expr] = children
        result = env0.set_A_to_B(settable, expr)

# obsoleted by PR 1831
#    elif p == r'{COMMAND} : Set {SETTABLE} to {EXPR}. {note}':
#        [settable, expr, note] = children
#        result = env0.set_A_to_B(settable, expr)

    elif p == r'{COMMAND} : Set all of the bytes of {var} to 0.':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block)
        result = env1

    elif p == r'{COMMAND} : Wait until no agent is in the critical section for {var}, then enter the critical section for {var} (without allowing any other agent to enter).':
        [var1, var2] = children
        [var_name1] = var1.children
        [var_name2] = var2.children
        assert var_name1 == var_name2
        env1 = env0.ensure_expr_is_of_type(var1, T_WaiterList)
        result = env1

    elif p in [
        r"{COMMAND} : Set {var}'s essential internal methods to the default ordinary object definitions specified in {h_emu_xref}.",
        r"{COMMAND} : Set {var}'s essential internal methods to the definitions specified in {h_emu_xref}.",
    ]:
        [var, emu_xref] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        result = env1

    elif p in [
        r"{COMMAND} : Add {EX} as the last element of {var}.",
        r"{COMMAND} : Add {var} as an element of the list {var}.",
        r"{COMMAND} : Append {EX} as an element of {var}.",
        r"{COMMAND} : Append {EX} as the last element of the List that is {DOTTING}.",
        r"{COMMAND} : Append {EX} as the last element of the List {var}.",
        r"{COMMAND} : Append {EX} as the last element of {var}.",
        r"{COMMAND} : Append {EX} to the end of the List {var}.",
        r"{COMMAND} : Append {EX} to the end of {var}.",
        r"{COMMAND} : Append {EX} to {EX}.",
        r"{COMMAND} : Insert {var} as the first element of {var}.",
        r"{SMALL_COMMAND} : append {LITERAL} to {var}",
        r"{SMALL_COMMAND} : append {var} to {var}",
    ]:
        [value_ex, list_ex] = children
        result = env0.ensure_A_can_be_element_of_list_B(value_ex, list_ex)

    elif p in [
        r'{COMMAND} : Append to {var} the elements of {EXPR}.',
        r"{COMMAND} : Append to {var} {EXPR}.",
        r"{COMMAND} : Append all the entries of {var} to the end of {var}.",
        r"{COMMAND} : Append each item in {var} to the end of {var}.",
    ]:
        [ex1, ex2] = children
        (t1, env1) = tc_expr(ex1,  env0); assert env1 is env0
        (t2, env2) = tc_expr(ex2, env0); assert env2 is env0
        if t1 == T_TBD and t2 == T_TBD:
            pass
        elif t1 == T_List and t2 == T_TBD:
            pass
        elif t1 == T_List and t2 == T_List:
            pass
        elif isinstance(t1, ListType) and t2 == T_TBD:
            env0 = env0.with_expr_type_replaced(ex2, t1)
        elif t1 == T_List and isinstance(t2, ListType):
            env0 = env0.with_expr_type_replaced(ex1, t2)
        elif isinstance(t1, ListType) and isinstance(t2, ListType):
            if t1 == t2:
                pass
            elif 'Append to' in p and t1.is_a_subtype_of_or_equal_to(t2):
                # widen ex1 to be able to accept ex2
                env0 = env0.with_expr_type_replaced(ex1, t2)
            elif ('Append all' in p or 'Append each' in p) and t2.is_a_subtype_of_or_equal_to(t1):
                env0 = env0.with_expr_type_replaced(ex2, t1)
            else:
                assert 0
        else:
            assert t1.is_a_subtype_of_or_equal_to(T_List)
            assert t2.is_a_subtype_of_or_equal_to(T_List)
            assert t1 == t2
        result = env0

    elif p == r"{COMMAND} : Append the pair (a two element List) consisting of {var} and {var} to the end of {var}.":
        [avar, bvar, list_var] = children
        env0.assert_expr_is_of_type(avar, T_String | T_Symbol)
        env0.assert_expr_is_of_type(bvar, T_Property_Descriptor)
        (list_type, env1) = tc_expr(list_var, env0); assert env1 is env0
        assert list_type == T_List
        result = env0.with_expr_type_narrowed(list_var, ListType(ListType(T_TBD)))

    elif p == r'{COMMAND} : Append to {var} each element of {var} that is not already an element of {var}.':
        [vara, varb, varc] = children
        (vara_type, enva) = tc_expr(vara, env0); assert enva is env0
        (varb_type, envb) = tc_expr(varb, env0); assert envb is env0
        (varc_type, envc) = tc_expr(varc, env0); assert envc is env0
        if vara_type == T_TBD and varb_type == T_TBD and varc_type == T_TBD:
            pass
        else:
            assert vara_type.is_a_subtype_of_or_equal_to(T_List)
            assert vara_type == varb_type
            assert varb_type == varc_type
        result = env0

    elif p in [
        r'{COMMAND} : Set {DOTTING} as described in {h_emu_xref}.',
        r'{COMMAND} : Set {DOTTING} as specified in {h_emu_xref}.',
        r'{COMMAND} : Set {DOTTING} to the definition specified in {h_emu_xref}.',
    ]:
        [dotting, emu_xref] = children

        # (t, env1) = tc_expr(settable, env0); assert env1 is env0
        # XXX: could check that emu_xref is sensible for t, but not really worth it?

        mo = re.fullmatch(r'<emu-xref href="#([^"<>]+)"></emu-xref>', emu_xref.source_text())
        sec_id = mo.group(1)
        implied_base_t = {
            # 9.2.*
            'sec-ecmascript-function-objects-call-thisargument-argumentslist'                        : T_function_object_,
            'sec-ecmascript-function-objects-construct-argumentslist-newtarget'                      : T_constructor_object_,

            # 9.4.1.*
            'sec-bound-function-exotic-objects-call-thisargument-argumentslist'                      : T_bound_function_exotic_object_,
            'sec-bound-function-exotic-objects-construct-argumentslist-newtarget'                    : T_bound_function_exotic_object_,

            # 9.4.2.*
            'sec-array-exotic-objects-defineownproperty-p-desc'                                      : T_Array_object_,

            # 9.4.3.*
            'sec-string-exotic-objects-getownproperty-p'                                             : T_String_exotic_object_,
            'sec-string-exotic-objects-defineownproperty-p-desc'                                     : T_String_exotic_object_,
            'sec-string-exotic-objects-ownpropertykeys'                                              : T_String_exotic_object_,

            # 9.4.4.*
            'sec-arguments-exotic-objects-getownproperty-p'                                          : T_Object,
            'sec-arguments-exotic-objects-defineownproperty-p-desc'                                  : T_Object,
            'sec-arguments-exotic-objects-get-p-receiver'                                            : T_Object,
            'sec-arguments-exotic-objects-set-p-v-receiver'                                          : T_Object,
            'sec-arguments-exotic-objects-delete-p'                                                  : T_Object,

            # 9.4.5.*
            'sec-integer-indexed-exotic-objects-getownproperty-p'                                    : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-hasproperty-p'                                       : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-defineownproperty-p-desc'                            : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-get-p-receiver'                                      : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-set-p-v-receiver'                                    : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-ownpropertykeys'                                     : T_Integer_Indexed_object_,

            # 9.5.*
            'sec-proxy-object-internal-methods-and-internal-slots-call-thisargument-argumentslist'   : T_Proxy_exotic_object_,
            'sec-proxy-object-internal-methods-and-internal-slots-construct-argumentslist-newtarget' : T_Proxy_exotic_object_,

        }[sec_id]

        assert dotting.prod.rhs_s == '{var}.{DSBN}'
        [base_var, dsbn] = dotting.children

        (curr_base_t, env1) = tc_expr(base_var, env0); assert env1 is env0
        if curr_base_t == T_Object:
            result = env1.with_expr_type_narrowed(base_var, implied_base_t)
        elif curr_base_t == T_bound_function_exotic_object_ | T_Proxy_exotic_object_ | T_other_function_object_ and implied_base_t == T_constructor_object_:
            result = env1.with_expr_type_replaced(base_var, implied_base_t)
        elif curr_base_t == implied_base_t:
            result = env1
        else:
            assert 0

    elif p == r'{COMMAND} : Leave the critical section for {var}.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        result = env0

    elif p == r'{COMMAND} : Create own properties of {var} corresponding to the definitions in {h_emu_xref}.':
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r'{SMALL_COMMAND} : reverse the order of the elements of {var}':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_List)

    elif p in [
        r'{COMMAND} : Add {var} to {var}.',
        r"{SMALL_COMMAND} : add {var} to {var}",
    ]:
        [item_var, collection_var] = children
        (item_type, env1) = tc_expr(item_var, env0); assert env1 is env0
        (collection_type, env2) = tc_expr(collection_var, env0); assert env2 is env0
        if item_type.is_a_subtype_of_or_equal_to(T_event_) and collection_type == T_Set:
            pass
        elif item_type == T_character_ and collection_type == T_CharSet:
            pass
        else:
            assert 0
        result = env0

#    elif p == r"{COMMAND} : Increment {var}.":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_Integer_)
#        result = env0
#
#    elif p in [
#        r'{COMMAND} : Increment {var} by {NUM_LITERAL}.',
#        r'{COMMAND} : Decrement {var} by {NUM_LITERAL}.',
#        r'{COMMAND} : Increase {var} by {NUM_LITERAL}.',
#        r"{COMMAND} : Decrease {var} by {NUM_LITERAL}.",
#        r"{SMALL_COMMAND} : increase {var} by {NUM_LITERAL}",
#    ]:
#        [var, num_literal] = children
#        env0.assert_expr_is_of_type(num_literal, T_Integer_)
#        result = env0.ensure_expr_is_of_type(var, T_Integer_)
#
#    elif p == r'{COMMAND} : Increment {var} and {var} each by {NUM_LITERAL}.':
#        [vara, varb, num_literal] = children
#        env0.assert_expr_is_of_type(num_literal, T_Integer_)
#        result = env0.ensure_expr_is_of_type(vara, T_Integer_).ensure_expr_is_of_type(varb, T_Integer_)

    elif p == r'{COMMAND} : {note}':
        result = env0

    elif p == r'{COMMAND} : Create an immutable indirect binding in {var} for {var} that references {var} and {var} as its target binding and record that the binding is initialized.':
        [er_var, n_var, m_var, n2_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(m_var, T_Module_Record)
        env0.assert_expr_is_of_type(n2_var, T_String)
        result = env0

#    elif p == r'{COMMAND} : Perform any implementation or host environment defined processing of {var}. This may include modifying the {DSBN} field or any other field of {var}.':
#        [var1, dsbn, var2] = children
#        assert var1.children == var2.children
#        env0.assert_expr_is_of_type(var1, T_PendingJob)
#        result = env0
#
#    elif p == r"{COMMAND} : Perform any implementation or host environment defined job initialization using {var}.":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_PendingJob)
#        result = env0
#
#    elif p == r'{COMMAND} : Add {var} at the back of the Job Queue named by {var}.':
#        [job_var, queue_var] = children
#        env0.assert_expr_is_of_type(job_var, T_PendingJob)
#        env0.assert_expr_is_of_type(queue_var, T_String)
#        result = env0
# ^ obsoleted by PR 1597

#    elif p == r"{COMMAND} : Set {var}'s essential internal methods (except for {DSBN} and {DSBN}) to the definitions specified in {h_emu_xref}.":
#        [var, dsbn1, dsbn2, emu_xref] = children
#        env0.assert_expr_is_of_type(var, T_Object)
#        result = env0
# ^ obsoleted by PR 1460

    elif p in [
        r"{SMALL_COMMAND} : store the individual bytes of {var} into {var}, in order, starting at {var}[{var}]",
        r"{COMMAND} : Store the individual bytes of {var} into {var}, in order, starting at {var}[{var}].",

    ]:
        [var1, var2, var3, var4] = children
        env0.assert_expr_is_of_type(var1, ListType(T_Integer_))
        env1 = env0.ensure_expr_is_of_type(var2, T_Data_Block)
        assert var3.children == var2.children
        env0.assert_expr_is_of_type(var4, T_Integer_)
        result = env1

    elif p == r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION} and suspend {var} for up to {var} milliseconds, performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost.  {var} can notify either because the timeout expired or because it was notified explicitly by another agent calling NotifyWaiter({var}, {var}), and not for any other reasons at all.":
        [noi, w_var, t_var, *blah] = children
        env0.assert_expr_is_of_type(noi, T_not_returned)
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(t_var, T_Number)
        result = env0

    elif p in [
        r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}.",
        r"{SMALL_COMMAND} : perform {PP_NAMED_OPERATION_INVOCATION}",
        r"{COMMAND} : Call {PREFIX_PAREN}.",
    ]:
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded=True)
        if noi_t.is_a_subtype_of_or_equal_to(T_not_returned | T_Undefined | T_empty_):
            pass
        else:
            if 0:
                # disable because it's noisy for no benefit?
                add_pass_error(
                    anode,
                    "`Perform/Call` discards `%s` value"
                    % str(noi_t)
                )
        result = env1

    elif p == r"{COMMAND} : Add the characters in set {var} to set {var}.":
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_CharSet)
        env0.assert_expr_is_of_type(var2, T_CharSet)
        result = env0

    elif p == r"{SMALL_COMMAND} : create an own {PROPERTY_KIND} property named {var} of object {var} whose {DSBN}, {DSBN}, {DSBN}, and {DSBN} attribute values are described by {var}. If the value of an attribute field of {var} is absent, the attribute of the newly created property is set to its {h_emu_xref}":
        [kind, name_var, obj_var, *dsbn_, desc_var, desc_var2, emu_xref] = children
        assert desc_var.children == desc_var2.children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        result = env0

    elif p == r"{SMALL_COMMAND} : no further validation is required":
        [] = children
        result = env0

    elif p == r"{SMALL_COMMAND} : convert the property named {var} of object {var} from an? {PROPERTY_KIND} property to an? {PROPERTY_KIND} property. Preserve the existing values of the converted property's {DSBN} and {DSBN} attributes and set the rest of the property's attributes to their {h_emu_xref}":
        [name_var, obj_var, kind1, kind2, dsbn1, dsbn2, emu_xref] = children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : set the corresponding attribute of the property named {var} of object {var} to the value of the field":
        [name_var, obj_var] = children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p in [
        r"{COMMAND} : ReturnIfAbrupt({EX}).",
        r"{SMALL_COMMAND} : ReturnIfAbrupt({var})",
    ]:
        [ex] = children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        if ex_t == T_TBD:
            # Doesn't make sense to compare_types
            # And a proc_add_return(..., T_TBD) wouldn't help
            result = env1
        else:
            (normal_part_of_ex_t, abnormal_part_of_ex_t) = ex_t.split_by(T_Normal)
            if normal_part_of_ex_t == T_0:
                add_pass_error(
                    anode,
                    "ST of `%s` is `%s`, so could just Return, rather than ReturnIfAbrupt"
                    % (ex.source_text(), ex_t)
                )
            if abnormal_part_of_ex_t == T_0:
                add_pass_error(
                    anode,
                    "STA indicates that calling RIA is unnecessary, because `%s` can't be abrupt"
                    % ex.source_text()
                )

            proc_add_return(env1, abnormal_part_of_ex_t, anode)
            result = env1.with_expr_type_narrowed(ex, normal_part_of_ex_t)

    elif p == r"{COMMAND} : IfAbruptRejectPromise({var}, {var}).":
        [vara, varb] = children
        env0.assert_expr_is_of_type(varb, T_PromiseCapability_Record)
        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0

        env0.assert_expr_is_of_type(vara, T_Normal | T_Abrupt)
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_Normal)

        proc_add_return(env0, T_Promise_object_, anode)
        result = env0.with_expr_type_narrowed(vara, normal_part_of_ta)

    elif p == r"{COMMAND} : Set {var}'s essential internal methods except for {DSBN} to the default ordinary object definitions specified in {h_emu_xref}.":
        [var, dsbn, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

#    elif p == r"{COMMAND} : Need to defer setting the {DSBN} attribute to {LITERAL} in case any elements cannot be deleted.":
#        [dsbn, literal] = children
#        result = env0
# ^ obsoleted by PR 1924

    elif p == r"{COMMAND} : {h_emu_not_ref_Record} that the binding for {var} in {var} has been initialized.":
        [_, key_var, oer_var] = children
        env0.assert_expr_is_of_type(key_var, T_String)
        env0.assert_expr_is_of_type(oer_var, T_Environment_Record)
        result = env0

    elif p in [
        r"{COMMAND} : Create an immutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding is a strict binding.",
        r"{COMMAND} : Create a mutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding may be deleted by a subsequent DeleteBinding call.",
    ]:
        [er_var, n_var, s_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        result = env0

    elif p == r"{COMMAND} : Set the remainder of {var}'s essential internal methods to the default ordinary object definitions specified in {h_emu_xref}.":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{COMMAND} : Remove the binding for {var} from {var}.":
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        result = env0

    elif p == r"{SMALL_COMMAND} : remove that element from the {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Remove the own property with name {var} from {var}.":
        [name_var, obj_var] = children
        env0.assert_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : change its bound value to {var}":
        # once, in SetMutableBinding
        # elliptical
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        result = env0

    elif p == r"{COMMAND} : Perform an implementation-defined debugging action.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Put {var} into {var} at index {EX}.":
        [item_var, list_var, index_ex] = children
        list_type = env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        env0.assert_expr_is_of_type(index_ex, T_Integer_)
        result = env0

    elif p in [
        r"{COMMAND} : Remove all occurrences of {var} from {var}.",
        r"{COMMAND} : Remove {var} from {var}.",
        r"{COMMAND} : Remove {var} from {DOTTING}.",
    ]:
        [item_var, list_ex] = children
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        result = env0

    elif p == r"{IF_CLOSED} : If any static semantics errors are detected for {var} or {var}, throw a {ERROR_TYPE} exception. If {CONDITION}, the Early Error rules for {h_emu_grammar} are applied.":
        [avar, bvar, error_type1, cond, emu_grammar] = children
        env0.assert_expr_is_of_type(avar, T_Parse_Node)
        env0.assert_expr_is_of_type(bvar, T_Parse_Node)
        error_type_name1 = error_type1.source_text()[1:-1]
        proc_add_return(env0, ThrowType(NamedType(error_type_name1)), error_type1)
        (t_env, f_env) = tc_cond(cond, env0); assert t_env.equals(env0); assert f_env.equals(env0)
        result = env0

    elif p == r"{COMMAND} : Order the elements of {var} so they are in the same relative order as would be produced by the Iterator that would be returned if the EnumerateObjectProperties internal method were invoked with {var}.":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(bvar, T_Object)
        result = env0

    elif p == r"{COMMAND} : Set fields of {var} with the values listed in {h_emu_xref}. {the_field_names_are_the_names_listed_etc}":
        [var, emu_xref, _] = children
        env0.assert_expr_is_of_type(var, T_Intrinsics_Record)
        result = env0

    elif p == r"{COMMAND} : Add 1 to {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        result = env0

    elif p == r"{COMMAND} : Remove the last element of {SETTABLE}.":
        [settable] = children
        env0.assert_expr_is_of_type(settable, T_List)
        result = env0

    elif p == r"{COMMAND} : Remove this element from {var}.":
        # todo: less ellipsis
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Search the enclosing {nonterminal} for an instance of a {nonterminal} for a {nonterminal} which has a StringValue equal to the StringValue of the {nonterminal} contained in {PROD_REF}.":
        [nont1, nont2, nont3, nont4, prod_ref] = children
        result = env0

    elif p == r"{COMMAND} : Create any host-defined global object properties on {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

#    elif p == r"{COMMAND} : In an implementation-dependent manner, obtain the ECMAScript source texts (see clause {h_emu_xref}) and any associated host-defined values for zero or more ECMAScript scripts and/or ECMAScript modules. For each such {var} and {var}, do{IND_COMMANDS}":
#        [emu_xref, avar, bvar, commands] = children
#        env_for_commands = (
#            env0
#            .plus_new_entry(avar, T_Unicode_code_points_)
#            .plus_new_entry(bvar, T_host_defined_)
#        )
#        result = tc_nonvalue(commands, env_for_commands)
# ^ obsoleted by PR 1597

    # -----

    elif p == r"{COMMAND} : Add {var} to the end of the list of waiters in {var}.":
        [w, wl] = children
        env0.assert_expr_is_of_type(w, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        result = env0

    elif p == r"{COMMAND} : Remove {var} from the list of waiters in {var}.":
        [sig, wl] = children
        env0.assert_expr_is_of_type(sig, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        result = env0

    elif p == r"{COMMAND} : Add {var} to the end of {var}.":
        [el, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(el, list_var)
        result = env1

    elif p == r"{COMMAND} : Subtract {NUM_LITERAL} from {var}.":
        [lit, var] = children
        env0.assert_expr_is_of_type(lit, T_Integer_)
        env0.assert_expr_is_of_type(var, T_Integer_)
        result = env0

    elif p == r"{COMMAND} : Notify the agent {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_agent_signifier_)
        result = env0

    elif p == r"{COMMAND} : Replace the element of {SETTABLE} whose value is {var} with an element whose value is {LITERAL}.":
        [list_var, elem_ex, lit] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(elem_ex, list_var)
        env2 = env1.ensure_A_can_be_element_of_list_B(lit, list_var)
        result = env2

    elif p == r"{COMMAND} : Append the elements of {PP_NAMED_OPERATION_INVOCATION} to the end of {var}.":
        [noi, var] = children
        # over-specific, but it only occurs once, in String.fromCodePoint:
        env0.assert_expr_is_of_type(noi, ListType(T_code_unit_))
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_code_unit_))
        result = env1

    elif p == r"{SMALL_COMMAND} : remove the first code unit from {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    elif p == r"{COMMAND} : Remove the first two code units from {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

#    elif p == r"{COMMAND} : Let `compareExchange` denote a semantic function of two List of byte values arguments that returns the second argument if the first argument is element-wise equal to {var}.":
#        [var] = children
#        env0.assert_expr_is_of_type(var, ListType(T_Integer_))
#        result = env0
# ^ obsoleted by PR 1907

    elif p == r"{COMMAND} : Remove {var} from the front of {var}.":
        [el_var, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(el_var, list_var)
        result = env1

    elif p == r"{SMALL_COMMAND} : in left to right order, starting with the second argument, append each argument as the last element of {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Tangible_))
        result = env1

    elif p == r"{COMMAND} : Append in order the code unit elements of {var} to the end of {var}.":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_String)
        env1 = env0.ensure_expr_is_of_type(b, ListType(T_code_unit_))
        result = env1

    elif p == r"{COMMAND} : Append in list order the elements of {var} to the end of the List {var}.":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_List)
        env0.assert_expr_is_of_type(b, T_List)
        result = env0

    elif p == r"{COMMAND} : Append {EX} and {EX} to {var}.":
        [pvar, svar, list_var] = children

        # only one occurrence, in RegExp.prototype [ @@replace ]
        assert list_var.source_text() == '_replacerArgs_'

        (list_type, list_env) = tc_expr(list_var, env0); assert list_env is env0
        assert list_type == ListType(T_String)
        # because it was created via: Let _replacerArgs_ be &laquo; _matched_ &raquo;.

        # so this is fine:
        env0.assert_expr_is_of_type(svar, T_String)
        # but this is not:
        env0.assert_expr_is_of_type(pvar, T_Integer_)

        # so generalize the list type:
        result = env0.with_expr_type_replaced(list_var, ListType(T_Tangible_))

    elif p == r"{COMMAND} : No action is required.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : The code points `/` or any {nonterminal} occurring in the pattern shall be escaped in {var} as necessary to ensure that the string-concatenation of {EX}, {EX}, {EX}, and {EX} can be parsed (in an appropriate lexical context) as a {nonterminal} that behaves identically to the constructed regular expression. For example, if {var} is {STR_LITERAL}, then {var} could be {STR_LITERAL} or {STR_LITERAL}, among other possibilities, but not {STR_LITERAL}, because `///` followed by {var} would be parsed as a {nonterminal} rather than a {nonterminal}. If {var} is the empty String, this specification can be met by letting {var} be {STR_LITERAL}.":
        # XXX
        result = env0

    elif p == r"{SMALL_COMMAND} : append {code_unit_lit} as the last code unit of {var}":
        [cu_lit, var] = children
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    # explicit-exotics:
    elif p == r"{SMALL_COMMAND} : append each of its elements to {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Set {var}'s essential internal methods, except for {DSBN} and {DSBN}, to the definitions specified in {h_emu_xref}.":
        var = children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : initialize the corresponding internal slot value on {var} to {LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{COMMAND} : Choose any such {var}.":
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_FinalizationRegistryCellRecord_)

    # elif p == r"{COMMAND} : Append {EX} and {EX} as the last two elements of {var}.":
    # elif p == r"{COMMAND} : For all {var}, {var}, and {var} in {var}'s domain:{IND_COMMANDS}":
    # elif p == r"{COMMAND} : For each {EACH_THING}, if {CONDITION}, then {SMALL_COMMAND}.":
    # elif p == r"{COMMAND} : Let {SAB_RELATION} be {EX}.":
    # elif p == r"{COMMAND} : Let {var} be {EXPR}. If {CONDITION}, {var} will be the execution context that performed the direct eval. If {CONDITION}, {var} will be the execution context for the invocation of the `eval` function.":
    # elif p == r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. If there are multiple possibilities for {var}, choose the value of {var} for which {PRODUCT} is closest in value to {var}. If there are two such possible values of {var}, choose the one that is even.":
    # elif p == r"{COMMAND} : Order the elements of {var} so they are in the same relative order as would be produced by the Iterator that would be returned if the EnumerateObjectProperties internal method was invoked with {var}.":
    # elif p == r"{COMMAND} : Perform an implementation-dependent sequence of calls to the {DSBN} and {DSBN} internal methods of {var}, to the DeletePropertyOrThrow and HasOwnProperty abstract operation with {var} as the first argument, and to SortCompare (described below), such that:{I_BULLETS}":
    # elif p == r"{COMMAND} : Repeat, while {var} is less than the total number of elements of {var}. The number of elements must be redetermined each time this method is evaluated.{IND_COMMANDS}":
    # elif p == r"{COMMAND} : Return {LITERAL},? if {CONDITION}.":
    # elif p == r"{COMMAND} : Return {LITERAL},? if {CONDITION}. Otherwise, return {LITERAL}.":
    # elif p == r"{COMMAND} : Return {var} as the Completion Record of this abstract operation.":
    # elif p == r"{COMMAND} : When the {nonterminal} {var} is evaluated, perform the following steps in place of the {nonterminal} Evaluation algorithm provided in {h_emu_xref}:{IND_COMMANDS}":
    # elif p == r"{COMMAND} : While {CONDITION} repeat,{IND_COMMANDS}":
    # elif p == r"{COMMAND} : While {CONDITION},{IND_COMMANDS}":
    # elif p == r"{COMMAND} : {CONDITION_AS_COMMAND}":
    # elif p == r"{SMALL_COMMAND} : append to {var} the elements of {NAMED_OPERATION_INVOCATION}":
    # elif p == r"{SMALL_COMMAND} : let {var}, {var}, and {var} be integers such that {CONDITION}. If there are multiple possibilities for {var}, choose the value of {var} for which {PRODUCT} is closest in value to {var}. If there are two such possible values of {var}, choose the one that is even. Note that {var} is the number of digits in the decimal representation of {var} and that {var} is not divisible by 10":
    # elif p == r"{SMALL_COMMAND} : pass its value as the {var} optional argument of FunctionCreate":
    # elif p == r"{SMALL_COMMAND} : replace {var} in {var} with that equivalent code point(s)":
    # elif p == r"{SMALL_COMMAND} : throw a {ERROR_TYPE} or a {ERROR_TYPE} exception, depending on the type of the error":
    # elif p == r"{SMALL_COMMAND} : {CONDITION_AS_SMALL_COMMAND}":

    else:
        stderr()
        stderr("tc_nonvalue:")
        stderr('    elif p == %s:' % escape(p))
        sys.exit(0)

    assert result is None or isinstance(result, Env)

    if trace_this_op:
        print()
        print("Leaving nv:", trace_line)
        mytrace(result)

    return result

# ------------------------------------------------------------------------------


def tc_cond(cond, env0, asserting=False):
    # returns a tuple of two envs, one for true and one for false

    p = str(cond.prod)

    if trace_this_op:
        print()
        print("Entering c:", p)
        print("           ", cond.source_text())
        mytrace(env0)

    result = tc_cond_(cond, env0, asserting)

    if trace_this_op:
        print()
        print("Leaving c:", p)
        print("          ", cond.source_text())
        mytrace(result[0])

    return result

def tc_cond_(cond, env0, asserting):
    p = str(cond.prod)
    children = cond.children

    #----------------
    # simple unit production

    if p in [
        r'{CONDITION} : {CONDITION_1}',
        r'{CONDITION_1} : {TYPE_TEST}',
        r'{CONDITION_1} : {NUM_COMPARISON}',
    ]:
        [child] = children
        return tc_cond(child, env0, asserting)

    # -------------
    # combining conditions

    elif p in [
        r"{CONDITION} : Either {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : either {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or if {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, or {CONDITION_1}, or {CONDITION_1}",
    ]:
        logical = ('or', children)
        return tc_logical(logical, env0, asserting)

    elif p in [
        r"{CONDITION} : {CONDITION_1} and if {CONDITION_1}",
        r'{CONDITION} : {CONDITION_1} and {CONDITION_1}',
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1} and {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}",
        r'{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}',
    ]:
        logical = ('and', children)
        return tc_logical(logical, env0, asserting)

    elif p in [
        # r"{CONDITION} : {CONDITION_1} or {CONDITION_1} and {CONDITION_1}", # obsoleted by PR 2111
        r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}",
    ]:
        [conda, condb, condc] = children
        logical = (
            'or',
            [
                conda,
                ('and', [condb, condc])
            ]
        )
        return tc_logical(logical, env0, asserting)

    # elif p == r"{CONDITION} : {CONDITION_1}, when {CONDITION_1}":

    elif p in [
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1} or {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or {CONDITION_1} and {CONDITION_1}",
    ]:
        [a, b, c, d] = children    
        logical = (
            'or',
            [
                ('and', [a, b]),
                ('and', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

    elif p == r"{CONDITION} : ({NUM_COMPARISON} or {NUM_COMPARISON}) and ({NUM_COMPARISON} or {NUM_COMPARISON})":
        [a, b, c, d] = children
        logical = (
            'and',
            [
                ('or', [a, b]),
                ('or', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

    # ---------------
    # Type-conditions

    elif p in [
        r'{TYPE_TEST} : Type({TYPE_ARG}) is {TYPE_NAME}',
        r'{TYPE_TEST} : Type({TYPE_ARG}) is not {TYPE_NAME}',
    ]:
        [type_arg, type_name] = children
        t = type_for_TYPE_NAME(type_name)
        copula = 'is a' if ' is {' in p else 'isnt a'
        return env0.with_type_test(type_arg, copula, t, asserting)

    elif p in [
        r"{TYPE_TEST} : Type({TYPE_ARG}) is either {TYPE_NAME} or {TYPE_NAME}",
        r"{TYPE_TEST} : Type({TYPE_ARG}) is either {TYPE_NAME}, {TYPE_NAME}, or {TYPE_NAME}",
        r"{TYPE_TEST} : Type({TYPE_ARG}) is either {TYPE_NAME}, {TYPE_NAME}, {TYPE_NAME}, or {TYPE_NAME}",
        r"{TYPE_TEST} : Type({TYPE_ARG}) is neither {TYPE_NAME} nor {TYPE_NAME}",
        r"{TYPE_TEST} : Type({TYPE_ARG}) is {TYPE_NAME}, {TYPE_NAME}, {TYPE_NAME}, or {TYPE_NAME}",
        r"{TYPE_TEST} : Type({TYPE_ARG}) is {TYPE_NAME}, {TYPE_NAME}, {TYPE_NAME}, {TYPE_NAME}, or {TYPE_NAME}",
        r'{TYPE_TEST} : Type({TYPE_ARG}) is {TYPE_NAME} or {TYPE_NAME}',
    ]:
        [type_arg, *type_name_] = children
        t = union_of_types([
            type_for_TYPE_NAME(tn)
            for tn in type_name_
        ])
        copula = 'isnt a' if 'neither' in p else 'is a'
        return env0.with_type_test(type_arg, copula, t, asserting)

    elif p == r"{TYPE_TEST} : Type({TYPE_ARG}) is an ECMAScript language type":
        [type_arg] = children
        return env0.with_type_test(type_arg, 'is a', T_Tangible_, asserting)

    elif p in [
        r'{TYPE_TEST} : Type({TYPE_ARG}) is Object and it has an {DSBN} internal slot',
        r'{TYPE_TEST} : Type({TYPE_ARG}) is Object and it has {DSBN}, {DSBN}, and {DSBN} internal slots',
    ]:
        [type_arg, *dsbn_] = children
        return env0.with_type_test(type_arg, 'is a', T_Object, asserting)
        # XXX ignore the part about the internal slot(s)?

    elif p == r"{TYPE_TEST} : Type({TYPE_ARG}) is not Number or BigInt":
        [type_arg] = children
        return env0.with_type_test(type_arg, 'isnt a', T_Number | T_BigInt, asserting)

    elif p == r"{TYPE_TEST} : Type({TYPE_ARG}) is Object and is either a built-in function object or has an {DSBN} internal slot":
        [type_arg, dsbn] = children
        assert dsbn.source_text() == '[[ECMAScriptCode]]'
        return env0.with_type_test(type_arg, 'is a', T_function_object_, asserting)

    elif p == r"{CONDITION_1} : {var} is an Object that has {DSBN}, {DSBN}, {DSBN}, {DSBN}, and {DSBN} internal slots":
        [var, *dsbn_] = children
        assert (
            [dsbn.source_text() for dsbn in dsbn_]
            ==
            ['[[ViewedArrayBuffer]]', '[[ArrayLength]]', '[[ByteOffset]]', '[[ContentType]]', '[[TypedArrayName]]']
        )
        return env0.with_type_test(var, 'is a', T_Integer_Indexed_object_, asserting)
        # could be more specific?

    elif p == r"{CONDITION_1} : {var} is an Object that has {DSBN} and {DSBN} internal slots":
        [var, *dsbn_] = children
        assert (
            [dsbn.source_text() for dsbn in dsbn_]
            ==
            [ '[[TypedArrayName]]', '[[ContentType]]' ]
        )
        return env0.with_type_test(var, 'is a', T_Integer_Indexed_object_, asserting)

    elif p == r"{CONDITION_1} : {var} has an? {DSBN} or {DSBN} internal slot":
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        assert dsbna.source_text() == '[[StringData]]'
        assert dsbnb.source_text() == '[[NumberData]]'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has {DSBN} and {DSBN} internal slots":
        # XXX could be a type-test
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have either a {DSBN} or an {DSBN} internal slot":
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p in [
        r'{TYPE_TEST} : Type({TYPE_ARG}) is the same as Type({TYPE_ARG})',
        r'{TYPE_TEST} : Type({TYPE_ARG}) is different from Type({TYPE_ARG})',
    ]:
        # Env can't represent the effect of these.
        # If the incoming static types were different,
        # the 'true' env could at least narrow those to their intersection,
        # but the form only appears twice, and in both cases the static types are the same.
        return (env0, env0)

    # ---

    elif p in [
        r"{CONDITION_1} : {LOCAL_REF} is an? {nonterminal} or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is an? {nonterminal}, an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {nonterminal} or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {nonterminal}, an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is neither an? {nonterminal} nor an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is neither an? {nonterminal} nor an? {nonterminal} nor an? {nonterminal}",
    ]:
        [local_ref, *nont_] = children
        types = []
        for nonterminal in nont_:
            types.append(ptn_type_for(nonterminal))
        target_t = union_of_types(types)
        copula = 'isnt a' if 'neither' in p else 'is a'
        return env0.with_type_test(local_ref, copula, target_t, asserting)
        # XXX at least some of these are using
        # a more complicated meaning for "is a".

    elif p == r'{CONDITION_1} : {var} is not a {nonterminal}':
        [var, nonterminal] = children
        target_t = ptn_type_for(nonterminal)
        return env0.with_type_test(var, 'isnt a', target_t, asserting)

    elif p == r'{CONDITION_1} : {EX} and {EX} are distinct {TYPE_NAME} or {TYPE_NAME} values':
        # XXX This means that either they're both one, or else they're both the other,
        # but I can't handle co-ordinated types like that.
        # LATER: Actually, that doesn't appear to be what it means.
        [exa, exb, tnc, tnd] = children
        t = type_for_TYPE_NAME(tnc) | type_for_TYPE_NAME(tnd)
        (a_t_env, a_f_env) = env0.with_type_test(exa, 'is a', t, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(exb, 'is a', t, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    # ---

    elif p == r"{CONDITION_1} : {var} is an abrupt completion":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Abrupt, asserting)

    elif p in [
        r"{CONDITION_1} : {var} is never an abrupt completion",
        r"{CONDITION_1} : {var} is not an abrupt completion",
    ]:
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Abrupt, asserting)

    elif p == r"{CONDITION_1} : {var} is not an abrupt completion because of validation preceding step {h_emu_xref}":
        [var, _] = children
        return env0.with_type_test(var, 'isnt a', T_Abrupt, asserting)

    elif p == r"{CONDITION_1} : {var} is either a set of algorithm steps or other definition of a function's behaviour provided in this specification":
        [var] = children
        return env0.with_type_test(var, 'is a', T_alg_steps, asserting)

    # PR 2109:
    elif p == r"{CONDITION_1} : {var} is either an Abstract Closure, a set of algorithm steps, or some other definition of a function's behaviour provided in this specification":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Abstract_Closure | T_alg_steps, asserting)

    # PR 2109:
    elif p == r"{CONDITION_1} : {var} is an Abstract Closure":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Abstract_Closure, asserting)

    elif p == r'{CONDITION_1} : {var} is an Array exotic object':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Array_object_, asserting)

    elif p == r'{CONDITION_1} : {var} is an AsyncGeneratorRequest record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_AsyncGeneratorRequest_Record, asserting)

    elif p == r'{CONDITION_1} : Type({EXPR}) is Boolean, String, Symbol, or Number':
        [expr] = children
        return env0.with_type_test(expr, 'is a', T_Boolean | T_String | T_Symbol | T_Number, asserting)

#    elif p == r'{CONDITION_1} : {var} is a Bound Function exotic object':
#        [var] = children
#        return env0.with_type_test(var, 'is a', T_bound_function_exotic_object_, asserting)
# ^ obsoleted by PR 1460

    elif p == r'{CONDITION_1} : {var} is a UTF-16 code unit':
        [var] = children
        return env0.with_type_test(var, 'is a', T_code_unit_, asserting)

    # PR 1668:
    elif p == r"{CONDITION_1} : {var} is a ClassFieldDefinition Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_ClassFieldDefinition_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a constructor function":
        [var] = children
        return env0.with_type_test(var, 'is a', T_constructor_object_, asserting)

    elif p == r"{CONDITION_1} : {var} is a Continuation":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Continuation, asserting)

    elif p == r"{CONDITION_1} : {var} is a Cyclic Module Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Cyclic_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is not a Cyclic Module Record":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Cyclic_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a Completion Record":
        # In a sense, this is a vacuous condition,
        # because any? value can be coerced into a Completion Record.
        [var] = children
        return env0.with_type_test(var, 'is a', T_Tangible_ | T_empty_ | T_Abrupt, asserting)

    elif p == r'{CONDITION_1} : {var} is a Data Block':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {var} is the execution context of a generator':
        [var] = children
        return env0.with_type_test(var, 'is a', T_execution_context, asserting)

    elif p == r'{CONDITION_1} : {var} is a callable object':
        [var] = children
        return env0.with_type_test(var, 'is a', T_function_object_, asserting)

    elif p in [
        r"{CONDITION_1} : {var} is an Environment Record",
        # r"{CONDITION_1} : {var} must be an Environment Record",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Environment_Record, asserting)

    elif p in [
        r"{CONDITION_1} : {var} is an? {ENVIRONMENT_RECORD_KIND} Environment Record",
        r"{CONDITION_1} : {var} is not an? {ENVIRONMENT_RECORD_KIND} Environment Record",
    ]:
        [var, kind] = children
        copula = 'isnt a' if 'not' in p else 'is a'
        return env0.with_type_test(var, copula, type_for_environment_record_kind(kind), asserting)

    elif p in [
        r'{CONDITION_1} : {var} is an ECMAScript function',
        r'{CONDITION_1} : {var} is an ECMAScript function object',
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_function_object_, asserting)

    elif p == r'{CONDITION_1} : {var}, {var}, and {var} are integer values &ge; 0':
        [vara, varb, varc] = children
        (a_t_env, a_f_env) = env0.with_type_test(vara, 'is a', T_Integer_, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(varb, 'is a', T_Integer_, asserting)
        (c_t_env, c_f_env) = env0.with_type_test(varc, 'is a', T_Integer_, asserting)
        return (
            envs_and([a_t_env, b_t_env, c_t_env]),
            envs_or([a_f_env, b_f_env, c_f_env])
        )

    elif p == r"{CONDITION_1} : {var} is an Integer-Indexed exotic object":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Integer_Indexed_object_, asserting)

    elif p == r"{CONDITION_1} : {var} is a List":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', T_List, asserting)

    elif p == r"{CONDITION_1} : {var} is a List whose elements are all ECMAScript language values":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_Tangible_), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of code points":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_code_point_), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of code units":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_code_unit_), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of internal slot names":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_SlotName_), asserting)

    elif p == r'{CONDITION_1} : {var} is a List of String values':
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_String), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of property keys":
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_String | T_Symbol), asserting)

    elif p == r'{CONDITION_1} : {var} is a List of errors':
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_SyntaxError | T_ReferenceError), asserting)

#    elif p == r'{CONDITION_1} : {var} is a List that has the same number of elements as the number of parameters required by {var}':
#        [list_var, proc_var] = children
#        env0.assert_expr_is_of_type(proc_var, T_proc_)
#        return env0.with_type_test(list_var, 'is a', T_List, asserting)
# ^ obsoleted by PR 1597

    elif p == r'{CONDITION_1} : {var} is a List of WriteSharedMemory or ReadModifyWriteSharedMemory events with length equal to {EX}':
        [var, ex] = children
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return env0.with_type_test(var, 'is a', ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of Source Text Module Records":
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_Source_Text_Module_Record), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of Record { {DSBN}, {DSBN} }":
        [var, dsbn1, dsbn2] = children
        assert dsbn1.source_text() == '[[Module]]'
        assert dsbn2.source_text() == '[[ExportName]]'
        return env0.with_type_test(var, 'is a', ListType(T_ExportResolveSet_Record_), asserting)

    elif p == r"{CONDITION_1} : {var} is a non-empty List of {ERROR_TYPE} objects":
        [var, error_type] = children
        error_type_name = error_type.source_text()[1:-1]
        return env0.with_type_test(var, 'is a', ListType(NamedType(error_type_name)), asserting)

    elif p == r"{CONDITION_1} : {var} is a List containing only String and Symbol values":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_String | T_Symbol))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a possibly empty List of Strings":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_String))
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} is an empty List",
        r"{CONDITION_1} : {var} is now an empty List",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a List of Unicode code points that is identical to a List of Unicode code points that is a Unicode {h_emu_not_ref_property_name} or property alias listed in the &ldquo;{h_emu_not_ref_Property_name} and aliases&rdquo; column of {h_emu_xref} or {h_emu_xref}":
        [v, _, _, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not an empty List":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List | T_WaiterList)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is a sequence of Unicode code points":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Unicode_code_points_)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {var} is a Module Record',
        r"{CONDITION_1} : {var} is an instance of a concrete subclass of Module Record",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Module_Record, asserting)

#    elif p in [
#        r"{CONDITION_1} : {var} is present as a parameter",
#    ]:
#        [var] = children
#        return env0.with_type_test(var, 'isnt a', T_not_passed, asserting)
# ^ obsoleted by PR 1965

    elif p in [
        r'{CONDITION_1} : {EX} is present',
        r'{CONDITION_1} : {EX} is not present',
    ]:
        [ex] = children
        if ex.is_a('{DOTTING}'):
            t = T_not_in_record
        elif ex.is_a('{PROD_REF}'):
            t = T_not_in_node
        elif ex.is_a('{var}'):
            # todo: get rid of this usage. (roll eyes at PR #953)
            t = T_not_passed # assuming it's a parameter
        else:
            assert 0, ex.source_text()
        copula = 'is a' if 'not present' in p else 'isnt a'
        return env0.with_type_test(ex, copula, t, asserting)

    elif p == r"{CONDITION_1} : {EX} is absent":
        # todo: eliminate?
        [ex] = children
        assert ex.is_a('{DOTTING}')
        return env0.with_type_test(ex, 'is a', T_not_in_record, asserting)

# PR 1567 obsoleted:
#    elif p == r'{CONDITION_1} : {var} is an integer value &ge; 0':
#        [var] = children
#        return env0.with_type_test(var, 'is a', T_Integer_, asserting)
#
#    elif p == r"{CONDITION_1} : {var} is an integer Number &ge; 0":
#        [var] = children
#        return env0.with_type_test(var, 'is a', T_Integer_, asserting)
#
#    elif p == r"{CONDITION_1} : {var} is an integer Number, {NUM_LITERAL}, or {NUM_LITERAL}":
#        [var, lita, litb] = children
#        return env0.with_type_test(var, 'is a', T_Integer_, asserting)

    elif p in [
        r'{CONDITION_1} : {EXPR} is an object',
        r"{CONDITION_1} : {EX} is an Object",
    ]:
        [expr] = children
        return env0.with_type_test(expr, 'is a', T_Object, asserting)

    elif p == r"{CONDITION_1} : {var} is a Parse Node":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Parse_Node, asserting)

    elif p == r"{CONDITION_1} : {var} is a Parse Node for {nonterminal}":
        [var, nont] = children
        return env0.with_type_test(var, 'is a', ptn_type_for(nont), asserting)

#    elif p == r'{CONDITION_1} : {var} is the name of a Job':
#        [var] = children
#        return env0.with_type_test(var, 'is a', T_proc_, asserting)
# ^ obsoleted by PR 1597

    # PR 1668 privates:
    elif p == r"{CONDITION_1} : {EX} is a Private Name":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Private_Name, asserting)

    elif p == r"{CONDITION_1} : {var} is a PromiseCapability Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_PromiseCapability_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a PromiseReaction Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_PromiseReaction_Record, asserting)

    elif p == r'{CONDITION_1} : {var} is an? {PROPERTY_KIND} property':
        [var, kind] = children
        t = {
            'accessor': T_accessor_property_,
            'data'    : T_data_property_,
        }[kind.source_text()]
        return env0.with_type_test(var, 'is a', t, asserting)

    elif p in [
        r'{CONDITION_1} : {var} is a Property Descriptor',
        # r"{CONDITION_1} : {var} must be an accessor Property Descriptor",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Property_Descriptor, asserting)

    elif p in [
        r'{CONDITION_1} : {var} is a Proxy exotic object',
        r"{CONDITION_1} : {var} is a Proxy object",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Proxy_exotic_object_, asserting)

    elif p == r'{CONDITION_1} : {var} is a ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_ReadModifyWriteSharedMemory_event, asserting)

    elif p == r'{CONDITION_1} : {var} is a ReadSharedMemory or ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)

    elif p == r'{CONDITION_1} : {var} is a Realm Record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Realm_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a ResolvedBinding Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_ResolvedBinding_Record, asserting)

    elif p == r'{CONDITION_1} : {var} is a Shared Data Block':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Shared_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {var} is not a Shared Data Block':
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Shared_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {var} is a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Shared_Data_Block_event, asserting)

    elif p == r"{CONDITION_1} : {var} is a Source Text Module Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Source_Text_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is not a Source Text Module Record":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Source_Text_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a State":
        [var] = children
        return env0.with_type_test(var, 'is a', T_State, asserting)

    elif p in [
        r'{CONDITION_1} : {EX} is a String value',
        # r"{CONDITION_1} : {var} is a String", # obsoleted by PR #1923
    ]:
        [ex] = children
        if ex.prod.lhs_s == '{var}':
            return env0.with_type_test(ex, 'is a', T_String, asserting)
        elif (
            ex.prod.rhs_s == '{LOCAL_REF}'
            and
            ex.children[0].prod.rhs_s == '{SETTABLE}'
            and
            ex.children[0].children[0].prod.rhs_s == '{var}'
        ):
            [var] = ex.children[0].children[0].children
            return env0.with_type_test(var, 'is a', T_String, asserting)
        elif (
            ex.prod.rhs_s == '{LOCAL_REF}'
            and
            ex.children[0].prod.rhs_s == '{SETTABLE}'
            and
            ex.children[0].children[0].prod.rhs_s == '{DOTTING}'
        ):
            [dotting] = ex.children[0].children[0].children
            # XXX
            return (env0, env0)
        else:
            assert 0

    elif p == r"{CONDITION_1} : both {var} and {var} are Strings":
        [a_var, b_var] = children
        (at_env, af_env) = env0.with_type_test(a_var, 'is a', T_String, asserting)
        (bt_env, bf_env) = env0.with_type_test(b_var, 'is a', T_String, asserting)
        return (
            env_and(at_env, bt_env),
            env_or(af_env, bf_env)
        )

    elif p == r"{TYPE_TEST} : Both Type({TYPE_ARG}) and Type({TYPE_ARG}) is {TYPE_NAME}":
        [type_arga, type_argb, type_name] = children
        t = type_for_TYPE_NAME(type_name)
        (a_t_env, a_f_env) = env0.with_type_test(type_arga, 'is a', t, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(type_argb, 'is a', t, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    elif p == r"{TYPE_TEST} : Both Type({var}) and Type({var}) are Number or both are BigInt":
        [vara, varb] = children
        (a_t, env1) = tc_expr(vara, env0); assert env1 is env0
        (b_t, env1) = tc_expr(varb, env0); assert env1 is env0
        # XXX clean this up
        assert asserting
        if (
            a_t == T_Number and b_t == T_Number
            or
            a_t == T_BigInt and b_t == T_BigInt
        ):
            # assertion succeeded
            pass
        else:
            add_pass_error(
                cond,
                "STA can't confirm assertion blah"
            )
        return (env0, env0)

#    elif p == r"{CONDITION_1} : {var} is a String exotic object":
#        [var] = children
#        return env0.with_type_test(var, 'is a', T_String_exotic_object_, asserting)

    elif p == r"{CONDITION_1} : {var} is an ECMAScript language value":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Tangible_, asserting)

#    elif p == r"{CONDITION_1} : {var} will never be *undefined* or an accessor descriptor because Array objects are created with a length data property that cannot be deleted or reconfigured":
#        [var] = children
#        return env0.with_type_test(var, 'isnt a', T_Undefined, asserting)
# ^ obsoleted by PR 1924

    elif p in [
        r"{CONDITION_1} : {var} is a normal completion with a value of {LITERAL}. The possible sources of completion values are Await or, if the async function doesn't await anything, step {h_emu_xref} above",
    ]:
        [var, literal, _] = children
        env0.assert_expr_is_of_type(literal, T_Undefined)
        return env0.with_type_test(var, 'is a', T_Undefined, asserting)

    elif p == r'{CONDITION_1} : {var} is an ECMAScript source text (see clause {h_emu_xref})':
        [var, emu_xref] = children
        return env0.with_type_test(var, 'is a', T_Unicode_code_points_, asserting)

    elif p == r'{CONDITION_1} : {var} is a WriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_WriteSharedMemory_event, asserting)

    elif p ==  r"{CONDITION_1} : {var} is a normal completion":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Normal, asserting)

    elif p == r"{CONDITION_1} : {var} is either a String, Number, Boolean, Null, or an Object that is defined by either an {nonterminal} or an {nonterminal}":
        [var, nonta, nontb] = children
        return env0.with_type_test(var, 'is a', T_String | T_Number | T_Boolean | T_Null | T_Object, asserting)

    elif p == r"{CONDITION_1} : {EX} is a Boolean value":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Boolean, asserting)

    elif p == r"{CONDITION_1} : {EX} is a Number value":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Number, asserting)

    elif p == r"{CONDITION_1} : {EX} is a Symbol value":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Symbol, asserting)

# PR 1692 obsoleted
#    elif p == r"{CONDITION_1} : {var} is a Synchronize event":
#        [v] = children
#        return env0.with_type_test(v, 'is a', T_Synchronize_event, asserting)

    elif p == r"{CONDITION_1} : {var} is a bound function exotic object":
        [var] = children
        return env0.with_type_test(var, 'is a', T_bound_function_exotic_object_, asserting)

    elif p == r"{CONDITION_1} : {var} is a bound function exotic object or a {h_emu_xref}":
        [var, xref] = children
        return env0.with_type_test(var, 'is a', T_function_object_, asserting)

    # ----------------------
    # quasi-type-conditions

    elif p == r"{CONDITION_1} : {var} is a List of a single Number":
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, ListType(T_Number)),
            env0
        )

    elif p == r"{CONDITION_1} : {var} is a {h_emu_xref} or a {h_emu_xref}":
        [var, xrefa, xrefb] = children
        assert xrefa.source_text() in [
            '<emu-xref href="#sec-bound-function-exotic-objects">Bound Function exotic object</emu-xref>',
            '<emu-xref href="#sec-bound-function-exotic-objects">bound function exotic object</emu-xref>', # PR 1460
        ]
        assert xrefb.source_text() == '<emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>'
        return (
            env0.with_expr_type_narrowed(var, T_function_object_),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is hint String",
        r"{CONDITION_1} : {var} is hint Number",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_LangTypeName_)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar} ',
        r"{CONDITION_1} : {var} is an instance of the production {h_emu_grammar}",
    ]:
        [local_ref, emu_grammar] = children
        emu_grammar_text = emu_grammar.source_text()
        lhs = re.sub(r'<emu-grammar>(\w+) :.*', r'\1', emu_grammar_text)
        prodn_type = ptn_type_for(lhs)
        #
        (ref_type, env1) = tc_expr(local_ref, env0); assert env1 is env0
        assert prodn_type.is_a_subtype_of_or_equal_to(ref_type)
        # but whether or not it's an instance of that particular production
        # doesn't narrow its type.
        return (env1.with_expr_type_narrowed(local_ref, prodn_type), env1)

    elif p in [
        r"{CONDITION_1} : {var} is an Object that has a {DSBN} internal slot",
        r'{CONDITION_1} : {var} is an extensible object that does not have a {starred_str} own property',

        # PR 1302 obsoleted:
        # r'{CONDITION_1} : {var} is an extensible object that does not have a {backticked_word} own property',
    ]:
        [var, _] = children
        return (
            env0.with_expr_type_narrowed(var, T_Object),
            env0
        )

    elif p == r"{CONDITION_1} : {var} has a {DSBN} internal slot. If it does not, the definition in {h_emu_xref} applies":
        [var, dsbn, emu_xref] = children
        assert dsbn.source_text() == '[[TypedArrayName]]'
        return (
            env0.with_expr_type_narrowed(var, T_Integer_Indexed_object_),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is an ordinary, extensible object with no non-configurable properties",
        r"{CONDITION_1} : {var} is an extensible ordinary object",
        r"{CONDITION_1} : {var} is an extensible ordinary object with no own properties",
        r"{CONDITION_1} : {var} is an initialized RegExp instance",
        r'{CONDITION_1} : {var} is an Object that implements the <i>IteratorResult</i> interface',
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_Object),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is an integer index",
        r"{CONDITION_1} : {var} is an array index",
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_String),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is not an array index",
        r"{CONDITION_1} : {var} is not an integer index",
    ]:
        [var] = children
        return (
            env0,
            env0.with_expr_type_narrowed(var, T_String)
        )

    elif p in [
        r"{CONDITION_1} : {var} is a {h_emu_xref}",
        r"{CONDITION_1} : {var} is not a {h_emu_xref}",
    ]:
        [var, emu_xref] = children

        # copula = 'isnt a' if 'not' in p else 'is a'

        if emu_xref.source_text() in [
            '<emu-xref href="#leading-surrogate"></emu-xref>',
            '<emu-xref href="#trailing-surrogate"></emu-xref>',
        ]:
            t = T_code_unit_
        elif emu_xref.source_text() == '<emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>':
            t = T_function_object_
        else:
            assert 0

        if 'is a' in p:
            return (
                env0.with_expr_type_narrowed(var, t),
                env0
            )
        else:
            return (
                env0,
                env0.with_expr_type_narrowed(var, t)
            )

    elif p in [
        r"{CONDITION_1} : The value of {SETTABLE} is {LITERAL}",
        r"{CONDITION_1} : {EXPR} is {LITERAL}",
        r"{CONDITION_1} : {EX} has the value {LITERAL}",
        r"{CONDITION_1} : {EX} is not {LITERAL}",
        r"{CONDITION_1} : {EX} is present and has value {LITERAL}",
        r"{CONDITION_1} : {EX} is {LITERAL}",
        r"{CONDITION_1} : {var} is also {LITERAL}",
        r"{CONDITION_1} : {var} is the value {LITERAL}",
        r"{CONDITION_1} : {var} is {LITERAL} because formal parameters mapped by argument objects are always writable",
    ]:
        [ex, literal] = children

        # kludgey?
        r = is_simple_call(ex)
        if r:
            (callee_op_name, var) = r
            #
            if callee_op_name == 'IsSharedArrayBuffer':
                t = T_SharedArrayBuffer_object_
            elif callee_op_name == 'IsPromise':
                t = T_Promise_object_
            elif callee_op_name == 'IsCallable':
                t = T_function_object_
            elif callee_op_name == 'IsConstructor':
                t = T_constructor_object_
            elif callee_op_name == 'IsPropertyKey':
                t = T_String | T_Symbol
            elif callee_op_name == 'IsInteger':
                t = T_Integer_
            elif callee_op_name == 'IsNonNegativeInteger':
                t = T_Integer_
            else:
                t = None
            #
            if t:
                assert 'not' not in p
                if literal.source_text() == '*true*':
                    copula = 'is a'
                elif literal.source_text() == '*false*':
                    copula = 'isnt a'
                else:
                    assert 0
                #
                return env0.with_type_test(var, copula, t, asserting)

        copula = 'isnt a' if 'is not' in p else 'is a'

        # special handling for Completion Records:
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            dsbn_name = dsbn.source_text()[2:-2]
            if dsbn_name != 'Type': break
            t = type_corresponding_to_comptype_literal(literal)
            return env0.with_type_test(lhs, copula, t, asserting)

        # ------------

        (lit_type, lit_env) = tc_expr(literal, env0)
        assert lit_env is env0

        if lit_type in [T_Undefined, T_Null, T_empty_, T_not_in_node, T_match_failure_, T_Infinity_]:
            # i.e., the literal is *undefined* or *null* or ~empty~ or ~[empty]~ or ~failure~ or &infin;
            # Because the type has only one value,
            # a value-comparison is equivalent to a type-comparison.
            return env0.with_type_test(ex, copula, lit_type, asserting)
        elif literal.source_text() == '*"ambiguous"*':
            # The return-type of ResolveExport includes String,
            # but only for the single value "ambiguous".
            # So a test against that value is a type-comparison.
            return env0.with_type_test(ex, copula, lit_type, asserting)
        else:
            # The type has more than one value.
            # So, while the is-case is type-constraining,
            # the isn't-case isn't.
            is_env = env0.with_expr_type_narrowed(ex, lit_type)
            isnt_env = env0

            if copula == 'is a':
                return (is_env, isnt_env)
            else:
                return (isnt_env, is_env)

    elif p in [
        r'{CONDITION_1} : {EX} is {LITERAL} or {LITERAL}',
        r'{CONDITION_1} : {EX} is either {LITERAL} or {LITERAL}',
        # ---
        r"{CONDITION_1} : {EX} is not {LITERAL} or {LITERAL}",
        r"{CONDITION_1} : {EX} is neither {LITERAL} nor {LITERAL}",
        r"{CONDITION_1} : {EX} is present, and is neither {LITERAL} nor {LITERAL}",
        r"{CONDITION_1} : In this case, {var} will never be {LITERAL} or {LITERAL}",
    ]:
        [ex, lita, litb] = children

        # special handling for Completion Records' [[Type]] field
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            dsbn_name = dsbn.source_text()[2:-2]
            if dsbn_name != 'Type': break
            ta = type_corresponding_to_comptype_literal(lita)
            tb = type_corresponding_to_comptype_literal(litb)
            assert 'never' not in p
            assert 'neither' not in p
            return env0.with_type_test(lhs, 'is a', ta | tb, asserting)

        (lita_type, lita_env) = tc_expr(lita, env0); assert lita_env is env0
        (litb_type, litb_env) = tc_expr(litb, env0); assert litb_env is env0

        copula = 'isnt a' if ('never' in p or 'neither' in p or 'not' in p) else 'is a'

        # It's only a type-test if the literals are from very small types.
        if (
            lita_type == T_Null and litb_type == T_Undefined
            or
            lita_type == T_Undefined and litb_type == T_Null
        ):
            return env0.with_type_test(ex, copula, T_Null | T_Undefined, asserting)

        elif lita_type == T_Null and litb_type == T_String and litb.source_text() == '*"ambiguous"*':
            return env0.with_type_test(ex, copula, T_Null | T_String, asserting)

        elif lita_type == litb_type:
            (t, env1) = tc_expr(ex, env0)
            if t == lita_type:
                pass
            else:
                env1 = env1.with_expr_type_replaced(ex, lita_type)
            return (env1, env1)

        elif lita_type == T_Boolean and litb_type == T_Undefined:
            # Evaluation of RelationalExpression: If _r_ is *true* or *undefined*, ...
            env0.assert_expr_is_of_type(ex, T_Boolean | T_Undefined)
            return (env0, env0)

        else:
            assert 0

# 1411 obsoleted:
#    elif p == r"{CONDITION_1} : {EX} is either not present or {LITERAL}":
#        [ex, lit] = children
#        (t_lit, env1) = tc_expr(lit, env0); assert env1 is env0
#        assert t_lit == T_Undefined
#        return env0.with_type_test(ex, 'is a', T_not_passed | t_lit, asserting)

# 1411 obsoleted:
#     elif p == r"{CONDITION_1} : {var} is {LITERAL}, {LITERAL} or not supplied":
#         [ex, lita, litb] = children
#         (t_lita, env1) = tc_expr(lita, env0); assert env1 is env0
#         (t_litb, env1) = tc_expr(litb, env0); assert env1 is env0
#         assert t_lita == T_Null
#         assert t_litb == T_Undefined
#         return env0.with_type_test(ex, 'is a', t_lita | t_litb | T_not_passed, asserting)

# 1411 obsoleted:
#    elif p == r"{CONDITION_1} : {EX} is not present, or is either {LITERAL} or {LITERAL}":
#        [ex, lita, litb] = children
#        (t_lita, env1) = tc_expr(lita, env0); assert env1 is env0
#        (t_litb, env1) = tc_expr(litb, env0); assert env1 is env0
#        assert t_lita == T_Undefined
#        assert t_litb == T_Null
#        return env0.with_type_test(ex, 'is a', T_not_passed | t_lita | t_litb, asserting)

    elif p == r'{CONDITION_1} : {EX} and {EX} are both {LITERAL}':
        [exa, exb, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        if lit_type == T_Undefined:
            (a_t_env, a_f_env) = env0.with_type_test(exa, 'is a', T_Undefined, asserting)
            (b_t_env, b_f_env) = env0.with_type_test(exb, 'is a', T_Undefined, asserting)
            return (
                env_and(a_t_env, b_t_env),
                env_or(a_f_env, b_f_env)
            )
        else:
            env0.assert_expr_is_of_type(exa, lit_type)
            env0.assert_expr_is_of_type(exb, lit_type)
            return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} are both WriteSharedMemory or ReadModifyWriteSharedMemory events":
        # XXX spec is ambiguous: "each is A or B" vs "either both A or both B"
        [ea, eb] = children
        (a_t_env, a_f_env) = env0.with_type_test(ea, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(eb, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    elif p in [
        r"{CONDITION_1} : {EX} is {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is {backticked_oth}, {backticked_oth}, or {backticked_oth}",
        r"{CONDITION_1} : {EX} is either {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {var} is {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {var} is either {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {var} is one of {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}",
        # r"{CONDITION_1} : {var} is either {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}", # PR 1546 obsoleted
        r"{CONDITION_1} : {var} is {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {var} is {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {var} is not {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
    ]:
        [var, *lit_] = children
        assert len(lit_) in [3,4,5,6]
        lit_types = []
        for lit in lit_:
            (ti, envi) = tc_expr(lit, env0)
            # assert envi is env0
            lit_types.append(ti)
        lt = union_of_types(lit_types)
        env1 = env0.ensure_expr_is_of_type(var, lt)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} is either {LITERAL} or an? {nonterminal}":
        # Once, in EvaluateNew
        [var, literal, nont] = children
        assert literal.source_text() == '~empty~'
        t = T_empty_ | ptn_type_for(nont)
        return env0.with_type_test(var, 'is a', t, asserting)

    elif p == r"{CONDITION_1} : {var} is {LITERAL} or a Module Record":
        [var, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        assert lit.source_text() == '*"ambiguous"*'
        return env0.with_type_test(var, 'is a', T_String | T_Module_Record, asserting)

# PR 1567 obsoleted:
#    elif p == r'{CONDITION_1} : {var} is an integer such that {CONDITION_1}':
#        [var, cond] = children
#        (t_env, f_env) = tc_cond(cond, env0)
#        return (
#            t_env.with_expr_type_narrowed(var, T_Integer_),
#            t_env
#        )
#
#    elif p == r"{CONDITION_1} : {var} is a nonnegative integer":
#        [var] = children
#        return (
#            env0.with_expr_type_narrowed(var, T_Integer_),
#            env0
#        )

    elif p == r'{CONDITION_1} : {var} has an? {DSBN} internal method':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name == 'Call':
            # one of the few where the presence/absence of an internal method is a type-test?
            return env1.with_type_test(var, 'is a', T_function_object_, asserting)
        elif dsbn_name == 'Construct':
            return env1.with_type_test(var, 'is a', T_constructor_object_, asserting)
        else:
            assert dsbn_name == 'Construct'
            return (env1, env1)

    elif p == r"{CONDITION_1} : {SETTABLE} has an? {DSBN} field":
        [settable, dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        t = env0.assert_expr_is_of_type(settable, T_Record)
        if t.name == 'Environment Record' and dsbn_name == 'NewTarget':
            add_pass_error(
                cond,
                "STA can't confirm that `%s` could have a `%s` field"
                % ( settable.source_text(), dsbn_name )
            )
            # We could confirm if we looked at the subtypes and what fields they have.
            return (
                env0.with_expr_type_narrowed(settable, T_function_Environment_Record),
                env0
            )
        else:
            assert dsbn_name in fields_for_record_type_named_[t.name], (t.name, dsbn_name)
            return (env0, env0)

    elif p == r'{CONDITION_1} : {var} does not have an? {DSBN} field':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Record)
        # XXX We should check whether its type says it *could* have such a field.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} does not have an? {DSBN} internal slot':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} does not have an? {var} internal slot":
        [obj_var, slotname_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(slotname_var, T_SlotName_)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {var} also has a {DSBN} internal slot',
        r'{CONDITION_1} : {var} has an? {DSBN} internal slot',
    ]:
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX we could be more specific about the sub-kind of Object
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} is an IEEE 754-2019 binary32 NaN value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} is an IEEE 754-2019 binary64 NaN value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary64_)
        return (env1, env1)

    # --------
    # These 4 are affected by the strangeness described in Issue #831

    elif p == r"{CONDITION_1} : {var} is the {nonterminal} {TERMINAL}":
        [var, nont, term] = children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        env0.ensure_expr_is_of_type(var, T_grammar_symbol_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an? {nonterminal}":
        [var, nont] = children
        if var.source_text() == '_symbol_' and nont.source_text() in ['|ReservedWord|', '|Identifier|']:
            t = T_grammar_symbol_
        else:
            t = T_Parse_Node
        env1 = env0.ensure_expr_is_of_type(var, t)
        return (env1, env1)
        #return env0.with_type_test(var, 'is a', ptn_type_for(nont), asserting)

    elif p == r"{CONDITION_1} : {var} is {nonterminal}":
        [var, nont] = children
        env1 = env0.ensure_expr_is_of_type(var, T_grammar_symbol_)
        return (env1, env1)

#    elif p == r"{CONDITION_1} : {EX} is the same value as {PP_NAMED_OPERATION_INVOCATION}":
#        [ex, noi] = children
#        assert ex.source_text() == 'StringValue of _symbol_'
#        assert noi.source_text() == 'the StringValue of |IdentifierName|'
#        # For now, just return the env unchanged.
#        return (env0, env0)
# ^ obsoleted by PR 1519 + PR 2022

    elif p in [
        r"{CONDITION_1} : {var} is not one of {nonterminal}, {nonterminal}, {nonterminal}, `super` or `this`",
        r"{CONDITION_1} : {var} is not one of {nonterminal}, {nonterminal}, {nonterminal}, `super`, or `this`",
    ]:
        [local_ref, *_] = children
        env0.ensure_expr_is_of_type(local_ref, T_grammar_symbol_)
        return (env0, env0)

    # ------------------------
    # relating to Environment Record bindings:

    elif p in [
        r"{CONDITION_1} : {var} does not already have a binding for {var}",
        r"{CONDITION_1} : {var} does not have a binding for {var}",
        r"{CONDITION_1} : {var} has a binding for the name that is the value of {var}",
        r"{CONDITION_1} : {var} has a binding for {var}",
        r"{CONDITION_1} : {var} must have an uninitialized binding for {var}",
    ]:
        [er_var, n_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : the binding for {var} in {var} cannot be deleted",
        r"{CONDITION_1} : the binding for {var} in {var} has not yet been initialized",
        r"{CONDITION_1} : the binding for {var} in {var} is a mutable binding",
        r"{CONDITION_1} : the binding for {var} in {var} is a strict binding",
        r"{CONDITION_1} : the binding for {var} in {var} is an uninitialized binding",
    ]:
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the binding for {var} is an indirect binding":
        # todo: make ER explicit in spec?
        [n_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the binding exists":
        # elliptical
        [] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : When {SETTABLE} is instantiated it will have a direct binding for {var}':
        [settable, var] = children
        env0.assert_expr_is_of_type(settable, T_Environment_Record | T_Undefined)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    # --------------------------------------------------
    # relating to strict code:

    elif p in [
        r"{CONDITION_1} : the code matched by {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the function code for {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the source code matching {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the source code matching {var} is non-strict code",
        r"{CONDITION_1} : {PROD_REF} is contained in strict mode code",
        r"{CONDITION_1} : {var} is strict mode code",
    ]:
        [prod_ref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the code matching the syntactic production that is being evaluated is contained in strict mode code":
        [] = children
        return (env0, env0)

    # -------------------------------------------------
    # introduce metavariable:

    # PR 1668 privates:
    elif p in [
        r"{CONDITION_1} : {EX} contains an entry {var} such that {CONDITION_1}",
        r"{CONDITION_1} : {EX} does not contain an entry {var} such that {CONDITION_1}",
    ]:
        [list_var, element_var, cond] = children
        (list_type, env1) = tc_expr(list_var, env0)
        assert isinstance(list_type, ListType)
        env2 = env1.plus_new_entry(element_var, list_type.element_type)
        (cond_t_env, cond_f_env) = tc_cond(cond, env2)
        if 'contains' in p:
            return (cond_t_env, env1)
        elif 'does not contain' in p:
            return (env1, cond_t_env)
        else:
            assert 0, p

    # PR 1668 privates:
    elif p == r"{CONDITION_1} : {EX} contains a Private Name {var} such that {CONDITION_1}":
        [ex, var, cond] = children
        env0.assert_expr_is_of_type(ex, ListType(T_String))
        env_for_cond = env0.plus_new_entry(var, T_Private_Name) # XXX!
        (cond_t_env, cond_f_env) = tc_cond(cond, env_for_cond)
        return (cond_t_env, env0)

    elif p == r"{CONDITION_1} : {DOTTING} contains a Record {var} such that {CONDITION_1}":
        [ex, var, cond] = children
        env0.assert_expr_is_of_type(ex, ListType(T_Record))
        env_for_cond = env0.plus_new_entry(var, T_Record)
        (cond_t_env, cond_f_env) = tc_cond(cond, env_for_cond)
        return (cond_t_env, env0)

    elif p == r"{CONDITION_1} : there does not exist an element {var} of {var} such that {CONDITION_1}":
        [member_var, list_var, cond] = children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String)) # over-specific
        env2 = env1.plus_new_entry(member_var, T_String)
        (t_env, f_env) = tc_cond(cond, env2)
        return (env1, env1)

    elif p in [
        r'{CONDITION_1} : there does not exist a member {var} of set {var} such that {CONDITION_1}',
        r'{CONDITION_1} : there exists a member {var} of set {var} such that {CONDITION_1}',
    ]:
        [member_var, set_var, cond] = children
        env1 = env0.ensure_expr_is_of_type(set_var, T_CharSet)
        env2 = env1.plus_new_entry(member_var, T_character_)
        (t_env, f_env) = tc_cond(cond, env2)
        assert t_env is f_env
        return (env1, env1)

    elif p == r"{CONDITION_1} : there exists an integer {var} between 0 (inclusive) and {var} (exclusive) such that {CONDITION_1}":
        [i_var, m_var, cond] = children
        env0.assert_expr_is_of_type(m_var, T_Integer_)
        env_for_cond = env0.plus_new_entry(i_var, T_Integer_)
        return tc_cond(cond, env_for_cond)

#    elif p == r"{CONDITION_1} : there exists any integer {var} not smaller than {var} such that {CONDITION_1}, and {CONDITION_1}":
#        [i_var, min_var, conda, condb] = children
#        env0.assert_expr_is_of_type(min_var, T_Integer_)
#        env_for_cond = env0.plus_new_entry(i_var, T_Integer_)
#        (at_env, af_env) = tc_cond(conda, env_for_cond)
#        (bt_env, bf_env) = tc_cond(condb, env_for_cond)
#        return (env_and(at_env, bt_env), env_or(af_env, bf_env))
# ^ obsoleted by PR #2009

    elif p == r"{CONDITION_1} : there exists any integer {var} such that {CONDITION_1} and {CONDITION_1}":
        [i_var, conda, condb] = children
        env_for_cond = env0.plus_new_entry(i_var, T_Integer_)
        (at_env, af_env) = tc_cond(conda, env_for_cond)
        (bt_env, bf_env) = tc_cond(condb, env_for_cond)
        return (env_and(at_env, bt_env), env_or(af_env, bf_env))

    elif p == r"{CONDITION_1} : for all nonnegative integers {var} less than {var}, {CONDITION_1}":
        [loop_var, min_var, cond] = children
        env0.assert_expr_is_of_type(min_var, T_Integer_)
        env_for_cond = env0.plus_new_entry(loop_var, T_Integer_)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there is a WriteSharedMemory or ReadModifyWriteSharedMemory event {var} that has {var} in its range such that {CONDITION_1}":
        [let_var, i, cond] = children
        env0.assert_expr_is_of_type(i, T_Integer_)
        env_for_cond = env0.plus_new_entry(let_var, T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there is an event {var} such that {CONDITION}":
        [let_var, cond] = children
        env_for_cond = env0.plus_new_entry(let_var, T_Shared_Data_Block_event)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : {SETTABLE} is not equal to {SETTABLE} for any integer value {var} in the range {LITERAL} through {var}, exclusive":
        [seta, setb, let_var, lo, hi] = children
        env0.assert_expr_is_of_type(lo, T_Integer_)
        env0.assert_expr_is_of_type(hi, T_Integer_)
        env_for_settables = env0.plus_new_entry(let_var, T_Integer_)
        env_for_settables.assert_expr_is_of_type(seta, T_Integer_)
        env_for_settables.assert_expr_is_of_type(setb, T_Integer_)
        return (env0, env0)

    # --------------------------------------------------
    # whatever

    elif p == r'{CONDITION_1} : {var} is the same Number value as {var}':
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_Number)
        env1 = env0.ensure_expr_is_of_type(var2, T_Number)
        return (env1, env1)

    elif p == r'{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}':
        [a, _, b, _, c] = children
        env0.assert_expr_is_of_type(a, T_Integer_)
        env0.ensure_expr_is_of_type(b, T_Number)
        env0.assert_expr_is_of_type(c, T_Integer_)
        return (env0, env0)

    elif p in [
        r"{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}",
        r'{NUM_COMPARISON} : {var} (is less than) {FACTOR}',
    ]:
        [a, _, b] = children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        (b_t, env1) = tc_expr(b, env0); assert env1 is env0

        if (
            a_t.is_a_subtype_of_or_equal_to(T_MathReal_)
            or
            b_t.is_a_subtype_of_or_equal_to(T_MathReal_)
        ):
            assert a_t == T_MathInteger_
            assert b_t == T_MathInteger_
            env2 = env0
        elif a_t == T_code_unit_ and b_t == T_Integer_:
            env2 = env0
        elif a_t == T_BigInt and b_t == T_Integer_:
            env2 = env0
        else:
            env1 = env0.ensure_expr_is_of_type(a, T_Number)
            env2 = env1.ensure_expr_is_of_type(b, T_Number)
            # It's almost always T_Integer_ for both.

        return (env2, env2)

    elif p in [
        r'{NUM_COMPARISON} : {NUM_COMPARAND} is not less than {NUM_LITERAL} and not greater than {NUM_LITERAL}',
        r'{NUM_COMPARISON} : {NUM_COMPARAND} is less than {NUM_LITERAL} or greater than {NUM_LITERAL}',
    ]:
        [a,b,c] = children
        env0.assert_expr_is_of_type(a, T_Integer_)
        env0.assert_expr_is_of_type(b, T_Integer_)
        env0.assert_expr_is_of_type(c, T_Integer_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : the file CaseFolding.txt of the Unicode Character Database provides a simple or common case folding mapping for {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} does not consist of a single code unit':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} does not contain exactly one character':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (env1, env1)

    elif p == r'{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive':
        [prod_ref] = children
        # XXX check that prod_ref makes sense
        return (env0, env0)

    elif p == r'{CONDITION_1} : The calling agent is not in the critical section for any WaiterList':
        # nothing to check
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : The execution context stack has at least two elements",
        r"{CONDITION_1} : The execution context stack is not empty",
        # r"{CONDITION_1} : The execution context stack is now empty", # PR 1597
        r"{CONDITION_1} : the execution context stack is empty",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : When we return here, {var} has already been removed from the execution context stack and {var} is the currently running execution context":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_execution_context)
        env0.assert_expr_is_of_type(b_var, T_execution_context)
        return (env0, env0)

    elif p == r'{CONDITION_1} : no such execution context exists':
        [] = children
        return (env0, env0)

    elif p in [
        # r"{CONDITION_1} : {var} contains the names {DSBN}, {DSBN}, {DSBN}, and {DSBN}", # obsoleted by PR 1460
        r"{CONDITION_1} : {var} contains the names {DSBN}, {DSBN}, {DSBN}, {DSBN}, and {DSBN}",
    ]:
        [var, *dsbn_] = children
        # XXX assert that each dsbn_ is a slot name
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(ListType(T_SlotName_))
        return (env1, env1)

    elif p == r'{CONDITION_1} : both {EX} and {EX} are absent':
        [exa, exb] = children
        (ta, enva) = tc_expr(exa, env0); assert enva is env0
        (tb, envb) = tc_expr(exb, env0); assert envb is env0
        # XXX Could assert that T_not_set is a subtype of ta and tb,
        # but the typing of Property Descriptors is odd.
        # XXX Could look at exa.source_text() and exb.source_text()
        # and make a dichotomy re Prop Desc subtypes, but not really worth it.
        # (because the form only appears in IsAccessorDescriptor and IsDataDescriptor,
        # which are tiny)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} has a thisValue component':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a Reference to an Environment Record binding":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (env0, env0)

    elif p == r'{CONDITION_1} : The calling agent is in the critical section for {var}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {EX} is an element of {var}',
        r"{CONDITION_1} : {EX} is not an element of {var}",
    ]:
        [value_ex, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_ex, list_var)
        return (env1, env1)

    elif p in [
        r"{CONDITION_1} : {DOTTING} contains {var}",
        r'{CONDITION_1} : {var} contains {var}',
        r"{CONDITION_1} : {var} does not contain {var}",
    ]:
        [list_var, value_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_var, list_var)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} is not in {PREFIX_PAREN}":
        [item_var, set_pp] = children
        env0.assert_expr_is_of_type(set_pp, T_Set)
        env0.assert_expr_is_of_type(item_var, T_event_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} has no further use. It will never be activated as the running execution context':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_execution_context)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} has a numeric value less than {code_unit_lit}':
        [var, code_unit_lit] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_point_) # odd
        return (env1, env1)

    elif p in [
        r"{CONDITION_1} : {EX} is different from {EX}",
        r"{CONDITION_1} : {EX} is equal to {EX}",
        r"{CONDITION_1} : {EX} is not equal to {EX}",
        r"{CONDITION_1} : {EX} is the same as {EX}",
        # r"{CONDITION_1} : {var} and {var} are the same", # obsoleted by PR #1046
        r"{CONDITION_1} : {var} is not the same as {var}",
    ]:
        [exa, exb] = children
        (exa_type, exa_env) = tc_expr(exa, env0); assert exa_env is env0
        (exb_type, exb_env) = tc_expr(exb, env0); assert exb_env is env0
        if exa_type == exb_type:
            # good
            env1 = env0
        elif exa_type == T_TBD:
            env1 = env0.with_expr_type_replaced(exa, exb_type)
        elif exa_type == T_Environment_Record | T_Undefined and exb_type == T_Environment_Record:
            env1 = env0.with_expr_type_replaced(exa, exb_type)
        elif exa_type == T_Integer_ and exb_type == T_Number:
            # XXX could be more specific
            env1 = env0
        elif exa_type == T_Number and exb_type == T_Number | T_BigInt:
            env1 = env0
        elif exa_type == T_BigInt | T_Integer_ and exb_type == T_BigInt | T_Number:
            # Atomics.wait
            env1 = env0
        else:
            assert 0, (exa_type, exb_type)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} and {var} are exactly the same sequence of code units (same length and same code units at corresponding indices)':
        # occurs once, in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_String); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_String); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {EX} and {EX} are both {LITERAL} or both {LITERAL}':
        # occurs once, in SameValueNonNumber
        [exa, exb, litc, litd] = children
        assert litc.source_text() == '*true*'
        assert litd.source_text() == '*false*'
        enva = env0.ensure_expr_is_of_type(exa, T_Boolean); assert enva is env0
        envb = env0.ensure_expr_is_of_type(exb, T_Boolean); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {var} and {var} are both the same Symbol value':
        # occurs once, in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Symbol); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_Symbol); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {var} and {var} are the same Number value':
        # in Abstract Relational Comparison
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Number); # assert enva is env0
        envb = enva.ensure_expr_is_of_type(varb, T_Number); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {var} and {var} are the same Object value':
        # in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Object); # assert enva is env0
        envb = enva.ensure_expr_is_of_type(varb, T_Object); # assert envb is env0
        return (envb, envb)

    elif p == r"{CONDITION_1} : {EX} and {EX} are the same Shared Data Block values":
        [exa, exb] = children
        env1 = env0.ensure_expr_is_of_type(exa, T_Shared_Data_Block)
        env2 = env1.ensure_expr_is_of_type(exb, T_Shared_Data_Block)
        return (env2, env2)

    elif p in [
        r"{CONDITION_1} : {var} and {var} are the same Module Record",
        r"{CONDITION_1} : {var} and {DOTTING} are the same Module Record",
        r"{CONDITION_1} : {DOTTING} and {DOTTING} are not the same Module Record",
    ]:
        [ex1, ex2] = children
        env0.assert_expr_is_of_type(ex1, T_Module_Record)
        env0.assert_expr_is_of_type(ex2, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is the same Parse Node as {EX}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_Parse_Node)
        env0.assert_expr_is_of_type(exb, T_Parse_Node)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} has attribute values { {DSBN}: *true*, {DSBN}: *true* }':
        [var, dsbn1, dsbn2] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Property_Descriptor)
        assert dsbn1.source_text() == '[[Writable]]'
        assert dsbn2.source_text() == '[[Enumerable]]'
        return (env1, env1)

    elif p == r'{CONDITION_1} : {EX} is {var}':
        [a_ex, b_ex] = children
        (a_t, a_env) = tc_expr(a_ex, env0)
        (b_t, b_env) = tc_expr(b_ex, env0); assert b_env is env0
        assert a_t != T_TBD
        if b_t == T_TBD:
            env1 = env0.with_expr_type_replaced(b_ex, a_t)
        elif a_t == T_Number and b_t == T_Integer_:
            env1 = env0
        elif a_t == T_throw_ | T_Undefined and b_t == T_throw_:
            # Evaluate()
            env1 = env0
        else:
            # assert a_t.is_a_subtype_of_or_equal_to(b_t)
            (common_t, _) = a_t.split_by(b_t)
            assert common_t != T_0
            env1 = env0
        e = env_or(a_env, env0)
        return (e, e)

    elif p == r'{CONDITION_1} : {var} has {var} in its range':
        [sdbe_var, loc_var] = children
        env1 = env0.ensure_expr_is_of_type(sdbe_var, T_Shared_Data_Block_event)
        env2 = env1.ensure_expr_is_of_type(loc_var, T_Integer_)
        return (env2, env2)

    elif p in [
        r'{CONDITION_1} : {EX} is in {EX}',
        r'{CONDITION_1} : {var} is not in {var}',
        r'{CONDITION_1} : {var} occurs exactly once in {var}',
    ]:
        [item_var, container_var] = children
        (container_t, env1) = tc_expr(container_var, env0); assert env1 is env0
        if container_t == T_String:
            env0.assert_expr_is_of_type(item_var, T_code_unit_)
        elif container_t == T_CharSet:
            env0.assert_expr_is_of_type(item_var, T_character_)
        elif container_t == T_Relation:
            env0.assert_expr_is_of_type(item_var, T_event_pair_)
        elif isinstance(container_t, ListType):
            el_type = container_t.element_type
            if el_type == T_Cyclic_Module_Record:
                # The stack only contains CMRs,
                # but _requiredModule_ might be a non-C MR:
                env0.assert_expr_is_of_type(item_var, T_Module_Record)
                # It's still reasonable to ask if _requiredModule_ is in the stack.
            elif el_type == T_String: # PR 1668
                env0.assert_expr_is_of_type(item_var, el_type)
            else:
                assert 0, container_t
        else:
            assert 0, container_t
        return (env0, env0)

#    elif p == r'{CONDITION_1} : its value is the name of a Job Queue recognized by this implementation':
#        # Once, in EnqueueJob
#        [] = children
#        return (env0, env0)
# ^ obsoleted by PR 1597

    elif p == r'{CONDITION_1} : There are sufficient bytes in {var} starting at {var} to represent a value of {var}':
        [ab_var, st_var, t_var] = children
        env0.assert_expr_is_of_type(ab_var, T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
        env0.assert_expr_is_of_type(st_var, T_Integer_)
        env0.assert_expr_is_of_type(t_var, T_TypedArray_element_type_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : The next step never returns an abrupt completion because {CONDITION_1}":
        [subcond] = children
        return tc_cond(subcond, env0, asserting)

    elif p == r'{CONDITION_1} : {var} does not have an own property with key {var}':
        [obj_var, key_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is not already suspended':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is on the list of waiters in {var}':
        [w_var, wl_var] = children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} was notified explicitly by another agent calling NotifyWaiter({var}, {var})':
        [w_var, *blah] = children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is as small as possible':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is odd':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {PROD_REF} is `export` {nonterminal}':
        [prod_ref, nont] = children
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {var} is empty',
        r"{CONDITION_1} : {var} is not empty",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_CharSet | T_List | T_String)
        # XXX For String, change spec to "is [not] the empty String" ?
        return (env0, env0)

    elif p == r"{CONDITION_1} : We've reached the starting point of an `export *` circularity":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} provides the direct binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} imports a specific binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not contained within an? {nonterminal}, {nonterminal}, or {nonterminal}":
        [var, *nont_] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is the {nonterminal} of an? {nonterminal}":
        [var, nont1, nont2] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {EX} is -1",
        r"{CONDITION_1} : {EX} is not -1",
    ]:
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not finite":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} is not the ordinary object internal method defined in {h_emu_xref}":
        [dotting, emu_xref] = children
        env0.assert_expr_is_of_type(dotting, T_proc_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This is a circular import request":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : A `default` export was not explicitly defined by this module":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : There is more than one `*` import that includes the requested name":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : every field in {var} is absent":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Property_Descriptor)
        return (env0, env0)

    elif p == r"{CONDITION_1} : its value is {LITERAL}":
        # todo: change the grammar or the spec
        [lit] = children
        env0.assert_expr_is_of_type(lit, T_Boolean)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the {DSBN} fields of {var} and {var} are the Boolean negation of each other":
        [dsbn, a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_Property_Descriptor)
        env0.assert_expr_is_of_type(b_var, T_Property_Descriptor)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} have different results":
        [a_ex, b_ex] = children
        env0.assert_expr_is_of_type(a_ex, T_Boolean)
        env0.assert_expr_is_of_type(b_ex, T_Boolean)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not include the element {LITERAL}":
        [list_var, item_lit] = children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String))
        env0.assert_expr_is_of_type(item_lit, T_String)
        return (env1, env1)

#    elif p == r"{CONDITION_1} : the order of evaluation needs to be reversed to preserve left to right evaluation":
#        [] = children
#        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a prefix of {var}":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_String)
        env0.assert_expr_is_of_type(b_var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the mathematical value of {var} is less than the mathematical value of {var}":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(b_var, T_Number|T_BigInt)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is absent or has the value {LITERAL}":
        [ex, literal] = children
        (lit_type, env1) = tc_expr(literal, env0); assert env1 is env0
        assert lit_type == T_Boolean
        # hrm
        return (env1, env1)

    elif p == r"{CONDITION_1} : we return here":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the async function either threw an exception or performed an implicit or explicit return; all awaiting is done":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the async generator either threw an exception or performed either an implicit or explicit return":
        [] = children
        return (env0, env0)

#    elif p == r"{TYPE_TEST} : Type({TYPE_ARG}) is {var}":
#        [type_arg, var] = children
#        env0.assert_expr_is_of_type(var, T_LangTypeName_)
#        return (env0, env0)
# ^ obsoleted by the merge of PR #1918

    elif p == r"{TYPE_TEST} : Type({TYPE_ARG}) is not an element of {var}":
        [type_arg, var] = children
        env0.assert_expr_is_of_type(var, ListType(T_LangTypeName_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not contain a rest parameter, any binding patterns, or any initializers. It may contain duplicate identifiers":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has any elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : it must be in the object Environment Record":
        # elliptical
        [] = children
        return (env0, env0)
 
    elif p == r"{CONDITION_1} : This method is never invoked. See {h_emu_xref}":
        [emu_xref] = children
        return (None, env0)

    # for PR #1961 compound_assignment
    elif p == r"{CONDITION_1} : Execution cannot reach this step":
        return (None, env0)

    elif p == r"{CONDITION_1} : The following loop will terminate":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the base of {var} is an Environment Record":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the above call will not return here, but instead evaluation will continue as if the following return has already occurred":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} binds a single name":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} contains any duplicate entries",
        r"{CONDITION_1} : {var} contains no duplicate entries",
        r"{CONDITION_1} : {var} has any duplicate entries",
        r"{CONDITION_1} : {var} has no duplicate entries",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

# PR 1676 obsoleted
#    elif p == r"{CONDITION_1} : All of the above CreateDataProperty operations return {LITERAL}":
#        [literal] = children
#        return (env0, env0)

    elif p == r"{CONDITION_1} : the generator either threw an exception or performed either an implicit or explicit return":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a String value that is this specification's name of an intrinsic object. The corresponding object must be an intrinsic that is intended to be used as the {DSBN} value of an object":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} contain the same values in the same order":
        # Once, in GetTemplateObject.
        [a_ex, b_ex] = children
        env0.assert_expr_is_of_type(a_ex, ListType(T_String))
        env1 = env0.ensure_expr_is_of_type(b_ex, ListType(T_String))
        return (env0, env0)

# obsoleted by PR #1046:
#    elif p == r"{CONDITION_1} : The VariableEnvironment and LexicalEnvironment of {var} are the same":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_execution_context)
#        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not currently have a property {var}":
        [obj_var, pn_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(pn_var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r"{CONDITION_1} : its value is either {LITERAL} or {LITERAL}":
        # once, in OrdinaryToPrimitive
        # elliptical    
        [alit, blit] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} contains any code unit other than *"g"*, *"i"*, *"m"*, *"s"*, *"u"*, or *"y"* or if it contains the same code unit more than once':
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains {LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lit, T_String | T_code_unit_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This is an attempt to change the value of an immutable binding":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is now the running execution context":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {PROD_REF} is the token `false`",
        r"{CONDITION_1} : {PROD_REF} is the token `true`",
    ]:
        [prod_ref] = children
        assert prod_ref.source_text() == '|BooleanLiteral|'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has no elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : an implementation-defined debugging facility is available and enabled":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a formal parameter mapping for {var}":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Object)
        env0.assert_expr_is_of_type(bvar, T_String | T_Symbol)
        return (env0, env0)

#    elif p in [
#        r"{CONDITION_1} : This is a re-export of an imported module namespace object",
#        r"{CONDITION_1} : this is a re-export of a single name",
#    ]:
#        [] = children
#        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} exists and has been initialized":
        [dotting] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} are not the same Realm Record":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Realm_Record)
        env0.assert_expr_is_of_type(bvar, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : any element of {PP_NAMED_OPERATION_INVOCATION} also occurs in {PP_NAMED_OPERATION_INVOCATION}":
        [anoi, bnoi] = children
        env0.assert_expr_is_of_type(anoi, ListType(T_String)) # T_String not justified, but always correct (currently)
        env0.assert_expr_is_of_type(bnoi, ListType(T_String))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains any duplicate elements":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : All named exports from {var} are resolvable":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

#    elif p == r"{CONDITION_1} : ModuleDeclarationInstantiation has already been invoked on {var} and successfully completed":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_Module_Record)
#        return (env0, env0)

    elif p == r"{CONDITION_1} : Evaluate has already been invoked on {var} and successfully completed":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has been linked and declarations in its module environment have been instantiated":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r'''{CONDITION_1} : The value of {var}'s {starred_str} property is {EX}''':
        [var, prop_name, ex] = children
        env0.assert_expr_is_of_type(var, T_Object)
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (env0, env0)

    elif p == r"{NUM_COMPARISON} : {var} is finite and less than {var}":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Integer_) # XXX or infinity
        env0.assert_expr_is_of_type(bvar, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the character {EX} is one of {nonterminal}":
        [ex, nonterminal] = children
        env0.assert_expr_is_of_type(ex, T_character_)
        assert nonterminal.source_text() == '|LineTerminator|'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} is not the same character value as {PP_NAMED_OPERATION_INVOCATION}":
        [anoi, bnoi] = children
        env0.assert_expr_is_of_type(anoi, T_character_)
        env0.assert_expr_is_of_type(bnoi, T_character_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is finite":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

#    elif p == r"{CONDITION_1} : All dependencies of {var} have been transitively resolved and {var} is ready for evaluation":
#        [var, var2] = children
#        assert var.children == var2.children
#        env0.assert_expr_is_of_type(var, T_Module_Record)
#        return (env0, env0)
# ^ obsoleted by PR 1597

    elif p == r"{CONDITION_1} : the host requires use of an exotic object to serve as {var}'s global object":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the host requires that the `this` binding in {var}'s global scope return an object other than the global object":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

#    elif p in [
#        r"{CONDITION_1} : {var} is the source code of a script",
#        r"{CONDITION_1} : {var} is the source code of a module",
#    ]:
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
#        return (env0, env0)
# ^ obsoleted by PR 1597

    elif p == r"{CONDITION_1} : the code units at index ({SUM}) and ({SUM}) within {var} do not represent hexadecimal digits":
        [posa, posb, var] = children
        env0.assert_expr_is_of_type(posa, T_Integer_)
        env0.assert_expr_is_of_type(posb, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the most significant bit in {var} is {NUM_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the two most significant bits in {var} are not 10":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not contain a valid UTF-8 encoding of a Unicode code point":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is {U_LITERAL}":
        [noi, lit] = children
        (noi_t, noi_env) = tc_expr(noi, env0); assert noi_env is env0
        env0.assert_expr_is_of_type(lit, noi_t)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} can be the string-concatenation of {var} and some other String {var}":
        [a,b,c] = children
        env0.assert_expr_is_of_type(a, T_String)
        env0.assert_expr_is_of_type(b, T_String)
        # Hm, This is causes `c` to come into existence.
        # env0.assert_expr_is_of_type(c, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} each contain exactly one character":
        [a,b] = children
        env0.assert_expr_is_of_type(a, T_CharSet)
        env0.assert_expr_is_of_type(b, T_CharSet)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains any {nonterminal}":
        [rvar, nonterminal] = children
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the {var}<sup>th</sup> capture of {var} was defined with a {nonterminal}":
        [ivar, rvar, nonterminal] = children
        env0.assert_expr_is_of_type(ivar, T_Integer_)
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : A unique such {nonterminal} is found":
        [nonterminal] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a List of Unicode code points that is identical to a List of Unicode code points that is a canonical, unaliased Unicode property name listed in the &ldquo;Canonical property name&rdquo; column of {h_emu_xref}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a List of Unicode code points that is identical to a List of Unicode code points that is a property value or property value alias for Unicode property {var} listed in the &ldquo;Property value and aliases&rdquo; column of {h_emu_xref} or {h_emu_xref}":
        [va, vb, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(va, ListType(T_Integer_))
        env0.assert_expr_is_of_type(vb, ListType(T_Integer_))
        return (env0, env0)
    
    elif p == r"{CONDITION_1} : {var} is a Unicode property name or property alias listed in the &ldquo;Property name and aliases&rdquo; column of {h_emu_xref}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a binary Unicode property or binary property alias listed in the &ldquo;Property name and aliases&rdquo; column of {h_emu_xref}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} is identical to a List of Unicode code points that is the name of a Unicode general category or general category alias listed in the &ldquo;Property value and aliases&rdquo; column of {h_emu_xref}":
        [noi, emu_xref] = children
        env0.assert_expr_is_of_type(noi, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have a Generator component":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an AsyncGenerator instance":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_AsyncGenerator_object_)
        return (env1, env1)
    
    elif p == r"{CONDITION_1} : {EX} is listed in the Code Unit Value column of {h_emu_xref}":
        [ex, emu_xref] = children
        assert emu_xref.source_text() == '<emu-xref href="#table-json-single-character-escapes"></emu-xref>'
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (env0, env0)

    # ----

    elif p == r"{CONDITION_1} : {var} is not on the list of waiters in any WaiterList":
        [sig_var] = children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not on the list of waiters in {var}":
        [sig_var, wl_var] = children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} are valid byte offsets within the memory of {var}":
        [offset1, offset2, sdb] = children
        env1 = env0.ensure_expr_is_of_type(offset1, T_Integer_)
        env1.assert_expr_is_of_type(offset2, T_Integer_)
        env1.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} is divisible by {NUM_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        env0.assert_expr_is_of_type(lit, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not one of {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}":
        [var, *lit_] = children
        tc_expr
        (var_t, var_env) = tc_expr(var, env0); assert var_env is env0
        for lit in lit_:
            env0.assert_expr_is_of_type(lit, var_t)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is one of the code units in {STR_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        env0.assert_expr_is_of_type(lit, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : neither {var} nor any prefix of {var} satisfies the syntax of a {nonterminal} (see {h_emu_xref})":
        [var1, var2, nont, emu_xref] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the four code units at indices {SUM}, {SUM}, {SUM}, and {SUM} within {var} are all hexadecimal digits":
        [e1, e2, e3, e4, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(e1, T_Integer_)
        env0.assert_expr_is_of_type(e2, T_Integer_)
        env0.assert_expr_is_of_type(e3, T_Integer_)
        env0.assert_expr_is_of_type(e4, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the two code units at indices {SUM} and {SUM} within {var} are both hexadecimal digits":
        [i1, i2, var] = children
        env0.assert_expr_is_of_type(i1, T_Integer_)
        env0.assert_expr_is_of_type(i2, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : GlobalSymbolRegistry does not currently contain an entry for {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the first two code units of {var} are either {STR_LITERAL} or {STR_LITERAL}":
        [var, lita, litb] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a code unit that is not a radix-{var} digit":
        [svar, rvar] = children
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(rvar, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have all of the internal slots of an? {TYPE_NAME} Iterator Instance ({h_emu_xref})":
        [var, type_name, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have all of the internal slots of a RegExp String Iterator Object Instance (see {h_emu_xref})":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is the String value {STR_LITERAL} or the String value {STR_LITERAL}":
        [var, lita, litb] = children
        env0.assert_expr_is_of_type(var, T_Tangible_) # you'd expect T_String, but _hint_ in Date.prototype [ @@toPrimitive ]
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is the String value {STR_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_Tangible_) # you'd expect T_String, but _hint_ in Date.prototype [ @@toPrimitive ]
        env0.assert_expr_is_of_type(lit, T_String)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : this method was called with more than one argument",
        r"{CONDITION_1} : only one argument was passed",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an integer index &le; {var}":
        [a, b] = children
        env0.assert_expr_is_of_type(b, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(a, T_Integer_)
        return (env1, env1)

#    elif p == r"{CONDITION_1} : {var} is added as a single item rather than spread":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_Tangible_)
#        return (env0, env0)

    elif p == r"{CONDITION_1} : both {EX} and {EX} are {LITERAL}":
        [exa, exb, lit] = children
        (t, env1) = tc_expr(lit, env0); assert env1 is env0
        env1.assert_expr_is_of_type(exa, t)
        env1.assert_expr_is_of_type(exb, t)
        return (env1, env1)

    elif p == r"{CONDITION_1} : the number of actual arguments is {NUM_LITERAL}":
        [lit] = children
        env0.assert_expr_is_of_type(lit, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the sequence of code units of {var} starting at {var} of length {var} is the same as the full code unit sequence of {var}":
        [sa, k, n, sb] = children
        env0.assert_expr_is_of_type(sa, T_String)
        env0.assert_expr_is_of_type(k, T_Integer_)
        env0.assert_expr_is_of_type(n, T_Integer_)
        env0.assert_expr_is_of_type(sb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not currently an element of {var}":
        [item_var, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(item_var, list_var)
        return (env1, env1)

    elif p == r"{NUM_COMPARISON} : {NUM_COMPARAND} is 10 or less":
        [x] = children
        env0.assert_expr_is_of_type(x, T_Integer_)
        return (env0, env0)

# 1411 obsoleted:
#    elif p == r"{CONDITION_1} : no arguments were passed to this function invocation":
#        [] = children
#        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is neither {LITERAL} nor the active function":
        [ex, lit] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is any ECMAScript language value other than an Object with a {DSBN} internal slot. If it is such an Object, the definition in {h_emu_xref} applies":
        [var, dsbn, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : The value of {var}'s `length` property is {var}":
        [ovar, ivar] = children
        env0.assert_expr_is_of_type(ovar, T_Object)
        env0.assert_expr_is_of_type(ivar, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : When we reach this step, {var} has already been removed from the execution context stack and {var} is the currently running execution context":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(varb, T_execution_context)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} has an? {DSBN} internal slot whose value is a PromiseCapability Record",
        r"{CONDITION_1} : {var} has an? {DSBN} internal slot whose value is an Object",
    ]:
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_Object) # more specific?
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are in {EX}",
        r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are not in {EX}",
        r"{CONDITION_1} : either {PAIR} or {PAIR} is in {EX}",
    ]:
        [paira, pairb, ex] = children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

# PR 1676 obsoleted
#    elif p == r"{CONDITION_1} : Each of the above calls returns {LITERAL}":
#        [lit] = children
#        assert lit.source_text() == '*true*'
#        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} are in a race in {var}":
        [ea, eb, exe] = children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(exe, T_candidate_execution)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} and {var} do not have disjoint ranges",
        r"{CONDITION_1} : {var} and {var} have equal ranges",
        r"{CONDITION_1} : {var} and {var} have overlapping ranges",
    ]:
        [ea, eb] = children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not {var}":
        [ea, eb] = children
        # over-specific:
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is listed in the &ldquo;Code Point&rdquo; column of {h_emu_xref}":
        [ex, emu_xref] = children
        env0.assert_expr_is_of_type(ex, T_code_point_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has the same numeric value as a {h_emu_xref} or {h_emu_xref}":
        [var, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (env0, env0)

    # explicit-exotics:
    elif p in [
        r"{CONDITION_1} : the caller will not be overriding both {var}'s {DSBN} and {DSBN} essential internal methods",
        r"{CONDITION_1} : the caller will not be overriding all of {var}'s {DSBN}, {DSBN}, and {DSBN} essential internal methods",
    ]:
        var = children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains {DSBN}":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, ListType(T_SlotName_))
        return (env0, env0)

    # PR 1554 NumericValue
    elif p == r"{CONDITION_1} : {nonterminal} has more than 20 significant digits":
        [nont] = children
        env0.assert_expr_is_of_type(nont, T_grammar_symbol_) # but really T_Parse_Node. Should use {PROD_REF}.
        return (env0, env0)

    # PR 1554 NumericValue:
    elif p == r"{CONDITION_1} : {var} has more than 20 significant digits":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    # PR 1554 NumericValue
    elif p == r"{CONDITION_1} : {var} contains a {nonterminal}":
        [var, nont] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        env0.assert_expr_is_of_type(nont, T_grammar_symbol_)
        return (env0, env0)

    # PR 1554 NumericValue
    elif p == r'{CONDITION_1} : the first non white space code point in {var} is `"-"`':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (env0, env0)

    # PR ? function-strictness
    elif p == r"{CONDITION_1} : the source text matching {var} is strict mode code":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not a {h_emu_xref} or {h_emu_xref}":
        [var, xrefa, xrefb] = children
        assert xrefa.source_text() == '<emu-xref href="#leading-surrogate"></emu-xref>'
        assert xrefb.source_text() == '<emu-xref href="#trailing-surrogate"></emu-xref>'
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} Contains {nonterminal}":
        [local_ref, nonterminal] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} or {var} is {LITERAL}":
        [v1, v2, lit] = children
        env0.assert_expr_is_of_type(v1, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(v2, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(lit, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} or {var} are any of {LITERAL}, {LITERAL}, or {LITERAL}":
        [v1, v2, lita, litb, litc] = children
        env0.assert_expr_is_of_type(v1, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(v2, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(lita, T_Number)
        env0.assert_expr_is_of_type(litb, T_Number)
        env0.assert_expr_is_of_type(litc, T_Number)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {PROD_REF} is {backticked_oth}",
        r"{CONDITION_1} : {LOCAL_REF} is {backticked_oth}",
    ]:
        [prod_ref, oth] = children
        return (env0, env0)

#    elif p == r"{CONDITION_1} : @ is {EX}":
#        [ex] = children
#        env0.assert_expr_is_of_type(ex, T_Unicode_code_points_)
#        return (env0, env0)
# ^ obsoleted by PR 1961

    elif p == r"{CONDITION_1} : {var} has a Synchronize event":
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not provide the direct binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} does not contain {starred_str}":
        [ex, starred_str] = children
        env0.assert_expr_is_of_type(ex, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains any code points other than {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, or {backticked_word}, or if it contains the same code point more than once":
        [noi, *bw_] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        for bw in bw_:
            assert len(bw.source_text()) == 3 # single-character 'words'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains {backticked_word}":
        [noi, bw] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        assert len(bw.source_text()) == 3 # single-character 'word'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has all of the internal slots of a For-In Iterator Instance ({h_emu_xref})":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} did not conform to the grammar":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : any elements of {var} were not matched by the parse": 
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : any Early Error conditions exist":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : This call to Evaluate is not happening at the same time as another call to Evaluate within the surrounding agent":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} have the same number of elements":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} do not have the same number of elements":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var}, {var}, and {var} have the same number of elements":
        [vara, varb, varc] = children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        env0.assert_expr_is_of_type(varc, T_List)
        return (env0, env0)

    # elif p == r"{CONDITION_1} : All named exports from {var} are resolvable":
    # elif p == r"{CONDITION_1} : any static semantics errors are detected for {var} or {var}":
    # elif p == r"{CONDITION_1} : either {EX} or {EX} is present":
    # elif p == r"{CONDITION_1} : either {EX} or {EX} is {LITERAL}":
    # elif p == r"{CONDITION_1} : replacing the {nonterminal} {var} with a {nonterminal} that has {var} as a {nonterminal} would not produce any Early Errors for {var}":
    # elif p == r"{CONDITION_1} : the Unicode Character Database provides a language insensitive lower case equivalent of {var}":
    # elif p == r"{CONDITION_1} : there is an infinite number of ReadSharedMemory or ReadModifyWriteSharedMemory events in SharedDataBlockEventSet({var}) with equal range that {SAB_RELATION} {var}":
    # elif p == r"{CONDITION_1} : there is no such integer {var}":
    # elif p == r"{CONDITION_1} : {var} _R_ {var}":
    # elif p == r"{CONDITION_1} : {var} and {var} are in {EX}":
    # elif p == r"{CONDITION_1} : {var} and {var} have equal range":
    # elif p == r"{CONDITION_1} : {var} has _order_ `"Init"`":
    # elif p == r"{CONDITION_1} : {var} is a List of WriteSharedMemory or ReadModifyWriteSharedMemory events":
    # elif p == r"{CONDITION_1} : {var} is a WriteSharedMemory or ReadModifyWriteSharedMemory event":
    # elif p == r"{CONDITION_1} : {var} is an exotic String object":
    # elif p == r"{CONDITION_1} : {var} is an instance of a nonterminal":
    # elif p == r"{CONDITION_1} : {var} is an instance of {var}":
    # elif p == r"{CONDITION_1} : {var} is any ECMAScript language value other than an Object with an? {DSBN} internal slot":
    # elif p == r"{CONDITION_1} : {var} is before {var} in List order of {EX}":
    # elif p == r"{CONDITION_1} : {var} is bound by any syntactic form other than an? {nonterminal}, an? {nonterminal}, the {nonterminal} of a for statement, the {nonterminal} of a for-in statement, or the {nonterminal} of a for-in statement":
    # elif p == r"{CONDITION_1} : {var} is not the Environment Record for a |Catch| clause":
    # elif p == r"{CONDITION_1} : {EX} is not {LITERAL} or {LITERAL}":
    # elif p == r"{CONDITION_1} : {var} is not {var}":
    # elif p == r"{CONDITION_1} : {var} {SAB_RELATION} {var}":
    # elif p == r"{CONDITION_AS_COMMAND} : At least one of {var} or {var} does not have {DSBN} {STR_LITERAL} or {var} and {var} have overlapping ranges.":
    # elif p == r"{CONDITION_AS_COMMAND} : It is not the case that {CONDITION}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : The host provides a {SAB_RELATION} Relation for {DOTTING}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : There is a List of length equal to {DOTTING} of WriteSharedMemory or ReadModifyWriteSharedMemory events {var} such that {PREFIX_PAREN} is {var}.":
    # elif p == r"{CONDITION_AS_COMMAND} : There is no WriteSharedMemory or ReadModifyWriteSharedMemory event {var} in SharedDataBlockEventSet({var}) with equal range as {var} such that {var} is not {var}, {var} {SAB_RELATION} {var}, and {var} {SAB_RELATION} {var}.":
    # elif p == r"{CONDITION_AS_COMMAND} : There is no WriteSharedMemory or ReadModifyWriteSharedMemory event {var} that has {var} in its range such that {CONDITION}.":
    # elif p == r"{CONDITION_AS_COMMAND} : There is no cycle in the union of {SAB_RELATION} and {SAB_RELATION}.":
    # elif p == r"{CONDITION_AS_COMMAND} : {DOTTING} is a strict partial order, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} _R_ {var} or {var} _R_ {var}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} has coherent reads, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} has sequentially consistent atomics.":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} has tear free reads, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} has valid chosen reads, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} has {var} in its range.":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} is equal to {var} and {SETTABLE} is equal to {SETTABLE} for all integer values {var} in the range {NUM_LITERAL} through {var}, exclusive.":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} is not {var}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} is not {var}.":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} {SAB_RELATION} {var} or {var} {SAB_RELATION} {var}.":
    # elif p == r"{CONDITION_AS_COMMAND} : {var} {SAB_RELATION} {var}.":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : it is not the case that {CONDITION}":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : there is no {var} such that {CONDITION}":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : {var} _R_ {var}":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : {var} {SAB_RELATION} {var}":

    else:
        stderr()
        stderr("tc_cond:")
        stderr('    elif p == r"%s":' % p)
        sys.exit(0)

# ------------------------------------------------------------------------------

def tc_logical(logical_structure, env0, asserting):

    def appropriate_function(x):
        if isinstance(x, ANode):
            return tc_cond
        elif isinstance(x, tuple):
            return tc_logical
        else:
            assert 0

    assert isinstance(logical_structure, tuple)
    assert len(logical_structure) == 2
    (operator, operands) = logical_structure
    if operator == 'or':
        # Each cond is type-checked under the assumption that
        # all preceding conditions failed.
        t_envs = []
        f_env = env0
        for cond in operands:
            # If `asserting` is True, that only propagates to the last cond
            # (again, assuming that all previous conditions failed).
            sub_asserting = asserting if (cond is operands[-1]) else False
            (t_env, f_env) = appropriate_function(cond)(cond, f_env, sub_asserting)
            t_envs.append(t_env)
        return ( envs_or(t_envs), f_env )

    elif operator == 'and':
        # Each cond is type-checked under the assumption that
        # all preceding conditions succeeded.
        t_env = env0
        f_envs = []
        for cond in operands:
            (t_env, f_env) = appropriate_function(cond)(cond, t_env, asserting)
            f_envs.append(f_env)
        return ( t_env, envs_or(f_envs) )

    else:
        assert 0

# ------------------------------------------------------------------------------

def tc_expr(expr, env0, expr_value_will_be_discarded=False):
    p = str(expr.prod)
    expr_text = expr.source_text()

    if trace_this_op:
        print()
        print("Entering e:", p)
        print("           ", expr_text)
        mytrace(env0)

    if expr_text in env0.vars:
        if trace_this_op:
            print()
            print("Getting type from cache")
        expr_type = env0.vars[expr_text]
        # stderr("cache: %s :: %s" % (expr_text, expr_type))
        assert isinstance(expr_type, Type)
        env1 = env0

    else:
        (expr_type, env1) = tc_expr_(expr, env0, expr_value_will_be_discarded)

        assert isinstance(expr_type, Type)
        assert isinstance(env1, Env)

        if expr_type in [T_Top_, T_TBD, T_0]:
            add_pass_error(
                expr,
                "warning: expr `%s` has type %s" % (expr_text, expr_type)
            )

    if 0 and not expr_value_will_be_discarded:
        if expr_type != T_Top_ and T_not_returned.is_a_subtype_of_or_equal_to(expr_type):
            add_pass_error(
                expr,
                f"warning: `{p}` could be not_returned"
            )
            # There are a few problems with this:
            # - If a param's type isn't Top_, but has been carved down from Top_,
            #   it will probably include not_returned.
            #   (Mind you, there's a problem there anyway.)
            #
            # - Can't pass expr_value_will_be_discarded=True to assert_expr_is_of_type.
            #   (Only affects "Perform LeaveCriticalSection" step.)
            #
            # - In cases where it actually makes a useful complaint,
            #   it complains at multiple levels.
            #   (But that's okay, because you're going to fix it, right?)

    if trace_this_op:
        print()
        print("Leaving e:", p)
        print("          ", expr_text)
        print(" has type:", expr_type)
        mytrace(env1)

    return (expr_type, env1)

# --------------------

def tc_expr_(expr, env0, expr_value_will_be_discarded):
    p = str(expr.prod)
    children = expr.children

    # stderr('>>>', expr.source_text())

    if p in [
        r"{EXPR} : the result of performing {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the result of {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : {EX}",
        r"{EX} : ({EX})",
        r"{EX} : the previous value of {var}",
        r"{EX} : the value of {SETTABLE}",
        r"{EX} : the {var} flag",
        r"{EX} : {code_unit_lit}",
        r"{EX} : {LITERAL}",
        r"{EX} : {LOCAL_REF}",
        r"{EX} : {NAMED_OPERATION_INVOCATION}",
        r"{EX} : {NUM_EXPR}",
        r"{EX} : {NUM_LITERAL}",
        r"{EX} : {PAIR}",
        r"{EX} : {PP_NAMED_OPERATION_INVOCATION}",
        r"{EX} : {PRODUCT}",
        r"{EX} : {RECORD_CONSTRUCTOR}",
        r"{EX} : {SUM}",
        r"{EX} : {U_LITERAL}",
        r"{EX} : {STR_LITERAL}",
        r"{FACTOR} : ({NUM_EXPR})",
        r"{FACTOR} : ({SUM})",
        r"{FACTOR} : {NAMED_OPERATION_INVOCATION}",
        r"{FACTOR} : {NUM_LITERAL}",
        r"{FACTOR} : {PP_NAMED_OPERATION_INVOCATION}",
        r"{FACTOR} : {SETTABLE}",
        r"{LITERAL} : {code_unit_lit}",
        r"{LITERAL} : {NUM_LITERAL}",
        r"{LOCAL_REF} : {PROD_REF}",
        r"{LOCAL_REF} : {SETTABLE}",
        r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}",
        r"{NUM_COMPARAND} : {FACTOR}",
        r"{NUM_COMPARAND} : {NUM_LITERAL}",
        r"{NUM_COMPARAND} : {PREFIX_PAREN}",
        r"{NUM_COMPARAND} : {SETTABLE}",
        r"{NUM_COMPARAND} : {SUM}",
        r"{NUM_COMPARAND} : {PRODUCT}",
        r"{NUM_EXPR} : {PRODUCT}",
        r"{NUM_EXPR} : {SUM}",
        r"{NUM_EXPR} : {BIT_EX}",
        r"{SETTABLE} : {DOTTING}",
        r"{TERM} : ({PRODUCT})",
        r"{TERM} : {DOTTING}",
        r"{TERM} : {FACTOR}",
        r"{TERM} : {PREFIX_PAREN}",
        r"{TERM} : {PRODUCT}",
        r"{TYPE_ARG} : {DOTTING}",
        r"{TYPE_ARG} : {var}",
    ]:
        [child] = children
        return tc_expr(child, env0, expr_value_will_be_discarded)

    elif p == r"{EXPR} : the CharSet that is {EXPR}":
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_CharSet)
        return (T_CharSet, env1)

    elif p == r"{EXPR} : the Matcher that is {EXPR}":
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Matcher)
        return (T_Matcher, env1)

    # ------------------------------------------------------
    # literals

    elif p in [
        "{LITERAL} : *false*",
        "{LITERAL} : *true*",
    ]:
        return (T_Boolean, env0)

    elif p == r'{LITERAL} : *undefined*':
        return (T_Undefined, env0)

    elif p == r'{LITERAL} : *null*':
        return (T_Null, env0)

    elif p == r"{LITERAL} : {atat_word}":
        return (T_Symbol, env0)    

    elif p == r"{NUM_LITERAL} : &infin;":
        return (T_Infinity_, env0)

    elif p == r"{LITERAL} : {TYPE_NAME}":
        [type_name] = children
        return (T_LangTypeName_, env0)

    elif p in [
        r"{EX} : hint Number",
        r"{EX} : hint String",
    ]:
        [] = children
        return (T_LangTypeName_, env0)

    elif p in [
        r"{LITERAL} : the value *undefined*",
        r"{U_LITERAL} : *undefined*",
    ]:
        [] = children
        return (T_Undefined, env0)

    elif p == r"{LITERAL} : {tilded_word}":
        [tilded_word] = children
        chars = tilded_word.source_text()[1:-1]
        if chars == '[empty]':
            # The spec uses ~[empty]~ to denote
            # what you get when you ask for, e.g.
            # "the second |Expression|",
            # and it's not present.
            return (T_not_in_node, env0)
        elif chars == 'empty':
            return (T_empty_, env0)
        elif chars == 'failure':
            return (T_match_failure_, env0)
        elif chars == 'strict':
            # T_this_mode or T_AssignmentTargetType_, depending on context
            # super-kludge to get context:
            if 'Mode' in spec.text[expr.start_posn-20:expr.start_posn]:
                return (T_this_mode, env0)
            else:
                assert 0 # since PR #1652 was merged
                return (T_AssignmentTargetType_, env0)

        elif chars == 'lexical':
            # T_this_mode or T_this_binding_status_, depending on context
            # super-kludge:
            text = spec.text[expr.start_posn-30:expr.start_posn]
            if 'ThisBindingStatus' in text:
                return (T_this_binding_status_, env0)
            elif 'ThisMode' in text or '_thisMode_' in text:
                return (T_this_mode, env0)
            assert 0, text

        elif chars == 'async':
            # T_IteratorKind_ or T_FunctionKind2_
            text = spec.text[expr.start_posn-32:expr.start_posn]
            if (
                '~non-constructor~' in text
                or
                '_functionPrototype_,' in text
                or
                '_kind_ is' in text
                or
                'DynamicFunction(_C_, NewTarget,' in text
            ):
                return (T_FunctionKind2_, env0)
            elif (
                'State]]' in text
                or
                'GetGeneratorKind()' in text
                or
                '_generatorKind_' in text
                or
                '_iteratorKind_' in text
                or
                '_iteratorHint_' in text
                or
                '~sync~' in text
                or
                '_hint_' in text
                or
                '_labelSet_,' in text
            ):
                return (T_IteratorKind_, env0)

            assert 0, text

        elif chars in ['global']:
            return (T_this_mode, env0)
        elif chars in ['initialized', 'uninitialized']:
            return (T_this_binding_status_, env0)
        elif chars in ['enumerate', 'iterate', 'async-iterate']:
            return (T_IterationKind_, env0)
        elif chars in ['Normal', 'Arrow', 'Method']:
            return (T_FunctionKind1_, env0)
        elif chars in ['assignment', 'varBinding', 'lexicalBinding']:
            return (T_LhsKind_, env0)
        elif chars in ['non-generator', 'async', 'sync']:
            return (T_IteratorKind_, env0)
        elif chars in ['simple', 'invalid']:
            return (T_AssignmentTargetType_, env0)
        elif chars in ['SeqCst', 'Unordered', 'Init']:
            return (T_SharedMemory_ordering_, env0)
        elif chars in ['normal', 'non-constructor', 'classConstructor', 'generator', 'async', 'asyncGenerator']:
            return (T_FunctionKind2_, env0)
        elif chars in ['base', 'derived']:
            return (T_constructor_kind_, env0)
        elif chars in [
            'BigInt64',
            'BigUint64',
            'Float32',
            'Float64',
            'Int16',
            'Int32',
            'Int8',
            'Uint16',
            'Uint32',
            'Uint8',
            'Uint8C',
        ]:
            return (T_TypedArray_element_type_, env0)
        elif chars in ['BigInt', 'Number']:
            return (T_numeric_primitive_type_, env0)
        elif chars in ['suspendedStart', 'suspendedYield', 'executing', 'completed', 'awaiting-return']:
            return (T_generator_state_, env0)
        elif chars in ['start', 'end', 'start+end']:
            return (T_TrimString_where_, env0)
        elif chars in ['key', 'value', 'key+value']:
            return (T_iteration_result_kind_, env0)
        elif chars in ['Fulfill', 'Reject']:
            return (T_settlement_type_, env0)
        elif chars in ['pending', 'fulfilled', 'rejected']:
            return (T_promise_state_, env0)
        elif chars in ['unlinked', 'linking', 'linked', 'evaluating', 'evaluated']:
            return (T_module_record_status_, env0)
        elif chars in ['frozen', 'sealed']:
            return (T_integrity_level_, env0)
        elif chars in ['lexical-this', 'non-lexical-this']:
            return (T_this_mode2_, env0)
        elif chars in ['string', 'symbol']:
            return (T_PropertyKeyKind_, env0)
        elif chars in ['ConstructorMethod', 'NonConstructorMethod']:
            return (T_ClassElementKind_, env0)
        else:
            assert 0, chars

    # --------------------------------------------------------
    # introduce metavariables:

    elif p == r'{EXPR} : {EX}, where {var} is {EX}':
        [exa, var, exb] = children
        (exb_type, env1) = tc_expr(exb, env0); assert env1 is env0
        env2 = env1.plus_new_entry(var, exb_type)
        (exa_type, env3) = tc_expr(exa, env2)
        return (exa_type, env3)

    elif p == r'{EXPR} : {EX}, where {var} is {EX} and {var} is {EX}':
        [ex3, var2, ex2, var1, ex1] = children

        (ex1_type, ex1_env) = tc_expr(ex1, env0); assert ex1_env is env0
        env1 = ex1_env.plus_new_entry(var1, ex1_type)

        (ex2_type, ex2_env) = tc_expr(ex2, env1); assert ex2_env is env1
        env2 = ex2_env.plus_new_entry(var2, ex2_type)

        (ex3_type, ex3_env) = tc_expr(ex3, env2); assert ex3_env is env2
        return (ex3_type, ex3_env)

    elif p in [
        r"{EXPR} : the largest possible nonnegative integer {var} not larger than {var} such that {CONDITION}; but if there is no such integer {var}, return the value {NUM_EXPR}",
        # r"{EXPR} : the smallest possible integer {var} not smaller than {var} such that {CONDITION}; but if there is no such integer {var}, return the value {NUM_EXPR}", # obsoleted by PR 2009
    ]:
        [let_var, limit_var, cond, let_var2, default] = children
        assert same_source_text(let_var2, let_var)
        env0.assert_expr_is_of_type(limit_var, T_Integer_)
        env0.assert_expr_is_of_type(default, T_Integer_)
        env_for_cond = env0.plus_new_entry(let_var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        return (T_Integer_, t_env)

    elif p == r"{EXPR} : the smallest (closest to *-&infin;*) such integer":
        [] = children
        return (T_Integer_, env0)

    # --------------------------------------------------------
    # invocation of named operation:

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : the {ISDO_NAME} of {PROD_REF}",
        r"{NAMED_OPERATION_INVOCATION} : {ISDO_NAME} of {PROD_REF}",
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}",
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} (see {h_emu_xref})",
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}",
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}; if {LOCAL_REF} is not present, use the numeric value zero",
        r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}",
        r"{NAMED_OPERATION_INVOCATION} : the result of performing {cap_word} on {EX}",
    ]:
        [callee, local_ref] = children[0:2]
        callee_op_name = callee.source_text()
        if callee_op_name == 'CodePointToUTF16CodeUnits':
            # An abstract operation that uses SDO-style invocation.
            return tc_ao_invocation(callee_op_name, [local_ref], expr, env0)
        else:
            return tc_sdo_invocation(callee_op_name, local_ref, [], expr, env0)

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} {WITH_ARGS}",
        r"{NAMED_OPERATION_INVOCATION} : {cap_word} for {LOCAL_REF} {WITH_ARGS}",
        r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}",
    ]:
        [callee, local_ref, with_args] = children
        callee_op_name = callee.source_text()
        if with_args.prod.rhs_s in [
            '{PASSING} argument {EX}',
            '{PASSING} arguments {EX} and {EX}',
            '{PASSING} arguments {var}, {var}, and {var}',
            '{PASSING} {EX} as the argument',
            '{PASSING} {var} and {EX} as arguments',
            '{PASSING} {var} and {EX} as the arguments',
            '{PASSING} {var}, {var}, and {var} as the arguments',
        ]:
            args = with_args.children[1:]
        elif with_args.prod.rhs_s == '{PASSING} arguments {EX} and {EX} as the optional {var} argument':
            args = with_args.children[1:3]
        else:
            assert 0, with_args.prod.rhs_s
        return tc_sdo_invocation(callee_op_name, local_ref, args, expr, env0)

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : evaluating {LOCAL_REF}",
        r"{NAMED_OPERATION_INVOCATION} : evaluating {LOCAL_REF}. This may be of type Reference",
    ]:
        [local_ref] = children
        if local_ref.source_text() in [
            '|Assertion|',
            '|AtomEscape|',
            '|Atom|',
            '|CharacterClassEscape|',
            '|CharacterEscape|',
            '|ClassAtomNoDash|',
            '|ClassAtom|',
            '|ClassEscape|',
            '|Disjunction|',
            '|LeadSurrogate|',
            '|NonSurrogate|',
            '|NonemptyClassRanges|'
            '|RegExpUnicodeEscapeSequence|',
            '|TrailSurrogate|',
        ]:
            op_name = 'regexp-Evaluate'
        else:
            op_name = 'Evaluation'
        return tc_sdo_invocation(op_name, local_ref, [], expr, env0)

    elif p == r"{NAMED_OPERATION_INVOCATION} : evaluating {LOCAL_REF} with argument {var}":
        [local_ref, var] = children
        assert local_ref.source_text() in [
            '|Atom|',
            '|AtomEscape|',
            '|Disjunction|',
        ]
        op_name = 'regexp-Evaluate'
        return tc_sdo_invocation(op_name, local_ref, [var], expr, env0)

    elif p == r"{NAMED_OPERATION_INVOCATION} : evaluating {nonterminal} {var}":
        [nont, var] = children
        assert nont.source_text() == '|CaseClause|'
        env0.assert_expr_is_of_type(var, ptn_type_for(nont))
        return tc_sdo_invocation('Evaluation', var, [], expr, env0)

#?    elif p == r"{EXPR} : the result of evaluating {DOTTING}":
#?        [dotting] = children
#?        return tc_sdo_invocation('Evaluation', dotting, [], expr, env0)

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {var}",
        r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {nonterminal}",
    ]:
        [lhs, rhs] = children
        return tc_sdo_invocation('Contains', lhs, [rhs], expr, env0)


    # ------

    elif p in [
        r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})',
        r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT}) (see {h_emu_xref})',
        r"{EXPR} : {OPN_BEFORE_PAREN}({V})",
    ]:
        [opn_before_paren, arglist] = children[0:2]
        if arglist.prod.lhs_s == '{EXLIST_OPT}':
            args = exes_in_exlist_opt(arglist)
        else:
            args = [arglist]

        if opn_before_paren.prod.rhs_s in [
            r'{DOTTING}',
            r'{var}',
        ]:
            [thing] = opn_before_paren.children
            (t, env0) = tc_expr(thing, env0)
            assert isinstance(t, ProcType)
            params = with_fake_param_names(t.param_types)
            return_type = t.return_type

        elif opn_before_paren.prod.rhs_s == r'{var}.{cap_word}':
            [var, cap_word] = opn_before_paren.children
            callee_op_name = cap_word.source_text()

            callee_op = operation_named_[callee_op_name]
            assert callee_op.kind == 'concrete method'

            # XXX If PR #955 is accepted, that will change things around here.

            # When there's a type hierarchy (under Environment Record or Module Record),
            # and sub-types augment the set of types defined at the root,
            # then the use of one of those added methods
            # implies a tighter constraint on the type of the LHS.

            assert len(callee_op.headers) > 0
            forp_types = [
                header.for_param_type
                for header in callee_op.headers
            ]
            if callee_op_name in ['Link', 'Evaluate']:
                # These are abstract methods of all Module Records,
                # but the spec only has definitions for Cyclic Module Records.
                forp_types.append(T_other_Module_Record)
            elif callee_op_name in ['GetExportedNames', 'ResolveExport']:
                # These are abstract methods of all Module Records,
                # but the spec only has definitions for Source Text Module Records.
                forp_types.append(T_other_Module_Record)
                forp_types.append(T_other_Cyclic_Module_Record)
            elif callee_op_name in ['InitializeEnvironment', 'ExecuteModule']:
                # These are abstract methods of all Cyclic Module Records,
                # but the spec only has definitions for Source Text Module Records.
                forp_types.append(T_other_Cyclic_Module_Record)

            union_of_forp_types = union_of_types(forp_types)

            env0 = env0.ensure_expr_is_of_type(var, union_of_forp_types)

            params = callee_op.parameters_with_types
            return_type = callee_op.return_type

        elif opn_before_paren.prod.rhs_s == r'{NUMERIC_TYPE_INDICATOR}::{low_word}':
            [num_type_indicator, low_word] = opn_before_paren.children

            nti = num_type_indicator.source_text()
            if nti in [ 'Number', 'BigInt']:
                for_type = NamedType(nti)
            else:
                # hack for now
                opn = low_word.source_text()
                if opn in [
                    'sameValue',
                    'sameValueZero',
                    'equal',
                    'lessThan',
                ]:
                    return (T_Boolean, env0)
                elif opn in [
                    'add',
                    'bitwiseAND',
                    'bitwiseNOT',
                    'bitwiseOR',
                    'bitwiseXOR',
                    'divide',
                    'exponentiate',
                    'leftShift',
                    'multiply',
                    'remainder',
                    'signedRightShift',
                    'subtract',
                    'unaryMinus',
                    'unsignedRightShift',
                ]:
                    return (T_Number|T_BigInt, env0)
                assert 0, expr.source_text()

            callee_op_name = '::' + low_word.source_text()
            callee_op = operation_named_[callee_op_name]
            assert callee_op.kind == 'numeric method'
            assert len(callee_op.headers) == 2

            for header in callee_op.headers:
                if for_type is None or header.for_param_type == for_type:
                    params = header.parameter_types.items()
                    return_type = header.return_type
                    break
            else:
                assert 0

        else:
            callee_op_name = opn_before_paren.source_text()

            if callee_op_name == 'NormalCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = arg_type
                return (return_type, env0)
                # don't call tc_args etc

            elif callee_op_name == 'ThrowCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = ThrowType(arg_type)
                return (return_type, env0)

            elif callee_op_name == 'Completion':
                assert len(args) == 1
                [arg] = args
                (arg_type, env1) = tc_expr(arg, env0)
                return_type = arg_type # bleah
                return (return_type, env1)

            elif callee_op_name == 'Await':
                assert len(args) == 1
                [arg] = args
                env0.assert_expr_is_of_type(arg, T_Tangible_|T_empty_)
                return (T_Tangible_|T_empty_|T_return_|T_throw_, env0)

            elif callee_op_name in ['floor', 'abs']:
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                assert arg_type.is_a_subtype_of_or_equal_to(T_Number)
                if callee_op_name == 'floor':
                    return_type = T_Integer_
                elif callee_op_name == 'abs':
                    return_type = arg_type
                else:
                    assert 0
                return (return_type, env0)

            elif callee_op_name in ['min', 'max']:
                assert len(args) == 2
                env1 = env0
                for arg in args:
                    env1 = env1.ensure_expr_is_of_type(arg, T_Number)
                return (T_Integer_, env1)

            elif callee_op_name in [
                # 30232 Day Number and Time within Day
                'Day',
                'TimeWithinDay',

                # 30264 Month Number
                'MonthFromTime',

                # 30286 Date Number
                'DateFromTime',

                # 30305 Week Day
                'WeekDay',

                # 30424 Year Number
                'YearFromTime',

                # 30376 Hours, Minutes, Second, and Milliseconds
                'HourFromTime',
                'MinFromTime',
                'SecFromTime',
                'msFromTime',

                # 'DaylightSavingTA',
            ]:
                assert len(args) == 1
                [arg] = args
                env0.ensure_expr_is_of_type(arg, T_Number)
                return_type = T_Integer_
                return (return_type, env0)

            # ---------------

            else:
                callee_op = operation_named_[callee_op_name]
                if callee_op.kind == 'syntax-directed operation':
                    add_pass_error(
                        expr,
                        "Unusual to invoke a SDO via prefix-paren notation: " + expr.source_text()
                    )
                    assert len(args) == 1
                    return tc_sdo_invocation(callee_op_name, args[0], [], expr, env0)
                else:
                    assert callee_op.kind in ['abstract operation', 'host-defined abstract operation']
                params = callee_op.parameters_with_types
                return_type = callee_op.return_type
                # fall through to tc_args etc

                # if callee_op_name == 'ResolveBinding': pdb.set_trace()

        # context = 'in call to `%s`' % opn_before_paren.source_text()
        env2 = tc_args(params, args, env0, expr)
        return (return_type, env2)

    # -----

    elif p == r"{NAMED_OPERATION_INVOCATION} : Strict Equality Comparison {var} === {EX}":
        [lhs, rhs] = children
        return tc_ao_invocation('Strict Equality Comparison', [lhs, rhs], expr, env0)

    elif p in [
        r"{EXPR} : the result of the comparison {EX} == {EX}",
        r"{NAMED_OPERATION_INVOCATION} : Abstract Equality Comparison {var} == {var}",
    ]:
        [lhs, rhs] = children
        return tc_ao_invocation('Abstract Equality Comparison', [lhs, rhs], expr, env0)

    elif p == r"{NAMED_OPERATION_INVOCATION} : Abstract Relational Comparison {var} &lt; {var}":
        [lhs, rhs] = children
        return tc_ao_invocation('Abstract Relational Comparison', [lhs, rhs], expr, env0)

    elif p == r"{NAMED_OPERATION_INVOCATION} : Abstract Relational Comparison {var} &lt; {var} with {var} equal to {LITERAL}":
        [lhs, rhs, param, lit] = children
        return tc_ao_invocation('Abstract Relational Comparison', [lhs, rhs, lit], expr, env0)

    # --------------------------------------------------------

    elif p == r"{SETTABLE} : the {DSBN} field of {EXPR}":
        [dsbn, ex] = children
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name == 'EventList':
            env0.assert_expr_is_of_type(ex, T_Agent_Events_Record)
            return (ListType(T_event_), env0)
        elif dsbn_name == 'CandidateExecution':
            env0.assert_expr_is_of_type(ex, T_Agent_Record)
            return (T_candidate_execution, env0)
        elif dsbn_name == 'LittleEndian':
            env0.assert_expr_is_of_type(ex, T_Agent_Record)
            return (T_Boolean, env0)
        else:
            assert 0, expr

    elif p in [
        r'{DOTTING} : {var}.{DSBN}',
        r"{DOTTING} : {DOTTING}.{DSBN}",
    ]:
        [lhs_var, dsbn] = children
        lhs_text = lhs_var.source_text()
        dsbn_name = dsbn.source_text()[2:-2]
        (lhs_t, env1) = tc_expr(lhs_var, env0)

        # assert dsbn_name != 'Type'
        # because anything involving [[Type]] has been intercepted at a higher level
        # Nope, _reaction_.[[Type]]

        # ----------------------------------

        # Handle "Completion Records" specially.
        while True: # ONCE
            if dsbn_name not in ['Type', 'Target', 'Value']:
                # We can't be dealing with a Completion Record
                break
            if lhs_t in [
                T_ImportMeta_record_,
                T_MapData_record_,
                T_PromiseReaction_Record,
                T_Property_Descriptor,
                T_boolean_value_record_,
                T_integer_value_record_,
            ]:
                # We know we're not dealing with a Completion Record
                break

            assert lhs_text not in [
                '_D_',
                '_Desc_',
                '_alreadyResolved_',
                '_current_',
                '_desc_',
                '_like_',
                '_newLenDesc_',
                '_oldLenDesc_',
                '_reaction_',
                '_remainingElementsCount_',
            ]

            result_memtypes = set()
            for memtype in lhs_t.set_of_types():
                if dsbn_name == 'Value':
                    # Lots of things have a '[[Value]]' field.
                    if memtype.is_a_subtype_of_or_equal_to(T_Abrupt):
                        result_memtype = T_Tangible_ | T_empty_
                    elif memtype == T_Normal:
                        result_memtype = T_Tangible_ | T_empty_
                    elif memtype.is_a_subtype_of_or_equal_to(T_Tangible_ | T_empty_):
                        result_memtype = memtype

                    elif memtype.is_a_subtype_of_or_equal_to(T_Reference):
                        # Completion Record's [[Value]] can be a Reference, despite the definition of CR?
                        result_memtype = memtype
                    elif memtype == T_Realm_Record:
                        # GetFunctionRealm can supposedly return a Completion Record whose [[Value]] is a Realm Record, despite the definition of CR
                        result_memtype = memtype
                    elif memtype in [T_not_returned, ListType(T_code_unit_), T_Top_]:
                        # hm.
                        result_memtype = memtype
                    elif memtype.is_a_subtype_of_or_equal_to(T_Private_Name):
                        result_memtype = T_function_object_
                    elif memtype == T_Record:
                        # All we know is that it's a Record with a [[Value]] field.
                        result_memtype = T_TBD
                    else:
                        assert 0, memtype

                elif dsbn_name == 'Target':
                    if memtype in [T_continue_, T_break_, T_Abrupt]:
                        result_memtype = T_String | T_empty_
                    elif memtype == T_throw_:
                        result_memtype = T_empty_
                    elif memtype in [T_TBD, T_Top_]:
                        result_memtype = T_String | T_empty_
                    elif memtype in [T_Tangible_, T_empty_]:
                        result_memtype = T_empty_
                    elif memtype in [T_Reference, T_not_returned, ListType(T_code_unit_)]:
                        # hm.
                        result_memtype = T_empty_
                    else:
                        assert 0, memtype

                elif dsbn_name == 'Type':
                    assert 0

                else:
                    assert 0

                result_memtypes.add(result_memtype)

            result_type = union_of_types(result_memtypes)
            return (result_type, env1)

        # Finished with "Completion Records"
        # ----------------------------------

        # In some cases, we first need to change the type of lhs_var...

        if lhs_t == T_0:
            if lhs_text == '_starResolution_':
                # ResolveExport _starResolution_
                # The first time through the For loop,
                # _starResolution has type Null,
                # so after "If _starResolution_ is *null*,",
                # in the Else branch it has type T_0.
                # Properly, that should make us not do STA on the Else branch,
                # then we would re-STA the loop-body
                # with a wider type for _starResolution_.
                # But I'm hoping to avoid the need to re-STA loop-bodies.
                lhs_t = T_ResolvedBinding_Record
            elif lhs_text == '_received_':
                # Similar to the above,
                # in Evaluation of YieldExpression
                lhs_t = T_Tangible_ | T_throw_ # ?
            elif lhs_text == '_declResult_':
                # EvaluateBody: See Issue 837
                lhs_t = T_throw_
            else:
                assert 0, expr.source_text()
            add_pass_error(
                expr,
                "`%s` has type T_0, changing to %s" % (lhs_text, lhs_t)
            )
            env2 = env1

        elif lhs_t == T_Property_Descriptor | T_Undefined:
            # CreateGlobalFunctionBinding:
            # If _existingProp_ is *undefined* or _existingProp_.[[Configurable]] is *true*
            lhs_t = T_Property_Descriptor
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t in [
            T_Object | T_Boolean | T_Environment_Record | T_Number | T_String | T_Symbol | T_Undefined,
            T_Object | T_Null,
            T_Object | T_Undefined,
        ]:
            # GetValue. (Fix by replacing T_Reference with ReferenceType(base_type)?)
            lhs_t = T_Object
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Realm_Record | T_Undefined:
            lhs_t = T_Realm_Record
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t in [
            T_TBD,
            T_Top_,
            T_Tangible_,
            T_Normal,
            T_empty_,
            T_Tangible_ | T_empty_,
            T_Tangible_ | T_empty_ | T_Abrupt,
        ]:
            # Have to peek at the dsbn to infer the type of the lhs_var.

            candidate_type_names = []

            for (record_type_name, fields) in sorted(fields_for_record_type_named_.items()):
                if dsbn_name in fields:
                    candidate_type_names.append(record_type_name)

            if dsbn_name in type_of_internal_thing_:
                candidate_type_names.append('Object')
                # But we could sometimes be more specific about the kind of Object:
                # 'PromiseState'    : Promise Instance object
                # 'TypedArrayName'  : Integer Indexed object
                # 'GeneratorState'  : Generator Instance
                # 'OriginalSource'  : RegExp Instance
                # 'GeneratorContext': Generator Instance

            if dsbn_name == 'Realm':
                assert candidate_type_names == ['Cyclic Module Record', 'Job_record_', 'Module Record', 'Script Record', 'Source Text Module Record', 'other Module Record', 'Object']
                if lhs_text == '_scriptRecord_':
                    lhs_t = T_Script_Record
                elif lhs_text == '_module_':
                    lhs_t = T_Source_Text_Module_Record
                else:
                    assert 0
            elif dsbn_name == 'Status':
                assert candidate_type_names == ['Module Record', 'Source Text Module Record', 'other Module Record']
                assert lhs_text == '_module_'
                lhs_t = T_Module_Record
            elif dsbn_name == 'Done':
                assert candidate_type_names == ['iterator_record_', 'Object']
                assert lhs_text == '_iteratorRecord_'
                lhs_t = T_iterator_record_
            elif dsbn_name in ['Reject', 'Resolve']:
                assert candidate_type_names == ['PromiseCapability Record', 'ResolvingFunctions_record_']
                assert lhs_text == '_promiseCapability_'
                lhs_t = T_PromiseCapability_Record
            elif dsbn_name == 'Promise':
                assert candidate_type_names == ['PromiseCapability Record', 'Object']
                assert lhs_text == '_promiseCapability_'
                lhs_t = T_PromiseCapability_Record
            else:
                assert len(candidate_type_names) == 1, (dsbn_name, candidate_type_names)
                [type_name] = candidate_type_names
                lhs_t = parse_type_string(type_name)

            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        else:
            env2 = env1

        # --------------------------------------------

        if lhs_t.is_a_subtype_of_or_equal_to(T_Object):
            # _foo_.[[Bar]] references an object's internal method or internal slot.
            assert dsbn_name in type_of_internal_thing_, dsbn_name
            it_type = type_of_internal_thing_[dsbn_name]
            # XXX We should require that lhs_t is allowed to have this internal thing.

            # But for some subtypes of Object, we can give a narrower type for the slot
            if lhs_t == T_SharedArrayBuffer_object_ and dsbn_name == 'ArrayBufferData':
                narrower_type = T_Shared_Data_Block
                assert narrower_type.is_a_subtype_of_or_equal_to(it_type)
                assert narrower_type != it_type
                it_type = narrower_type
            return (it_type, env2)

        elif lhs_t == T_Symbol:
            assert dsbn_name == 'Description'
            return (T_String | T_Undefined, env2)

        elif lhs_t.is_a_subtype_of_or_equal_to(T_Abrupt):
            # Handle "Completion Records" specially.
            t = {
                'Value'  : T_Tangible_ | T_empty_,
                'Target' : T_String | T_empty_,
            }[dsbn_name]
            return (t, env2)

        elif lhs_t.is_a_subtype_of_or_equal_to(T_Record):
            # _foo_.[[Bar]] references a record's field
            if isinstance(lhs_t, NamedType):
                if lhs_t.name == 'Record':
                    add_pass_error(
                        expr,
                        "type of `%s` is only 'Record', so don't know about a `%s` field"
                        % (lhs_text, dsbn_name)
                    )
                    for record_type_name in [
                        'Property Descriptor', # for the almost-Property Descriptor in CompletePropertyDescriptor
                        'iterator_record_',
                        'templateMap_entry_',
                        'methodDef_record_',
                        'CodePointAt_record_',
                        'Job_record_',
                        'FinalizationRegistryCellRecord_',
                    ]:
                        pd_fields = fields_for_record_type_named_[record_type_name]
                        if dsbn_name in pd_fields:
                            field_type = pd_fields[dsbn_name]
                            break
                    else:
                        assert 0, dsbn_name
                        # Need to add something to fields_for_record_type_named_?
                elif lhs_t.name == 'Intrinsics Record':
                    field_type = {
                        '%Array%'               : T_constructor_object_,
                        # '%FunctionPrototype%' : T_Object,
                        '%Function.prototype%'  : T_Object,
                        # '%ObjectPrototype%'   : T_Object,
                        '%Object.prototype%'    : T_Object,
                        '%ThrowTypeError%'      : T_function_object_,
                    }[dsbn_name]
                else:
                    assert lhs_t.name in fields_for_record_type_named_, lhs_t.name
                    fields_info = fields_for_record_type_named_[lhs_t.name]
                    if dsbn_name in fields_info:
                        field_type = fields_info[dsbn_name]
                    else:
                        add_pass_error(
                            expr,
                            "STA can't confirm that `%s` has a `%s` field"
                            % (lhs_text, dsbn_name)
                        )

                        field_type = {
                            (T_Environment_Record, 'NewTarget')        : T_Object | T_Undefined,
                            (T_Module_Record,      'DFSAncestorIndex') : T_Integer_,
                            (T_Module_Record,      'DFSIndex')         : T_Integer_ | T_Undefined,
                            (T_Module_Record,      'EvaluationError')  : T_throw_ | T_Undefined,
                        }[(lhs_t, dsbn_name)]
                        # KeyError here might mean you need to add something to
                        # fields_for_record_type_named_

                return (field_type, env2)

            elif isinstance(lhs_t, UnionType):
                types_for_field = set()
                for mt in lhs_t.member_types:
                    fields_info = fields_for_record_type_named_[mt.name]
                    assert dsbn_name in fields_info
                    field_type = fields_info[dsbn_name]
                    types_for_field.add(field_type)
                assert len(types_for_field) == 1
                field_type = types_for_field.pop()
                return (field_type, env2)

            else:
                assert 0, (expr.source_text(), lhs_t)

        else:
            assert 0, (expr.source_text(), str(lhs_t))

    # -------------------------------------------------

    elif p == r"{EXPR} : {EX} if {CONDITION}. Otherwise, it is {EXPR}":
        [exa, cond, exb] = children
        (t_env, f_env) = tc_cond(cond, env0)
        (ta, enva) = tc_expr(exa, t_env)
        (tb, envb) = tc_expr(exb, f_env)
        return (ta | tb, env_or(enva, envb))

    # -------------------------------------------------
    # return T_BigInt

    elif p == r"{NUM_LITERAL} : {starred_bigint_lit}":
        return (T_BigInt, env0)

    elif p == r"{EXPR} : the BigInt value that represents {EX}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathReal_|T_BigInt)
        return (T_BigInt, env0)

    elif p == r"{EXPR} : the BigInt value that corresponds to {var}":
        [var] = children    
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_BigInt, env0)

    # -------------------------------------------------
    # return T_Number

    elif p == r"{NUM_LITERAL} : {starred_int_lit}":
        return (T_Integer_, env0)

    elif p in [
        r"{NUM_LITERAL} : {starred_nonfinite_lit}",
        r'{NUM_LITERAL} : the *NaN* Number value',
        r"{NUM_LITERAL} : 8.64",
        r"{NUM_LITERAL} : 0.5",
    ]:
        return (T_Number, env0)

    elif p == r'{EXPR} : the Number value that corresponds to {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_ | T_IEEE_binary64_ | T_Integer_)
        return (T_Number, env1)

    elif p == r"{EX} : the Number value for {EX}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the number value that is the same sign as {var} and whose magnitude is {EX}",
        r"{EXPR} : the Number value that is the same sign as {var} and whose magnitude is {EX}",
    ]:
        [var, ex] = children
        env0.assert_expr_is_of_type(var, T_Number)
        env0.assert_expr_is_of_type(ex, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the Element Size value specified in {h_emu_xref} for Element Type {var}",
        r"{EXPR} : the Element Size specified in {h_emu_xref} for Element Type {var}",
        # r"{EXPR} : the Number value of the Element Size specified in {h_emu_xref} for Element Type {var}",
        # r"{EXPR} : the Number value of the Element Size value specified in {h_emu_xref} for Element Type {var}",
    ]:
        [emu_xref, var] = children
        assert var.source_text() in ['_type_', '_srcType_']
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type_)
        return (T_Integer_, env1)

    elif p in [
        r"{EXPR} : the Element Size value specified in {h_emu_xref} for {var}",
        r"{EXPR} : the Element Size value in {h_emu_xref} for {var}",
        # r"{EXPR} : the Number value of the Element Size value in {h_emu_xref} for {var}",
        # r"{EXPR} : the Number value of the Element Size value specified in {h_emu_xref} for {var}",
    ]:
        [emu_xref, var] = children
        assert var.source_text() in ['_constructorName_', '_srcName_', '_arrayTypeName_', '_targetName_', '_typedArrayName_', '_srcType_']
        # print(p, var.source_text(), file=sta_misc_f)
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : {var} `*` msPerHour `+` {var} `*` msPerMinute `+` {var} `*` msPerSecond `+` {var}, performing the arithmetic according to IEEE 754-2019 rules (that is, as if using the ECMAScript operators `*` and `+`)":
        for var in children:
            env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of forming the value of the |NumericLiteral|":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the Number value represented by {nonterminal} as defined in {h_emu_xref}":
        [nont, emu_xref] = children
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of adding the value {NUM_LITERAL} to {var}, using the same rules as for the `+` operator (see {h_emu_xref})",
        r"{EXPR} : the result of subtracting the value {NUM_LITERAL} from {var}, using the same rules as for the `-` operator (see {h_emu_xref})"
    ]:
        [num_lit, var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of negating {var}; that is, compute a Number with the same magnitude but opposite sign",
        r"{EXPR} : the result of applying bitwise complement to {var}. The result is a signed 32-bit integer",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of applying the addition operation to {var} and {var}. See the Note below {h_emu_xref}",
        r"{EXPR} : the result of applying the subtraction operation to {var} and {var}. See the note below {h_emu_xref}",        
    ]:
        [avar, bvar, emu_xref] = children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of {h_emu_xref} with {var} and {var} as specified in {h_emu_xref}":
        [emu_xrefa, avar, bvar, emu_xrefb] = children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of applying the {nonterminal} (`*`, `/`, or `%`) to {var} and {var} as specified in {h_emu_xref}, {h_emu_xref}, or {h_emu_xref}":
        [nonterminal, avar, bvar, *emu_xrefs] = children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of left shifting {var} by {var} bits. The result is a signed 32-bit integer",
        r"{EXPR} : the result of performing a sign-extending right shift of {var} by {var} bits. The most significant bit is propagated. The result is a signed 32-bit integer",
        r"{EXPR} : the result of performing a zero-filling right shift of {var} by {var} bits. Vacated bits are filled with zero. The result is an unsigned 32-bit integer",
        r"{EXPR} : the result of applying the bitwise operator @ to {var} and {var}. The result is a signed 32-bit integer",
    ]:
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Integer_)
        env0.assert_expr_is_of_type(bvar, T_Integer_)
        return (T_Number, env0)

    elif p == r"{EXPR} : the Number value that results from rounding {EX} as described below":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_Number, env0)

    # --------------------------------------------------------
    # return T_MathInteger_

    elif p == r"{EXPR} : {FACTOR} (a value so large that it will round to *+&infin;*)":
        [factor] = children
        return (T_MathInteger_, env0)

    elif p in [
        u"{EX} : \\d+{h_sub_math_r}",
        u"{FACTOR} : \\d+{h_sub_math_r}",
        u"{BASE} : 10{h_sub_math_r}",
        u"{FACTOR} : 0x[0-9A-F]+{h_sub_math_r}",
    ]:
        [_] = children
        return (T_MathInteger_, env0)

    elif p in [
        "{FACTOR} : {math_r}({var})",
        "{NUM_EXPR} : {math_r}({var})",
    ]:
        [_, var] = children
        (var_t, env1) = tc_expr(var, env0); assert env1 is env0
        if var_t.is_a_subtype_of_or_equal_to(T_Integer_):
            return (T_MathInteger_, env0)
        elif var_t.is_a_subtype_of_or_equal_to(T_Number):
            return (T_MathReal_, env0)
        else:
            assert 0, var_t

    elif p == r"{PRODUCT} : -{h_sub_math_r}{var}":
        [_, var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p in [
        r"{EXPR} : the mathematical integer number of code points in {PROD_REF}",
        r"{EX} : the mathematical integer number of code points in {PROD_REF}",
        r"{EX} : the mathematical value of the number of code points in {PROD_REF}",
    ]:
        [prod_ref] = children
        return (T_MathInteger_, env0)

    elif p == r"{EX} : {var} rounded towards 0 to the next integral value":
        [var] = children    
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_MathInteger_, env0)

    elif p == r"{EX} : the mathematical value of {var} raised to the power {var}":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_BigInt)
        env0.assert_expr_is_of_type(b, T_BigInt)
        return (T_MathInteger_, env0)

    elif p == r"{PRODUCT} : {FACTOR} &divide; {FACTOR}, rounding down to the nearest integer, including for negative numbers":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_BigInt)
        env0.assert_expr_is_of_type(b, T_BigInt)
        return (T_MathInteger_, env0)

    elif p in [
        r"{NUM_LITERAL} : {dec_int_lit}{h_sub_math_r}",
        r"{NUM_LITERAL} : {hex_int_lit}{h_sub_math_r}",
    ]:
        [int_lit, _] = children
        return (T_MathInteger_, env0)

    elif p == r"{BASE} : 10{h_sub_math_r}":
        [_] = children
        return (T_MathInteger_, env0)

    elif p == r"{EX} : the integer represented by the 32-bit two's complement bit string {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_) # bit string
        return (T_MathInteger_, env0)

    elif p == r"{EX} : the mathematical value of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number|T_BigInt)
        return (T_MathReal_, env0)

    # --------------------------------------------------------
    # return T_MathReal_

    elif p in [
        u"{PRODUCT} : {FACTOR} &times;{h_sub_math_r} {FACTOR}",
        u"{SUM} : {var}-{h_sub_math_r}{var}",
        u"{SUM} : {TERM} -{h_sub_math_r} {TERM}",
    ]:
        [left, _, right] = children
        env0.assert_expr_is_of_type(left, T_MathReal_)
        env0.assert_expr_is_of_type(right, T_MathReal_)
        return (T_MathReal_, env0)

    # BigInt
    elif p == r"{EX} : the mathematical value of {var} divided by {var}":
        [left, right] = children
        env0.assert_expr_is_of_type(left, T_BigInt)
        env0.assert_expr_is_of_type(right, T_BigInt)
        return (T_MathReal_, env0)

    elif p in [
        r'{EXPR} : the negative of {EX}',
    ]:
        [ex] = children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t == T_TBD or ex_t == T_MathInteger_
        return (ex_t, env0)

    # --------------------------------------------------------
    # return T_Integer_: The size of some collection:

    elif p in [
        r"{NUM_COMPARAND} : the length of {var}",
        r"{EXPR} : the length of {var}",
        r"{EXPR} : the number of code units in {var}",
        r"{TERM} : the number of code units in {var}",
        r"{EXPR} : the number of code unit elements in {var}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the number of characters contained in {var}",
        r"{EXPR} : the number of elements in the List {var}",
        r"{EX} : the number of elements in {var}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the number of elements in {var}'s _captures_ List":
        [var] = children
        env0.assert_expr_is_of_type(var, T_State)
        return (T_Integer_, env0)

    elif p in [
        r'{EX} : the number of code points in {PROD_REF}',
        r"{EXPR} : the number of code points in {PROD_REF}",
    ]:
        [prod_ref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the number of bytes in {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block | T_Shared_Data_Block)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the array size":
        # only once, in Encode()
        [] = children
        return (T_Integer_, env0)

    # ----
    # return T_Integer_: arithmetic:

    elif p == r"{EXPR} : the result of masking out all but the least significant 5 bits of {var}, that is, compute {var} &amp; {hex_int_lit}":
        [var, var2, _] = children
        assert var.children == var2.children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the numeric value 1",
        r"{EX} : [0-9]+",
        r"{FACTOR} : 0x[0-9A-F]+",
        r"{FACTOR} : [0-9]+",
        r"{NUM_COMPARAND} : -6",
        r"{NUM_LITERAL} : {hex_int_lit}",
        r"{NUM_LITERAL} : {dec_int_lit}",
        r"{NUM_LITERAL} : *[+-]0*",
        r"{NUM_LITERAL} : zero",
        r"{BASE} : 10",
        r"{BASE} : 2",
    ]:
        # [] = children
        return (T_Integer_, env0)

#    elif p == r'{FACTOR} : 10<sup>{EX}</sup>':
#        [ex] = children
#        (t, env1) = tc_expr(ex, env0); assert env1 is env0
#        if t == T_TBD:
#            pass
#        else:
#            assert t.is_a_subtype_of_or_equal_to(T_Integer_)
#        return (T_Integer_, env0) # unless EX is negative!

    elif p in [
        r"{FACTOR} : {BASE}<sup>{NUM_LITERAL}</sup>",
        r"{FACTOR} : {BASE}<sup>{NUM_EXPR}</sup>",
        r"{FACTOR} : {BASE}<sup>{var}</sup>",
        r"{FACTOR} : {BASE}<sup>{EX}</sup>",
    ]:
        [base, exponent] = children
        (base_t, env1) = tc_expr(base, env0); assert env1 is env0
        if base_t == T_Integer_:
            env0.assert_expr_is_of_type(exponent, T_Number)
        elif base_t == T_MathInteger_:
            env0.assert_expr_is_of_type(exponent, T_MathReal_)
        else:
            assert 0, base_t
        return (base_t, env0) # XXX unless exponent is negative

    elif p == r"{EX} : the remainder of dividing {EX} by {EX}":
        [aex, bex] = children
        env0.assert_expr_is_of_type(aex, T_Integer_)
        env0.assert_expr_is_of_type(bex, T_Integer_)
        return (T_Integer_, env0)

    elif  p == r"{BIT_EX} : {FACTOR} {BIT_OPERATOR} {FACTOR}":
        [numa, op, numb] = children
        env0.assert_expr_is_of_type(numa, T_Integer_)
        env0.assert_expr_is_of_type(numb, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the mathematical value that is the same sign as {var} and whose magnitude is floor(abs({var}))":
        [var1, var2] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_Number)
        return (T_Integer_, env0)

    elif p == r"{PRODUCT} : {FACTOR} modulo {FACTOR}":
        [factor1, factor2] = children
        #
        env0.assert_expr_is_of_type(factor2, T_Integer_)
        #
        (factor1_t, env1) = tc_expr(factor1, env0); assert env1 is env0
        if factor1_t.is_a_subtype_of_or_equal_to(T_Number):
            return (T_Integer_, env0)
        elif factor1_t == T_BigInt:
            return (T_BigInt, env0)
        else:
            assert 0, factor1_t

    elif p == r"{NUM_LITERAL} : (2|10)<sup>[0-9]+</sup>":
        [_] = children
        return (T_Integer_, env0)

    # ----

    elif p in [
        r"{NUM_COMPARAND} : the numeric value of {var}",
        r"{EX} : the numeric value of {EX}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the integer that is {EXPR}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (T_Integer_, env0)

    # ----

    elif p in [
        r'{EXPR} : the character value of character {var}',
        r"{EXPR} : {var}'s character value",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_Integer_, env0)

    elif p == r"{EX} : the code point value of {nonterminal}":
        [nont] = children
        assert nont.source_text() == '|SourceCharacter|'
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the code point value of {code_point_lit}",
        r"{EXPR} : the code point value of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the code point value of {var}",
        r"{EXPR} : {var}'s code point value",
    ]:
        [x] = children
        env1 = env0.ensure_expr_is_of_type(x, T_code_point_)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the code point value according to {h_emu_xref}":
        return (T_Integer_, env0)

    elif p == r'{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of a binary little-endian two's complement number of bit length {PRODUCT}":
        [var, product] = children
        env1 = env0.ensure_expr_is_of_type(product, T_Integer_ | T_Number); assert env1 is env0
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_Integer_, env1)

    elif p in [
        r"{EX} : {var}'s _endIndex_",
        r"{EX} : {var}'s _endIndex_ value",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the value at index {var} within {var}":
        # only once, in Encode()
        [index_var, list_var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_Integer_))
        env0.assert_expr_is_of_type(index_var, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the index into {var} of the character that was obtained from element {var} of {var}":
        [list_var, index_var, str_var] = children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(index_var, T_Integer_)
        env0.assert_expr_is_of_type(str_var, T_String) # todo: element of String
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the number of left-capturing parentheses in the entire regular expression that occur to the left of {PROD_REF}. This is the total number of {h_emu_grammar} Parse Nodes prior to or enclosing {PROD_REF}",
        r"{EXPR} : the number of left-capturing parentheses in {PROD_REF}. This is the total number of {h_emu_grammar} Parse Nodes enclosed by {PROD_REF}",
    ]:
        [prod_ref, emu_grammar, prod_ref2] = children
        assert same_source_text(prod_ref, prod_ref2)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the 8-bit value represented by the two hexadecimal digits at index {EX} and {EX}":
        [posa, posb] = children
        env0.assert_expr_is_of_type(posa, T_Integer_)
        env0.assert_expr_is_of_type(posb, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the value obtained by applying the UTF-8 transformation to {var}, that is, from a List of octets into a 21-bit value":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_Integer_))
        return (T_Integer_, env0)

    # ----

    elif p in [
        r"{EXPR} : the result of applying the bitwise AND operation to {var} and {var}",
        r"{EXPR} : the result of applying the bitwise exclusive OR (XOR) operation to {var} and {var}",
        r"{EXPR} : the result of applying the bitwise inclusive OR operation to {var} and {var}",
    ]:
        [x, y] = children
        env0.assert_expr_is_of_type(x, T_Integer_) # "bit string"
        env0.assert_expr_is_of_type(y, T_Integer_) # "bit string"
        return (T_Integer_, env0) # "bit string"

    elif p == r"{EXPR} : the 32-bit two's complement bit string representing the mathematical value of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Integer_, env0) # bit string

    # -------------------------------------------------
    # return MathReal_ or MathInteger_ or Number or Integer_ (arithmetic)

    elif p in [
        r'{SUM} : {TERM} {SUM_OPERATOR} {TERM}',
        r"{SUM} : {SUM} {SUM_OPERATOR} {TERM}",
        r'{PRODUCT} : {FACTOR} {PRODUCT_OPERATOR} {FACTOR}',
    ]:
        [a, op, b] = children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        (b_t, env1) = tc_expr(b, env0); assert env1 is env0

        if a_t == T_MathReal_ or b_t == T_MathReal_:
            env0.assert_expr_is_of_type(a, T_MathReal_)
            env0.assert_expr_is_of_type(b, T_MathReal_)
            return (T_MathReal_, env0)

        elif a_t == T_MathInteger_ or b_t == T_MathInteger_:
            env1 = env0.ensure_expr_is_of_type(a, T_MathInteger_)
            env2 = env1.ensure_expr_is_of_type(b, T_MathInteger_)
            return (T_MathInteger_, env2)

        elif a_t == T_code_unit_ and b_t == T_Integer_:
            assert op.source_text() == '-'
            return (T_Integer_, env0)

        elif a_t == T_Number or b_t == T_Number:
            env0.assert_expr_is_of_type(a, T_Number)
            env0.assert_expr_is_of_type(b, T_Number)
            return (T_Number, env0)

        elif a_t == T_BigInt and b_t == T_BigInt:
            return (T_BigInt, env0)

        elif a_t == T_BigInt and b_t == T_Integer_:
            return (T_BigInt, env0)

        elif a_t == T_Integer_ or b_t == T_Integer_:
            env1 = env0.ensure_expr_is_of_type(a, T_Integer_)
            env2 = env1.ensure_expr_is_of_type(b, T_Integer_)
            return (T_Integer_, env2)

        else:
            assert 0, (a_t, b_t)

    elif p in [
        r"{PRODUCT} : {UNARY_OPERATOR}{FACTOR}",
        r'{PRODUCT} : -{var}',
        r"{NUM_EXPR} : -{FACTOR}",
    ]:
        ex = children[-1]
        # almost: env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        # but's a vaguer type-requirement, and we need the actual type out.

        (t, env1) = tc_expr(ex, env0); assert env1 is env0
        if t == T_TBD:
            t = T_Integer_ # maybe
            env2 = env1.with_expr_type_replaced(ex, t)
        else:
            assert t.is_a_subtype_of_or_equal_to(T_Number), t
            env2 = env1
        return (t, env2)

    # -------------------------
    # return T_String

    elif p in [
        r'{LITERAL} : {STR_LITERAL}',
        r'{STR_LITERAL} : {code_unit_lit}',
        r'{STR_LITERAL} : `"[^`"]*"`',
    ]:
        return (T_String, env0)

    elif expr.prod.lhs_s == '{STR_LITERAL}':
        return (T_String, env0)

    elif p in [
        r"{EX} : the String {var}",
        r"{EXPR} : the String {STR_LITERAL}",
        r"{EXPR} : the String value {SETTABLE}",
    ]:
        [ex] = children
        env0.ensure_expr_is_of_type(ex, T_String)
        return (T_String, env0)

    elif p == r"{MULTILINE_EXPR} : the String value corresponding to the value of {var} as follows:{I_TABLE}":
        [old_var, table] = children
        env1 = env0.ensure_expr_is_of_type(old_var, T_code_unit_)
        return (T_String, env0)

    elif p == r'{EXPR} : the same result produced as if by performing the algorithm for `String.prototype.toUpperCase` using {var} as the *this* value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

    elif p == r'{EX} : the referenced name component of {var}':
        [v] = children
        env0.assert_expr_is_of_type(v, T_Reference)
        return (T_String | T_Symbol | T_Private_Name, env0) # PR 1668 privates

    elif p == r'{EXPR} : the string result of converting {EX} to a String of four lowercase hexadecimal digits':
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value consisting solely of {code_unit_lit}",
        r"{EXPR} : the String value containing only the code unit {var}",
        r"{EXPR} : the String value consisting of the single code unit {var}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_String, env1)

#    elif p == r"{EXPR} : the String value consisting of the sequence of code units corresponding to {PROD_REF}. In determining the sequence any occurrences of {TERMINAL} {nonterminal} are first replaced with the code point represented by the {nonterminal} and then the code points of the entire {PROD_REF} are converted to code units by CodePointToUTF16CodeUnits??? each code point":
#        return (T_String, env0)
# ^ obsoleted by PR 1552

    elif p == r"{EXPR} : the String value that is the same as {var} except that each occurrence of {code_unit_lit} in {var} has been replaced with the six code unit sequence {STR_LITERAL}":
        [var, lita, var2, litb] = children
        assert var.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

    elif p == r"{MULTILINE_EXPR} : the string-concatenation of:{I_BULLETS}":
        [bullets] = children
        # Should check the bullets
        return (T_String, env0)

    # PR 1554 NumericValue:
    elif p == r"{MULTILINE_EXPR} : an implementation-dependent choice of:{I_BULLETS}":
        [bullets] = children
        # Should check the bullets
        return (T_Parse_Node, env0)

    elif p in [
        r"{EXPR} : the string-concatenation of {EX} and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
    ]:
        env1 = env0
        for ex in children:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}. If {var} is 0, the first element of the concatenation will be the empty String":
        p_var = children[3]
        env0.assert_expr_is_of_type(p_var, T_Integer_)
        env1 = env0
        for ex in children[0:3]:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r'{EX} : the two uppercase hexadecimal digits encoding {var}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EX} : the code unit of the single digit of {var}",
        r"{EX} : the code units of the decimal representation of the integer abs({var}-1) (with no leading zeroes)",
        r"{EX} : the code units of the most significant digit of the decimal representation of {var}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EX} : the code units of the most significant {var} digits of the decimal representation of {var}",
        r"{EX} : the code units of the remaining {NUM_EXPR} digits of the decimal representation of {var}",
        r"{EX} : the code units of the {var} digits of the decimal representation of {var} (in order, with no leading zeroes)",
        r"{EX} : the code units of the {var} digits of the decimal representation of {var}",

    ]:
        [nd_var, num_var] = children
        env0.assert_expr_is_of_type(nd_var, T_Integer_)
        env0.assert_expr_is_of_type(num_var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EX} : {EX} occurrences of {code_unit_lit}":
        [ex, cu_lit] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        return (ListType(T_code_unit_), env1)

    elif p == r"{EX} : {code_unit_lit} or {code_unit_lit} according to whether {var}-1 is positive or negative":
        [lit1, lit2, var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the substring of {var} from index {var} to index {var} inclusive",
        r"{EXPR} : the matched substring (i.e. the portion of {var} between offset {var} inclusive and offset {var} exclusive)",
        r"{EX} : the substring of {var} consisting of the code units from {var} (inclusive) up to {var} (exclusive)",
    ]:
        [s_var, start_var, end_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(start_var, T_Integer_)
        env0.assert_expr_is_of_type(end_var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EX} : the substring of {var} consisting of the code units from {var} (inclusive) up through the final code unit of {var} (inclusive)":
        [s_var, start_var, s_var2] = children
        assert same_source_text(s_var, s_var2)
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(start_var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value of {DOTTING}":
        # todo: sounds like "String value" is an operation applied to the result of DOTTING
        [dotting] = children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_String, env0)

# PR 1725 obsoleted:
#    elif p == r"{EXPR} : the String value of the Element Type value in {h_emu_xref} for {EX}":
#        [emu_xref, ex] = children
#        env1 = env0.ensure_expr_is_of_type(ex, T_String)
#        return (T_String, env0)

    elif p == r"{EXPR} : the Element Type value in {h_emu_xref} for {EX}":
        [emu_xref, ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_TypedArray_element_type_, env0)

    elif p in [
        r"{EXPR} : the String value of length 1, containing one code unit from {var}, namely the code unit at index {var}",
        r"{EXPR} : the String value of length 1, containing one code unit from {var}, specifically the code unit at index {var}",
    ]:
        [s_var, i_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(i_var, T_Integer_)
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the sole element of {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the sole element of {var}",
    ]:
        [noi] = children
        env0.assert_expr_is_of_type(noi, ListType(T_String)) # not justified
        return (T_String, env0)

    elif p == r"{EXPR} : the string that is the only element of {PP_NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, ListType(T_String))
        return (T_String, env0)

    elif p == r"{EXPR} : {var}'s {DSBN} value":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_Symbol)
        assert dsbn.source_text() == '[[Description]]'
        return (T_String | T_Undefined, env0)

    elif p in [
        r"{EXPR} : the String value whose code units are {PP_NAMED_OPERATION_INVOCATION}",
        # r"{EXPR} : the String value whose elements are {NAMED_OPERATION_INVOCATION}",
    ]:
        [noi] = children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_code_unit_))
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value consisting of {EXPR}",
        r"{EXPR} : the String value consisting of the code units of {var}",
        r"{EXPR} : the String value consisting of {EX}",
        r"{EXPR} : the String value consisting of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the String value whose code units are, in order, the elements in {PP_NAMED_OPERATION_INVOCATION}",
        # r"{EXPR} : the String value whose elements are, in order, the elements in {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the string consisting of the code units of {var}",
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are the elements of {PP_NAMED_OPERATION_INVOCATION} as defined in {h_emu_xref}":
        [noi, emu_xref] = children    
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_code_unit_))
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value whose code units are the elements of {var} followed by the elements of {var}",
        r"{EXPR} : the String value whose code units are the elements of {var} followed by the elements of {var} followed by the elements of {var}",
    ]:
        for var in children:
            env0 = env0.ensure_expr_is_of_type(var, T_String | ListType(T_code_unit_))
        return (T_String, env0)

    elif p == r"{EXPR} : a String according to {h_emu_xref}":
        [emu_xref] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value of the property name":
        # property of the Global Object
        # todo: make that explicit
        [] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {code_unit_lit}. A comma is not inserted either before the first String or after the last String":
        [var, str_literal] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {var}. The {var} String is not inserted either before the first String or after the last String":
        [var, sep_var, sep_var2] = children
        assert sep_var.children == sep_var2.children
        env0.assert_expr_is_of_type(sep_var, T_String)
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    elif p == r"{EXPR} : the Name of the entry in {h_emu_xref} with the Number {PP_NAMED_OPERATION_INVOCATION}":
        [emu_xref, noi] = children
        env0.assert_expr_is_of_type(noi, T_Number)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the String representation of {EX}, formatted as a decimal number",
        r"{EXPR} : the String representation of {EX}, formatted as a two-digit decimal number, padded to the left with a zero if necessary",
    ]:
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Number)
        return (T_String, env0)

    elif p == r"{EXPR} : an implementation-defined string that is either {EX} or {EXPR}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_String)
        env0.assert_expr_is_of_type(exb, T_String)
        return (T_String, env0)

    elif p == r"{EX} : an implementation-defined timezone name":
        [] = children
        return (T_String, env0)

    elif p == r"{EX} : the escape sequence for {var} as specified in the &ldquo;Escape Sequence&rdquo; column of the corresponding row":
        [var] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value derived from {var} by copying code unit elements from {var} to {var} while performing replacements as specified in {h_emu_xref}. These `$` replacements are done left-to-right, and, once such a replacement is performed, the new replacement text is not subject to further replacements":
        [va, vb, vc, _] = children
        assert same_source_text(va, vb)
        env0.assert_expr_is_of_type(vb, T_String)
        # env0.assert_expr_is_of_type(vc, T_String) repeats the var-being-defined
        return (T_String | T_throw_, env0)

    # ----------------------------------------------------------
    # return T_character_

    elif p == r"{EXPR} : the character {code_point_lit}":
        [cp_literal] = children
        return (T_character_, env0)

    elif p == r"{EXPR} : the character matched by {PROD_REF}":
        [prod_ref] = children
        return (T_character_, env0)

    elif p == r"{EXPR} : the character whose character value is {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Integer_)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character whose code is {EXPR}":
        # todo: I think "code" means "code unit" and/or "value"?
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, ListType(T_code_unit_) | T_Integer_)
        return (T_character_, env1)

    elif p == r'{EXPR} : the result of applying that mapping to {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (T_character_, env1)

    elif p == r'{EXPR} : the one character in CharSet {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character {SETTABLE}":
        [settable] = children
        env1 = env0.ensure_expr_is_of_type(settable, T_character_)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character according to {h_emu_xref}":
        [emu_xref] = children
        return (T_character_, env0)

    # ----------------------------------------------------------
    # return T_code_unit_

    elif expr.prod.lhs_s == '{code_unit_lit}':
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : {var}'s single code unit element": # todo: element of String
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    elif p == r'{EX} : the first code unit of {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    elif p == r"{EXPR} : the code unit whose value is determined by {PROD_REF} according to {h_emu_xref}":
        [nonterminal, emu_xref] = children
        return (T_code_unit_, env0)

    elif p in [
        r"{EXPR} : the code unit whose value is {SUM}",
        r"{EXPR} : the code unit whose value is {EXPR}",
        r"{EXPR} : the code unit whose value is {NAMED_OPERATION_INVOCATION}", 
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_ | T_MathInteger_)
        return (T_code_unit_, env0)

#    elif p == r"{EX} : the code unit {var}":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_Integer_)
#        return (T_code_unit_, env0)

    elif p == r"{EX} : the code unit that is {PP_NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, ListType(T_code_unit_))
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : the code unit whose numeric value is that of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_code_unit_, env0)

    # ----

    elif p == r"{EX} : the code unit at index {EX} within {EX}":
        [index_ex, str_ex] = children
        env0.assert_expr_is_of_type(str_ex, T_String)
        env1 = env0.ensure_expr_is_of_type(index_ex, T_Integer_)
        return (T_code_unit_, env1)

    elif p == r"{EXPR} : the code unit (represented as a 16-bit unsigned integer) at index {var} within {var}":
        [ivar, svar] = children
        env0.assert_expr_is_of_type(ivar, T_Integer_)
        env0.assert_expr_is_of_type(svar, T_String)
        return (T_code_unit_, env0)

    # ----------------------------------------------------------
    # return T_code_point_

    elif p == r"{EXPR} : the code point {var}":
        # This means "the code point whose numeric value is {var}"
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_code_point_, env0)

    elif p == r"{EXPR} : the code point whose numeric value is that of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_code_point_, env0)

    elif expr.prod.lhs_s == '{code_point_lit}':
        return (T_code_point_, env0)

    elif p == r"{EXPR} : the code point matched by {PROD_REF}":
        [nont] = children
        return (T_code_point_, env0)

    elif p == r"{EX} : the single code point matched by this production":
        [] = children
        return (T_code_point_, env0)

    # ----------------------------------------------------------
    # return T_Unicode_code_points_

    elif p == r'{EXPR} : the source text that was recognized as {PROD_REF}':
        [nonterminal] = children
        # XXX Should check whether nonterminal makes sense
        # with respect to the emu-grammar accompanying this alg/expr.
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the source text matched by {PROD_REF}":
        [nont] = children
        return (T_Unicode_code_points_, env0) # XXX spec bug: needs to be T_String?

#    elif p == r"{EXPR} : a List whose elements are the code points resulting from applying UTF-16 decoding to {var}'s sequence of elements":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_String)
#        return (ListType(T_code_point_), env0)
# ^ obsoleted by PR 1552

    elif p == r"{EXPR} : a List whose elements are the code points of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (ListType(T_code_point_), env0)

    elif p == r"{EXPR} : the sequence of Unicode code points that results from interpreting {var} as UTF-16 encoded Unicode text as described in {h_emu_xref}":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the result of toLowercase({var}), according to the Unicode Default Case Conversion algorithm":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the result of replacing any occurrences of {TERMINAL} {nonterminal} in {var} with the code point represented by the {nonterminal}":
        [term, nont, var, nont2] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the sequence of code points resulting from interpreting each of the 16-bit elements of {var} as a Unicode BMP code point. UTF-16 decoding is not applied to the elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    # ----------------------------------------------------------
    # return ListType

    # --------------------
    # ListType(T_Integer_)

    elif (
        p.startswith(r'{EXPR} : a List containing the 4 bytes that are the result of converting {var} to IEEE 754-2019 binary32 format')
        or
        p.startswith(r'{EXPR} : a List containing the 8 bytes that are the IEEE 754-2019 binary64 format encoding of {var}.')
    ):
        var = children[0]
        env1 = env0.ensure_expr_is_of_type(var, T_Number)
        return (ListType(T_Integer_), env1)

    elif p in [
        r'{EXPR} : a List containing the {var}-byte binary encoding of {var}. If {var} is {LITERAL}, the bytes are ordered in big endian order. Otherwise, the bytes are ordered in little endian order',
        r"{EXPR} : a List containing the {var}-byte binary two's complement encoding of {var}. If {var} is {LITERAL}, the bytes are ordered in big endian order. Otherwise, the bytes are ordered in little endian order",
    ]:
        [n_var, v_var, i_var, literal] = children
        env0.assert_expr_is_of_type(n_var, T_Number)
        env0.assert_expr_is_of_type(v_var, T_MathInteger_)
        env0.assert_expr_is_of_type(i_var, T_Boolean)
        env0.assert_expr_is_of_type(literal, T_Boolean)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of length 1 that contains a nondeterministically chosen byte value":
        [] = children
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of length {var} of nondeterministically chosen byte values":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of size {var} containing the sequence of {var} bytes starting with {var}[{var}]":
        [var1, var2, var3, var4] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(var3, T_Data_Block | T_Shared_Data_Block)
        env0.assert_expr_is_of_type(var4, T_Integer_)
        return (ListType(T_Integer_), env1)

    elif p == r"{EXPR} : a List of 8-bit integers of size {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the List of octets resulting by applying the UTF-8 transformation to {DOTTING}":
        [dotting] = children
        env1 = env0.ensure_expr_is_of_type(dotting, T_code_point_)
        return (ListType(T_Integer_), env1)

    # ----------------------
    # ListType(T_code_unit_)

    elif p == r"{EXPR} : the empty code unit sequence":
        [] = children
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : the sequence consisting of {code_unit_lit}":
        [lit] = children
        return (ListType(T_code_unit_), env0)

    elif p in [
        r"{EX} : a sequence of up to two code units that is {NAMED_OPERATION_INVOCATION}",
        r"{EX} : the code units of {NAMED_OPERATION_INVOCATION}",
        r"{EX} : the code units of {NAMED_OPERATION_INVOCATION} in order",
        r"{EX} : the code units of {var}",
    ]:
        [noi] = children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_code_unit_))
        return (ListType(T_code_unit_), env1)

    elif p in [
        r"{EXPR} : {EX} followed by {EX}",
        r"{EXPR} : the sequence consisting of {EX} followed by {EX}",
        r"{EXPR} : the sequence consisting of {EX} followed by {EX} followed by {EX}",
        r"{EXPR} : the sequence consisting of {EX} followed by {EX} followed by {EX} followed by {EX}",
    ]:
        env1 = env0
        for ex in children:
            env1 = env1.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (ListType(T_code_unit_), env1)

    elif p in [
        r"{EXPR} : a sequence consisting of the code units of {NAMED_OPERATION_INVOCATION} followed by the code units of {NAMED_OPERATION_INVOCATION}",
    ]:
        [ex1, ex2] = children
        env1 = (
            env0.ensure_expr_is_of_type(ex1, ListType(T_code_unit_))
                .ensure_expr_is_of_type(ex2, ListType(T_code_unit_))
        )
        return (ListType(T_code_unit_), env1)

    elif p == r"{EXPR} : a List whose elements are the code unit elements of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

    elif p in [
        r"{EXPR} : the sequence of code units consisting of the code units of {var} followed by the elements of {var}",
        r"{EXPR} : the sequence of code units consisting of the elements of {var} followed by the code units of {var} followed by the elements of {var}",
    ]:
        for var in children:
            env0.ensure_expr_is_of_type(var, T_String | ListType(T_code_unit_))
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : the code unit sequence consisting of {var} followed by {var}":
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_Integer_)
        env0.assert_expr_is_of_type(var2, T_Integer_)
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : a List consisting of the sequence of code units that are the elements of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

    # ---------------
    # ListType(T_String)

    elif p == r"{EXPR} : a List containing {var} followed by the elements, in order, of {var}":
        # once, in TemplateStrings
        # This is over-specific to that case.
        [item_var, list_var] = children
        env1 = env0.ensure_expr_is_of_type(item_var, ListType(T_code_unit_))
        env2 = env1.ensure_expr_is_of_type(list_var, ListType(T_String))
        #PR2018 env1 = env0.ensure_expr_is_of_type(item_var, T_String | T_Undefined)
        #PR2018 env2 = env1.ensure_expr_is_of_type(list_var, ListType(T_String | T_Undefined))
        return (ListType(T_String), env2)

    # ---------------
    # ListType(other)

    elif p == r'{EXPR} : a new empty List':
        [] = children
        return (T_List, env0) # (ListType(T_0), env0)

    elif p in [
        r"{EXPR} : a List containing only {var}",
        r"{EXPR} : a List containing the one element which is {var}",
        r"{EXPR} : a List containing the single element, {var}",
        r"{EXPR} : a List containing {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : a List containing {PROD_REF}",
        r"{EXPR} : a List whose sole item is {var}",
        r"{EXPR} : a new List containing {EXPR}",
    ]:
        [element_expr] = children
        (element_type, env1) = tc_expr(element_expr, env0); assert env1.equals(env0)
        return (ListType(element_type), env0)

    elif p in [
        r"{EXPR} : the result of appending to {var} the elements of {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : a copy of {var} with all the elements of {var} appended",
    ]:
        [var, noi] = children
        (t1, env1) = tc_expr(var, env0); assert env1 is env0
        (t2, env2) = tc_expr(noi, env0); assert env2 is env0
        if t1 == T_TBD and t2 == T_TBD:
            list_type = T_List
        elif t1 == T_List and t2 == T_TBD:
            list_type = t1
        elif isinstance(t1, ListType) and t1 == t2:
            list_type = t1
        else:
            assert 0
            # assert t1.element_type == t2.element_type
        return (list_type, env0)

    elif p in [
        r"{EXPR} : a copy of {var} with {var} appended",
        r"{EXPR} : a List containing the elements, in order, of {var} followed by {var}",
    ]:
        [list_var, item_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(item_var, list_var)
        list_type = env1.lookup(list_var)
        return (list_type, env1)

#    elif p == r"{EXPR} : a List whose first element is {var}, whose second elements is {var}, and whose subsequent elements are the elements of {var}, in order. {var} may contain no elements":
#        [e1_var, e2_var, rest_var, _] = children
#        (t1, env1) = tc_expr(e1_var, env0); assert env1 is env0
#        (t2, env2) = tc_expr(e2_var, env0); assert env2 is env0
#        (rest_t, rest_env) = tc_expr(rest_var, env0); assert rest_env is env0
#        if t1 == T_TBD and t2 == T_TBD and rest_t == T_List:
#            # can't really do much
#            pass
#        elif t1 == T_TBD and t2 == T_Tangible_:
#            pass
#        elif t1 == T_Object and t2 == T_Tangible_ and rest_t == ListType(T_Tangible_):
#            pass
#        else:
#            assert t1 == t2
#            assert isinstance(rest_t, ListType)
#            assert t1 == rest_t.element_type
#        return (rest_t, rest_env)
# ^ obsoleted by PR #1402

    elif p == r'{EXPR} : a new List containing the same values as the list {var} where the values are ordered as if an Array of the same values had been sorted using `Array.prototype.sort` using *undefined* as {var}':
        [var, _] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

    elif p == r"{EXPR} : the List of {nonterminal} items in {PROD_REF}, in source text order":
        [nont, prod_ref] = children
        return (ListType(T_Parse_Node), env0)

    elif p == r"{EXPR} : a new list containing the same values as the list {var} in the same order followed by the same values as the list {var} in the same order":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(bvar, ListType(T_Tangible_))
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : {var}<sup>th</sup> element of {var}'s _captures_ List":
        [n_var, state_var] = children
        env0.assert_expr_is_of_type(n_var, T_Integer_)
        env0.assert_expr_is_of_type(state_var, T_State)
        return (T_captures_entry_, env0)

#    elif p == r"{EXPR} : a List consisting of the sequence of code points of {var} interpreted as a UTF-16 encoded ({h_emu_xref}) Unicode string":
#        [var, emu_xref] = children
#        env0.assert_expr_is_of_type(var, T_String)
#        return (ListType(T_code_point_), env0)
# obsoleted by 1552

    elif p == r"{EXPR} : a List consisting of the sequence of code points of {PP_NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return (ListType(T_code_point_), env0)

    elif p == r"{EXPR} : a List of {var} {LITERAL} values, indexed 1 through {var}":
        [var, literal, var2] = children
        assert var.children == var2.children
        env0.assert_expr_is_of_type(var, T_Integer_)
        (lit_t, env1) = tc_expr(literal, env0); assert env1 is env0
        return (ListType(lit_t), env1)

    elif p == r"{EXPR} : a new List whose elements are the characters of {var} at indices {var} (inclusive) through {var} (exclusive)":
        [list_var, s_var, e_var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_character_))
        env0.assert_expr_is_of_type(s_var, T_Integer_)
        env0.assert_expr_is_of_type(e_var, T_Integer_)
        return (ListType(T_character_), env0)

    # --------------------------------------------------------
    # return T_Parse_Node

    elif p == r'{MULTILINE_EXPR} : the result of parsing the source text{_indent_}{nlai}{h_pre_code}{nlai}using the syntactic grammar with the goal symbol {nonterminal}.{_outdent_}':
        [_, nonterminal] = children
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{EXPR} : the {nonterminal} that is covered by {LOCAL_REF}":
        [nonterminal, local_ref] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

#    elif p == r"{EXPR} : the ECMAScript code that is the result of parsing {var}, interpreted as UTF-16 encoded Unicode text as described in {h_emu_xref}, for the goal symbol {nonterminal}. If the parse fails, throw a {ERROR_TYPE} exception. If any early errors are detected, throw a {ERROR_TYPE} exception (but see also clause {h_emu_xref})":
#        [s_var, emu_xref, goal_nont,
#        error_type1,
#        error_type2, emu_xref4] = children
#        #
#        env0.assert_expr_is_of_type(s_var, T_String)
#        error_type_name1 = error_type1.source_text()[1:-1]
#        error_type_name2 = error_type2.source_text()[1:-1]
#        proc_add_return(env0, ThrowType(NamedType(error_type_name1)), error_type1)
#        proc_add_return(env0, ThrowType(NamedType(error_type_name2)), error_type2)
#        return (ptn_type_for(goal_nont), env0)
# ^ obsoleted by PR 1552

    elif p == r"{EXPR} : the ECMAScript code that is the result of parsing {PP_NAMED_OPERATION_INVOCATION}, for the goal symbol {nonterminal}. If the parse fails, throw a {ERROR_TYPE} exception. If any early errors are detected, throw a {ERROR_TYPE} exception (but see also clause {h_emu_xref})":
        [s_noi, goal_nont,
        error_type1,
        error_type2, emu_xref4] = children
        #
        env0.assert_expr_is_of_type(s_noi, T_Unicode_code_points_)
        error_type_name1 = error_type1.source_text()[1:-1]
        error_type_name2 = error_type2.source_text()[1:-1]
        proc_add_return(env0, ThrowType(NamedType(error_type_name1)), error_type1)
        proc_add_return(env0, ThrowType(NamedType(error_type_name2)), error_type2)
        return (ptn_type_for(goal_nont), env0)


#    elif p == r"{EXPR} : the result of parsing {var}, interpreted as UTF-16 encoded Unicode text as described in {h_emu_xref}, using {var} as the goal symbol. Throw a {ERROR_TYPE} exception if the parse fails":
#        [var, emu_xref, goal_var, error_type] = children    
#        env0.assert_expr_is_of_type(var, T_String)
#        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
#        error_type_name = error_type.source_text()[1:-1]
#        proc_add_return( env0, ThrowType(NamedType(error_type_name)), error_type)
#        return (T_Parse_Node, env0)
# ^ obsoleted by PR 1552

    elif p == r"{EXPR} : the result of parsing {PP_NAMED_OPERATION_INVOCATION}, using {var} as the goal symbol. Throw a {ERROR_TYPE} exception if the parse fails":
        [noi, goal_var, error_type] = children    
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
        error_type_name = error_type.source_text()[1:-1]
        proc_add_return( env0, ThrowType(NamedType(error_type_name)), error_type)
        return (T_Parse_Node, env0)


    # ----

    elif p == r'{LOCAL_REF} : the {nonterminal} of {var}':
        [nonterminal, var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        # XXX could check that t is a nonterminal that actually has a child of that type
        # but that requires having the whole grammar handy
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : this {nonterminal}':
        [nonterminal] = children
        # XXX check
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : {nonterminal}':
        [nonterminal] = children
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : the {ORDINAL} {nonterminal}':
        [ordinal, nonterminal] = children
        # XXX should check that the 'current' production has such.
        return (ptn_type_for(nonterminal), env0)

    elif p in [
        r'{PROD_REF} : the {nonterminal}',
        r'{PROD_REF} : the (first|second|third) {nonterminal}',
    ]:
        nonterminal = children[-1]
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{PROD_REF} : the corresponding {nonterminal}":
        [nont] = children
        return (ptn_type_for(nont), env0)

#    elif p == r"{PROD_REF} : the {nonterminal} that is that {nonterminal}":
#        [a_nont, b_nont] = children
#        return (ptn_type_for(a_nont), env0)
# ^ obsoleted by PR #1301

    elif p == r"{EXPR} : an instance of the production {h_emu_grammar}":
        [emu_grammar] = children
        assert emu_grammar.source_text() == '<emu-grammar>FormalParameters : [empty]</emu-grammar>'
        return (ptn_type_for('FormalParameters'), env0)

    elif p == r"{EXPR} : the {nonterminal}, {nonterminal}, or {nonterminal} that most closely contains {var}":
        [*nont_, var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (T_Parse_Node, env0)

#    elif p == r"{PROD_REF} : the {nonterminal} that is that single code point":
#        [nont] = children
#        return (T_Parse_Node, env0)
# ^ obsoleted by PR #1301

    elif p == r"{LOCAL_REF} : the parsed code that is {DOTTING}":
        [dotting] = children
        env0.assert_expr_is_of_type(dotting, T_Parse_Node)
        return (T_Parse_Node, env0)

    # --------------------------------------------------------
    # return T_Object

    elif p == r'{EXPR} : the binding object for {var}':
        [var] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_object_Environment_Record)
        return (T_Object, env0)

    elif p == r'{EXPR} : a newly created object with an internal slot for each name in {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
        return (T_Object, env1)

#    elif p == r"{EXPR} : a newly created module namespace exotic object with the internal slots listed in {h_emu_xref}":
#        [emu_xref] = children
#        return (T_Object, env0)
#
#    elif p == r"{EXPR} : a newly created Proxy exotic object with internal slots {DSBN} and {DSBN}":
#        [dsbn1, dsbn2] = children
#        return (T_Object, env0)
#
#    elif p == r"{EXPR} : a newly created arguments exotic object with a {DSBN} internal slot":
#        [dsbn] = children
#        return (T_Object, env0)
# ^ obsoleted by PR #1460

    elif p == r'{EXPR} : a newly created object':
        [] = children
        return (T_Object, env0)

    elif p in [
        r"{LITERAL} : {percent_word}",
        r"{EXPR} : the intrinsic object {percent_word}",
    ]:
        [percent_word] = children
        pws = percent_word.source_text()
        if pws in [
            '%Promise%',
            '%RegExp%',
            '%ArrayBuffer%',
            '%SharedArrayBuffer%',
        ]:
            rt = T_constructor_object_
        else:
            rt = T_Object
        return (rt, env0)
        # We could be more specific in many cases, but I'm not sure it would make any difference.

    elif p == r"{SETTABLE} : the Generator component of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (T_Object, env0)

    elif p == r"{EXPR} : the arguments object":
        [] = children
        return (T_Object, env0)

    elif p == r"{EXPR} : {var}'s intrinsic object named {var}":
        [r_var, n_var] = children
        env0.assert_expr_is_of_type(r_var, T_Realm_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (T_Object, env0)

    # -------------------------------------------------
    # return T_CharSet

    elif p == r'{EXPR} : the set containing all characters numbered {var} through {var}, inclusive':
        [var1, var2] = children
        env1 = env0.ensure_expr_is_of_type(var1, T_Integer_)
        env2 = env0.ensure_expr_is_of_type(var2, T_Integer_)
        assert env1 is env0
        assert env2 is env0
        return (T_CharSet, env0)

    elif p == r"{EXPR} : an empty set":
        [] = children
        return (T_CharSet, env0)

    elif p in [
        r"{EXPR} : the CharSet containing the single character {code_point_lit}",
        r"{EXPR} : the CharSet containing the single character {var}",
        r"{EXPR} : the CharSet containing the single character that is {EXPR}",
    ]:
        [ex] = children
        env0.ensure_expr_is_of_type(ex, T_character_)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing the character matched by {PROD_REF}":
        [prod_ref] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : a one-element CharSet containing the character {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the union of CharSets {var}, {var} and {var}":
        [va, vb, vc] = children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        envc = env0.ensure_expr_is_of_type(vc, T_CharSet)
        return (T_CharSet, envs_or([enva, envb, envc]))

    elif p == r"{EXPR} : the union of CharSets {var} and {var}":
        [va, vb] = children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env_or(enva, envb))

    elif p == r"{MULTILINE_EXPR} : a set of characters containing the sixty-three characters:{nlai}{h_figure}":
        [figure] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters except {nonterminal}":
        [nonterminal] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the ten-element set of characters containing the characters `0` through `9` inclusive":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters not included in the set returned by {h_emu_grammar} ":
        [emu_grammar] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of characters containing the characters that are on the right-hand side of the {nonterminal} or {nonterminal} productions":
        [nont1, nont2] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters returned by {PREFIX_PAREN}":
        [pp] = children
        env0.assert_expr_is_of_type(pp, T_CharSet)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the empty CharSet":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value {var}":
        [va, vb] = children
        env0.assert_expr_is_of_type(va, ListType(T_Integer_))
        env0.assert_expr_is_of_type(vb, ListType(T_Integer_))
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property &ldquo;General_Category&rdquo; with value {var}":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value &ldquo;True&rdquo;":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (T_CharSet, env0)

    elif p in [
        r"{EXPR} : the CharSet containing all Unicode code points included in the CharSet returned by {PROD_REF}",
        r"{EXPR} : the CharSet containing all Unicode code points not included in the CharSet returned by {PROD_REF}",
    ]:
        [nont] = children
        return (T_CharSet, env0)

    # -------------------------------------------------
    # return T_function_object_

#    elif p == r'{EXPR} : a newly created ECMAScript function object with the internal slots listed in {h_emu_xref}':
#        [emu_xref] = children
#        return (T_function_object_, env0)
# ^ obsoleted by PR #1460

    elif p == r'{EXPR} : a new built-in function object that when called performs the action described by {var}. The new function object has internal slots whose names are the elements of {var}, and an {DSBN} internal slot':
        [var1, var2, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var1, T_alg_steps)
        # env1 = env0.ensure_expr_is_of_type(var2, )
        return (T_function_object_, env1)

    # ------------------------------------------------
    # return T_alg_steps

    elif p == r"{EXPR} : the algorithm steps defined in {h_emu_xref}":
        [emu_xref] = children
        return (T_alg_steps, env0)

    elif p == r"{EXPR} : the algorithm steps defined in (.+) ({h_emu_xref})":
        [_, emu_xref] = children
        return (T_alg_steps, env0)

    elif p in [
        r"{EXPR} : the steps of an {cap_word} function as specified below",
    ]:
        [cap_word] = children
        return (T_alg_steps, env0)

# PR 1635 obsoleted
#    elif p == r"{EXPR} : the algorithm steps specified in {h_emu_xref} for the {percent_word} function":
#        [emu_xref, percent_word] = children
#        return (T_alg_steps, env0)

# PR 1635 obsoleted
#    elif p == r"{EXPR} : an empty sequence of algorithm steps":
#        [] = children
#        return (T_alg_steps, env0)

    # ------------------------------------------------
    # return T_execution_context

    elif p == r"{EXPR} : a new execution context":
        [] = children
        return (T_execution_context, env0)

    elif p == r"{EXPR} : a new ECMAScript code execution context":
        [] = children
        return (T_execution_context, env0)

    elif p == r'{EXPR} : the running execution context':
        [] = children
        return (T_execution_context, env0)

    elif p == r'{EXPR} : the topmost execution context on the execution context stack whose ScriptOrModule component is not {LITERAL}':
        [literal] = children
        return (T_execution_context, env0)

    elif p == r"{EXPR} : the second to top element of the execution context stack":
        [] = children
        return (T_execution_context, env0)

    # -------------------------------------------------
    # return T_Reference

    elif p == r'{EXPR} : a value of type Reference whose base value component is {EX}, whose referenced name component is {var}, and whose strict reference flag is {EX}':
        [bv_ex, rn_var, srf_var] = children

        env1 = env0.ensure_expr_is_of_type(bv_ex, T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number | T_Environment_Record)
        env2 = env1.ensure_expr_is_of_type(rn_var, T_String | T_Symbol)
        env3 = env2.ensure_expr_is_of_type(srf_var, T_Boolean)

        return (T_Reference, env3)

    elif p in [
        r'{V} : the reference (_V_)',
        r'{V} : (_V_)',
    ]:
        [v_name] = children
        assert v_name == '_V_'
        assert env0.vars[v_name] == T_Reference
        return (T_Reference, env0)

    elif p == r"{EXPR} : a value of type Reference that is a Super Reference whose base value component is {var}, whose referenced name component is {var}, whose thisValue component is {var}, and whose strict reference flag is {var}":
        [b_var, n_var, t_var, s_var] = children
        env0.assert_expr_is_of_type(b_var, T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number)
        env0.assert_expr_is_of_type(n_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(t_var, T_Tangible_)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        return (T_Reference, env0)

    # -------------------------------------------------

    elif p == r"{EXPR} : the value of the thisValue component of the reference {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (T_Tangible_, env0)

    elif p in [
        r"{EXPR} : the value currently bound to {var} in {var}",
        r"{SETTABLE} : the bound value for {var} in {var}",
    ]:
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (T_Tangible_, env0)

#    elif p == r"{EXPR} : the result of applying {var} to {var} and {var} as if evaluating the expression {var} {var} {var}":
#        [op_var, avar, bvar, avar2, op_var2, bvar2] = children
#        assert op_var.children == op_var2.children
#        assert avar.children == avar2.children
#        assert bvar.children == bvar2.children
#        env0.assert_expr_is_of_type(op_var, T_proc_)
#        env1 = env0.ensure_expr_is_of_type(avar, T_Tangible_)
#        env2 = env1.ensure_expr_is_of_type(bvar, T_Tangible_)
#        return (T_Tangible_, env2)
# ^ obsoleted by PR 1961

    elif p == r"{EXPR} : the Completion Record that is the result of evaluating {var} in a manner that conforms to the specification of {var}. {var} is the *this* value, {var} provides the named parameters, and the NewTarget value is *undefined*":
        [avar, bvar, cvar, dvar] = children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, T_Tangible_)
        env0.assert_expr_is_of_type(dvar, ListType(T_Tangible_))
        return (T_Tangible_ | T_throw_, env0)

    elif p == r"{EXPR} : the Completion Record that is the result of evaluating {var} in a manner that conforms to the specification of {var}. The *this* value is uninitialized, {var} provides the named parameters, and {var} provides the NewTarget value":
        [avar, bvar, cvar, dvar] = children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(dvar, T_Tangible_)
        return (T_Tangible_ | T_throw_, env0)

    # -------------------------------------------------
    # return component of T_execution_context

    elif p in [
        r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} component of {var}",
        r"{SETTABLE} : The {EXECUTION_CONTEXT_COMPONENT} of {var}",
        r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of {var}",
        r"{SETTABLE} : {var}'s {EXECUTION_CONTEXT_COMPONENT}",
        # r"{SETTABLE} : the {var}'s {EXECUTION_CONTEXT_COMPONENT}", # PR 1740 obsoleted
        # r"{SETTABLE} : {var}'s {EXECUTION_CONTEXT_COMPONENT} component", # PR 1743 obsoleted
    ]:
        if p.endswith('{var}'):
            [component_name, var] = children
        else:
            [var, component_name] = children

        component_name = component_name.source_text()

        # env0.assert_expr_is_of_type(var, T_execution_context)

        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t == T_TBD:
            t = T_execution_context
            env2 = env1.with_expr_type_replaced(var, t)
        else:
            env2 = env1

        result_type = {
            # todo: make it a record?
            # 7110: Table 22: State Components for All Execution Contexts
            'code evaluation state': T_host_defined_,
            'Function'      : T_function_object_,
            'Realm'         : T_Realm_Record,
            'ScriptOrModule': T_Module_Record | T_Script_Record,

            # 7159: Table 23: Additional State Components for ECMAScript Code Execution Contexts
            'LexicalEnvironment' : T_Environment_Record,
            'VariableEnvironment': T_Environment_Record,
            # PR 1668 privates:
            'PrivateEnvironment' : T_Environment_Record,

            # 7191: Table 24: Additional State Components for Generator Execution Contexts
            'Generator' : T_Object,
        }[component_name]

        return (result_type, env2)

    # -------------------------------------------------
    # return proc type

    elif p == r'{EXPR} : the abstract operation named in the Conversion Operation column in {h_emu_xref} for Element Type {var}':
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type_)
        return (ProcType([T_Tangible_], T_Integer_), env1)

#    elif p == r"{EXPR} : the `@` where |AssignmentOperator| is `@=`":
#        return (ProcType([T_Number, T_Number], T_Number), env0)
# ^ obsoleted by PR 1961

#    elif p == r"{NAMED_OPERATION_INVOCATION} : the internal procedure that evaluates the above parse of {var} by applying the semantics provided in {h_emu_xref} using {var} as the pattern's List of {nonterminal} values and {var} as the flag parameters":
#        [source_var, emu_xref, chars_var, nont, f_var] = children
#        env0.assert_expr_is_of_type(source_var, T_String)
#        env0.assert_expr_is_of_type(chars_var, ListType(T_character_))
#        env0.assert_expr_is_of_type(f_var, T_String)
#        return (T_RegExpMatcher_, env0)
# ^ obsoleted by PR 1552

#    elif p == r"{NAMED_OPERATION_INVOCATION} : the Abstract Closure that evaluates the above parse by applying the semantics provided in {h_emu_xref} using {var} as the pattern's List of {nonterminal} values and {var} as the flag parameters":
#        [emu_xref, chars_var, nont, f_var] = children
#        env0.assert_expr_is_of_type(chars_var, ListType(T_character_))
#        env0.assert_expr_is_of_type(f_var, T_String)
#        return (T_RegExpMatcher_, env0)
# ^ obsoleted by PR 1866

    elif p == r"{NAMED_OPERATION_INVOCATION} : the Abstract Closure that evaluates {var} by applying the semantics provided in {h_emu_xref} using {var} as the pattern's List of {nonterminal} values and {var} as the flag parameters":
        [p_var, emu_xref, chars_var, nont, f_var] = children
        env1 = env0.ensure_expr_is_of_type(p_var, T_PTN_Pattern)
        env1.assert_expr_is_of_type(chars_var, ListType(T_character_))
        env1.assert_expr_is_of_type(f_var, T_String)
        return (T_RegExpMatcher_, env1)

    elif p == r"{EXPR} : a Continuation that always returns its State argument as a successful MatchResult":
        [] = children
        return (T_Continuation, env0)

#    elif p == r"{EXPR} : a Continuation that takes a State argument {var} and returns the result of calling {PREFIX_PAREN}":
#        [state_param, pp] = children
#        env_for_body = env0.plus_new_entry(state_param, T_State)
#        (pp_type, env1) = tc_expr(pp, env_for_body)
#        assert pp_type == T_MatchResult
#        return (T_Continuation, env0)
#
#    elif p in [
#        r"{MULTILINE_EXPR} : an internal Continuation closure that takes one State argument {var} and performs the following steps:{IND_COMMANDS}",
#    ]:
#        [state_param, commands] = children
#        env_for_commands = env0.plus_new_entry(state_param, T_State)
#        defns = [(None, commands)]
#        env_after_commands = tc_proc(None, defns, env_for_commands)
#        closure_t = T_Continuation
#        assert env_after_commands.vars['*return*'].is_a_subtype_of_or_equal_to(closure_t.return_type)
#        return (closure_t, env0)
#
#    elif p == r"{MULTILINE_EXPR} : an internal Matcher closure that takes two arguments, a State {var} and a Continuation {var}, and performs the following steps:{IND_COMMANDS}":
#        [state_param, cont_param, commands] = children
#        env_for_commands = env0.plus_new_entry(state_param, T_State).plus_new_entry(cont_param, T_Continuation)
#        defns = [(None, commands)]
#        env_after_commands = tc_proc(None, defns, env_for_commands)
#        # returns from within `commands`
#        # contribute to the matcher's return type,
#        # not to the current operation's.
#        assert env_after_commands.vars['*return*'] == T_MatchResult
#        return (T_Matcher, env0)
#
#    elif p == r"{EXPR} : a Matcher that takes two arguments, a State {var} and a Continuation {var}, and returns the result of calling {PREFIX_PAREN}":
#        [state_param, cont_param, prefix_paren] = children
#        env_for_pp = env0.plus_new_entry(state_param, T_State).plus_new_entry(cont_param, T_Continuation)
#        (t, env1) = tc_expr(prefix_paren, env_for_pp)
#        assert t == T_MatchResult
#        return (T_Matcher, env0)
#
#    elif p == r"{MULTILINE_EXPR} : an internal closure that takes two arguments, a String {var} and an integer {var}, and performs the following steps:{IND_COMMANDS}":
#        [s_param, i_param, commands] = children
#        env_for_commands = env0.plus_new_entry(s_param, T_String).plus_new_entry(i_param, T_Integer_)
#        defns = [(None, commands)]
#        env_after_commands = tc_proc(None, defns, env_for_commands)
#        t  = ProcType([T_String, T_Integer_], T_MatchResult)
#        return (t, env0)
# ^ obsoleted by PR #1889

    elif p == r"{MULTILINE_EXPR} : a new {CLOSURE_KIND} with {CLOSURE_PARAMETERS} that captures {CLOSURE_CAPTURES} and performs the following {CLOSURE_STEPS} when called:{IND_COMMANDS}":
        [clo_kind, clo_parameters, clo_captures, _, commands] = children
        clo_kind = clo_kind.source_text()

        #XXX Should assert no intersection between clo_parameters and clo_captures

        # -----

        env_for_commands = Env()

        n_parameters = len(clo_parameters.children)
        if clo_kind == 'Abstract Closure':
            clo_param_types = [T_TBD] * n_parameters
            alsos = [
                # See #sec-pattern
                ('_Unicode_',          T_Boolean),
                ('_NcapturingParens_', T_Integer_),
            ]
        elif clo_kind == 'Continuation':
            assert n_parameters == 1
            clo_param_types = [T_State]
            alsos = [
                ('_Input_',       ListType(T_character_)),
            ]
        elif clo_kind == 'Matcher':
            assert n_parameters == 2
            clo_param_types = [T_State, T_Continuation]
            alsos = [
                # See BackreferenceMatcher
                ('_InputLength_', T_Integer_),
                ('_Input_',       ListType(T_character_)),
                ('_Multiline_',   T_Boolean),
            ]
        elif clo_kind == 'Job Abstract Closure':
            assert n_parameters == 0
            clo_param_types = []
            alsos = []
        elif clo_kind == 'read-modify-write modification function':
            assert n_parameters == 2
            clo_param_types = [ListType(T_Integer_), ListType(T_Integer_)]
            alsos = []
        else:
            assert 0, clo_kind

        for (clo_param_var, clo_param_type) in zip(clo_parameters.children, clo_param_types):
            env_for_commands = env_for_commands.plus_new_entry(clo_param_var, clo_param_type)

        for clo_capture_var in clo_captures.children:
            clo_capture_type = env0.lookup(clo_capture_var)
            env_for_commands = env_for_commands.plus_new_entry(clo_capture_var, clo_capture_type)

        for (pn, pt) in alsos:
            env_for_commands = env_for_commands.plus_new_entry(pn, pt)

        env_for_commands.vars['*return*'] = T_0

        # -----

        defns = [(None, commands)]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        t = ProcType(clo_param_types, env_after_commands.vars['*return*'])
        return (t, env0)

    # -------------------------------------------------
    # return Environment_Record

    elif p in [
        r'{EXPR} : the {ENVIRONMENT_RECORD_KIND} Environment Record for which the method was invoked',
        r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record containing no bindings',
        r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record',
    ]:
        [kind] = children
        t = type_for_environment_record_kind(kind)
        return (t, env0)

    elif p == r'{EXPR} : a new object Environment Record containing {var} as the binding object':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_object_Environment_Record, env1)

    # -------------------------------------------------
    # return T_Realm_Record

    elif p == r'{EX} : the current Realm Record':
        [] = children
        return (T_Realm_Record, env0)

    elif p == r"{EXPR} : a new Realm Record":
        [] = children
        return (T_Realm_Record, env0)

    # -------------------------------------------------
    # whatever

    elif expr.prod.lhs_s == "{nonterminal}":
        nont_name = expr.source_text()[1:-1]
        # Note that |Foo| often denotes a Parse Node,
        # rather than a grammar symbol,
        # but we capture those cases before they can get to here.
        return (T_grammar_symbol_, env0)

    elif p == r"{EXPR} : the grammar symbol {nonterminal}":
        [nont] = children
        return (T_grammar_symbol_, env0)

    elif expr.prod.lhs_s == '{var}':
        [var_name] = children
        return (env0.vars[var_name], env0)

    elif p in [
        r'{SETTABLE} : {var}',
        r'{FACTOR} : {var}',
    ]:
        [var] = children
        [var_name] = var.children
        if var_name not in env0.vars:
            add_pass_error(
                var,
                "NOT DEFINED"
            )
            t = T_TBD
        else:
            t = env0.vars[var_name]
            # print("the type of %s is %s" % (var_name, t))
        return (t, env0)

    elif p in [
        r'{EXPR} : the Agent Record of the surrounding agent',
        r"{EXPR} : the surrounding agent's Agent Record",
    ]:
        [] = children
        return (T_Agent_Record, env0)

    elif p == r'{EXPR} : a new Data Block value consisting of {var} bytes. If it is impossible to create such a Data Block, throw a {ERROR_TYPE} exception':
        [var, error_type] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_Integer_)
        error_type_name = error_type.source_text()[1:-1]
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
        return (T_Data_Block, env1)

    elif p == r'{EXPR} : a new Shared Data Block value consisting of {var} bytes. If it is impossible to create such a Shared Data Block, throw a {ERROR_TYPE} exception':
        [var, error_type] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_Integer_)
        error_type_name = error_type.source_text()[1:-1]
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
        return (T_Shared_Data_Block, env1)

    elif p == '{RECORD_CONSTRUCTOR} : {RECORD_CONSTRUCTOR_PREFIX} { {FIELDS} }':
        [record_constructor_prefix, fields] = children
        constructor_prefix = record_constructor_prefix.source_text().replace('the ', '')

        if constructor_prefix == 'Completion':
            f_ = dict( get_field_items(fields) )
            assert sorted(f_.keys()) == ['Target', 'Type', 'Value']
            type_ex = f_['Type']
            value_ex = f_['Value']
            target_ex = f_['Target']

            if fields.source_text() == '[[Type]]: _completionRecord_.[[Type]], [[Value]]: _value_, [[Target]]: _completionRecord_.[[Target]]':
                # The specialest of special cases!
                # Occurs once, in UpdateEmpty.
                # In the context there,
                # the static type of _completionRecord_ is
                # (or would be, if STA were smart enough)
                # T_empty_ | T_continue_ | T_break_,
                # and the static type of _value_ is T_Tangible_ | T_empty_

                return (T_Tangible_ | T_empty_ | T_continue_ | T_break_, env0)
                
            else:
                env1 = env0.ensure_expr_is_of_type(value_ex, T_Tangible_ | T_empty_)
                (value_type, _) = tc_expr(value_ex, env1) # bleah

                env0.assert_expr_is_of_type(target_ex, T_String | T_empty_)

                ct = type_corresponding_to_comptype_literal(type_ex)
                if ct == T_Normal:
                    t = value_type
                elif ct == T_throw_:
                    t = ThrowType(value_type)
                else:
                    t = ct

                return (t, env1)

        if constructor_prefix == 'Record':
            record_type_name = None
            field_names = sorted(get_field_names(fields))
            if field_names == ['Array', 'Site']:
                record_type_name = 'templateMap_entry_'
            elif field_names == ['Closure', 'Key']:
                record_type_name = 'methodDef_record_'
            elif field_names == ['Configurable', 'Enumerable', 'Get', 'Set', 'Value', 'Writable']:
                # CompletePropertyDescriptor: the almost-Property Descriptor
                record_type_name = 'Property Descriptor'
            elif field_names == ['Done', 'Iterator', 'NextMethod']:
                record_type_name = 'iterator_record_'
            elif field_names == ['ExportName', 'Module']:
                record_type_name = 'ExportResolveSet_Record_'
            elif field_names == ['Key', 'Symbol']:
                record_type_name = 'GlobalSymbolRegistry Record'
            elif field_names == ['Key', 'Value']:
                record_type_name = 'MapData_record_'
            elif field_names == ['Reject', 'Resolve']:
                record_type_name = 'ResolvingFunctions_record_'
            elif field_names == ['CodePoint', 'CodeUnitCount', 'IsUnpairedSurrogate']:
                record_type_name = 'CodePointAt_record_'
            elif field_names == ['Initializer', 'IsAnonymousFunctionDefinition', 'Name']:
                record_type_name = 'ClassFieldDefinition Record' # PR 1668
            elif field_names == ['Gap', 'Indent', 'PropertyList', 'ReplacerFunction', 'Stack']:
                record_type_name = 'JSON_Stringify_state_record_'
            elif field_names == ['HeldValue', 'UnregisterToken', 'WeakRefTarget']:
                record_type_name = 'FinalizationRegistryCellRecord_'

            elif field_names == ['Value']:
                fst = fields.source_text()
                if fst == '[[Value]]: *false*':
                    record_type_name = 'boolean_value_record_'
                elif fst == '[[Value]]: 1':
                    record_type_name = 'integer_value_record_'
                else:
                    assert 0, fst

            if record_type_name:
                add_pass_error(
                    expr,
                    "Inferred record type `%s`: be explicit!" % record_type_name
                )
                field_info = fields_for_record_type_named_[record_type_name]
            else:
                add_pass_error(
                    expr,
                    "Could not infer a record type for fields: " + str(field_names)
                )
                record_type_name = 'Record'
                field_info = None

        else:
            if constructor_prefix in [
                'ReadModifyWriteSharedMemory',
                'ReadSharedMemory',
                'WriteSharedMemory',
            ]:
                record_type_name = constructor_prefix + ' event'
            elif constructor_prefix in [
                'Completion',
                'PromiseReaction',
                'PromiseCapability',
                'AsyncGeneratorRequest',
            ]:
                record_type_name = constructor_prefix + ' Record'
            elif constructor_prefix == 'PropertyDescriptor':
                record_type_name = 'Property Descriptor'
            else:
                record_type_name = constructor_prefix
            field_info = fields_for_record_type_named_[record_type_name]

        envs = []
        for (dsbn_name, ex) in get_field_items(fields):
            if field_info is None:
                # (because it's just a Record, not a particular (named) kind of Record)
                # We can't really assert anything.
                (t, env1) = tc_expr(ex, env0); assert env1 is env0
            else:
                declared_field_type = field_info[dsbn_name]
                # If the constructor referred to an undeclared field, that would raise a KeyError
                env1 = env0.ensure_expr_is_of_type(ex, declared_field_type)
            envs.append(env1)
        env2 = envs_or(envs)

        # XXX: Should also ensure that each declared field is specified exactly once.

        return ( parse_type_string(record_type_name), env2 )

    elif p in [
        r"{SETTABLE} : the {DSBN} field of the surrounding agent's Agent Record",
        r"{SETTABLE} : the {DSBN} field of the calling surrounding's Agent Record", # XXX
    ]:
        [dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        assert dsbn_name in fields_for_record_type_named_['Agent Record'], dsbn_name
        return ( fields_for_record_type_named_['Agent Record'][dsbn_name], env0 )

    elif p == r'{SETTABLE} : the {DSBN} field of the element in {DOTTING} whose {DSBN} is {PREFIX_PAREN}':
        [dsbn1, dotting, dsbn2, pp] = children
        (list_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        telm = list_type.element_type
        dsbn_name1 = dsbn1.source_text()[2:-2]
        dsbn_name2 = dsbn2.source_text()[2:-2]
        assert telm == T_Agent_Events_Record
        assert dsbn_name2 == 'AgentSignifier'
        env1.assert_expr_is_of_type(pp, T_agent_signifier_)
        assert dsbn_name1 == 'EventList'
        return ( fields_for_record_type_named_['Agent Events Record'][dsbn_name1], env1 )

    elif p == r'{EXPR} : an Iterator object ({h_emu_xref}) whose `next` method iterates over all the String-valued keys of enumerable properties of {var}. The iterator object is never directly accessible to ECMAScript code. The mechanics and order of enumerating the properties is not specified but must conform to the rules specified below':
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_Iterator_object_, env1)

    elif p == r'{EX} : the base value component of {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Reference)
        return (T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number | T_Environment_Record, env1)

    elif p == r"{PP_NAMED_OPERATION_INVOCATION} : {NAMED_OPERATION_INVOCATION}":
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded)
        if noi_t == T_TBD:
            # Don't do the comparison to Normal,
            # because that loses the TBD-ness,
            # which is used as a sentinel all over.
            return (noi_t, env1)
        else:
            # (normal_part_of_type, abrupt_part_of_type) = noi_t.split_by(T_Normal)
            # if abrupt_part_of_type != T_0:
            #     add_pass_error(
            #         expr,
            #         "warning: `%s` static type includes `%s`, but isn't prefixed by ! or ?"
            #         % (expr.source_text(), abrupt_part_of_type)
            #     )
            #     # But that might be okay.
            #     # E.g. Return {NAMED_OPERATION_INVOCATION} -- inserting a '?' would have no effect.
            #     # or if next instruction is ReturnIfAbrupt.
            #     # So I dropped this warning,
            #     # and just rely on Abrupt values being flagged if necessary down the line.
            return (noi_t, env1)

    elif p == r'{PP_NAMED_OPERATION_INVOCATION} : ! {NAMED_OPERATION_INVOCATION}':
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0)

        if noi_t == T_TBD:
            return (T_TBD, env1)

        (abrupt_part_of_type, normal_part_of_type) = noi_t.split_by(T_Abrupt)

        if abrupt_part_of_type == T_0:
            # add_pass_error(
            #     noi,
            #     "The static type of the invocation is `%s`, so shouldn't need a '!'" % str(noi_t)
            # )
            # There are a lot of these now, and it's only goig to increase.
            pass
        else:
            # add_pass_error(
            #     expr,
            #     "STA fails to confirm that `%s` will return a Normal" % noi.source_text()
            # )
            # It's unsurprising, perhaps even *expected*,
            # that STA can't confirm it.
            pass

        return (normal_part_of_type, env1)

    elif p == r'{PP_NAMED_OPERATION_INVOCATION} : ? {NAMED_OPERATION_INVOCATION}':
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0)

        if noi_t == T_TBD:
            return (T_TBD, env1)

        (abrupt_part_of_type, normal_part_of_type) = noi_t.split_by(T_Abrupt)

        if normal_part_of_type == T_0:
            add_pass_error(
                expr,
                "used '?', but STA says operation can't return normal: " + expr.source_text()
            )

        if abrupt_part_of_type == T_0:
            add_pass_error(
                expr,
                "used '?', but STA says operation can't return abrupt: " + expr.source_text()
            )

        proc_add_return(env1, abrupt_part_of_type, expr)

        # RequireInternalSlot is a quasi-type-test.
        env2 = env1
        if str(noi.prod) == '{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}':
            [pp] = noi.children
            assert str(pp.prod).startswith(r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})')
            [opn_before_paren, exlist_opt] = pp.children[0:2]
            if opn_before_paren.source_text() == 'RequireInternalSlot':
                # This amounts to a type-test.
                # I.e., in the not-returning-early env resulting from this NAMED_OPERATION_INVOCATION,
                # we can narrow the type of the first arg to RequireInternalSlot.
                (obj_arg, slotname_arg) = exes_in_exlist_opt(exlist_opt)
                env2 = env1.with_expr_type_narrowed(obj_arg, T_Object)
                # XXX Depending on the slotname_arg, we could narrow it further.

        return (normal_part_of_type, env2)

    elif p == r"{TYPE_ARG} : {var}'s base value component":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return_type = T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number | T_Environment_Record
        return (return_type, env0)

    elif p == r'{EX} : the strict reference flag of {var}':
        [v] = children
        env0.assert_expr_is_of_type(v, T_Reference)
        return (T_Boolean, env0)

    elif p in [
        r"{SETTABLE} : the running execution context's {EXECUTION_CONTEXT_COMPONENT}",
        r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of the running execution context",
    ]:
        [component_name] = children
        t = {
            'LexicalEnvironment' : T_Environment_Record,
            'VariableEnvironment': T_Environment_Record,
            'PrivateEnvironment' : T_Environment_Record, # PR 1668 privates
        }[component_name.source_text()]
        return (t, env0)

    elif p == r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary32 value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_IEEE_binary32_, env1)

    elif p == r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary64 value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_IEEE_binary64_, env1)

    elif p == r"{EXPR} : a copy of {var}'s _captures_ List":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_captures_list_, env1)

    elif p in [
        r"{SETTABLE} : {var}[{EX}]",
        r"{SETTABLE} : {DOTTING}[{EX}]",
    ]:
        [seq_ex, subscript_var] = children
        (seq_type, seq_env) = tc_expr(seq_ex, env0); assert seq_env is env0
        env2 = env0.ensure_expr_is_of_type(subscript_var, T_Integer_); assert env2 is env0
        if isinstance(seq_type, ListType):
            item_type = seq_type.element_type
        elif seq_type == T_List:
            item_type = T_TBD
        elif seq_type.is_a_subtype_of_or_equal_to(T_Data_Block | T_Shared_Data_Block):
            item_type = T_Integer_
        elif seq_type.is_a_subtype_of_or_equal_to(T_Data_Block | T_Shared_Data_Block | T_Null):
            add_pass_error(
                expr,
                "STA fails to confirm that %s isnt Null" %
                (seq_ex.source_text())
            )
            item_type = T_Integer_
        else:
            assert 0, seq_type
        return (item_type, env0)

    elif p == r"{EXPR} : the State ({EX}, {var})":
        [ex, var] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_); assert env1 is env0
        env2 = env0.ensure_expr_is_of_type(var, T_captures_list_); assert env2 is env0
        return (T_State, env0)

    elif p == r"{EXPR} : {var}'s State":
        # todo?: change to Assert: _r_ is a State
        [var] = children
        env0.assert_expr_is_of_type(var, T_State)
        return (T_State, env0)

    elif p == r"{EXPR} : an empty Set":
        [] = children
        return (T_Set, env0)

    elif p in [
        r"{EX} : &laquo; &raquo;",
        r"{EX} : \u00ab \u00bb", # PR 1668
    ]:
        [] = children
        return (T_List, env0)

    elif p in [
        r"{EX} : &laquo; {EXLIST} &raquo;",
        r"{EX} : \u00ab {EXLIST} \u00bb",
    ]:
        [exlist] = children
        ex_types = set()
        for ex in exes_in_exlist(exlist):
            (ex_type, env1) = tc_expr(ex, env0); assert env1 is env0
            ex_types.add(ex_type)
        if len(ex_types) == 0:
            list_type = T_List # ListType(T_0)
        else:
            element_type = union_of_types(ex_types)
            list_type = ListType(element_type)
        return (list_type, env0)

    elif p == r"{SETTABLE} : the _withEnvironment_ flag of {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_object_Environment_Record)
        return (T_Boolean, env1)

    elif p == r"{EXPR} : {var}'s _captures_ List":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_captures_list_, env1)

    elif p == r"{EX} : {DSBN}":
        [dsbn] = children
        return (T_SlotName_, env0)

    elif p in [
        r"{EXPR} : a newly created Property Descriptor with no fields",
        r"{EXPR} : a new Property Descriptor that initially has no fields",
    ]:
        [] = children
        return (T_Property_Descriptor, env0)

    elif p == r"{EXPR} : the fully populated data Property Descriptor for the property, containing the specified attributes for the property. For properties listed in {h_emu_xref}, {h_emu_xref}, or {h_emu_xref} the value of the {DSBN} attribute is the corresponding intrinsic object from {var}":
        [emu_xref1, emu_xref2, emu_xref3, dsbn, var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (T_Property_Descriptor, env0)

    elif p == r"{EXPR} : {var}'s own property whose key is {var}":
        [obj_var, key_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (T_property_, env0)

    elif p == r"{SETTABLE} : {var}'s {DSBN} attribute":
        [prop_var, dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name in ['Enumerable', 'Configurable']:
            env0.assert_expr_is_of_type(prop_var, T_property_)
            result_type = T_Boolean
        elif dsbn_name in ['Value', 'Writable']:
            env0.assert_expr_is_of_type(prop_var, T_data_property_)
            result_type = T_Tangible_ if dsbn_name == 'Value' else T_Boolean
        elif dsbn_name in ['Get', 'Set']:
            env0.assert_expr_is_of_type(prop_var, T_accessor_property_)
            result_type = T_Object | T_Undefined
        else:
            assert 0
        return (result_type, env0)

    elif p == r"{SETTABLE} : the {DSBN} internal slot of this Date object":
        [dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        assert dsbn_name == 'DateValue'
        return (T_Number, env0)

    elif p == r"{EXPR} : this Source Text Module Record":
        [] = children
        return (T_Source_Text_Module_Record, env0)

    elif p == r"{EXPR} : this Cyclic Module Record":
        [] = children
        return (T_Cyclic_Module_Record, env0)

#    elif p in [
#        r"{EX} : ScriptEvaluationJob",
#        r"{EX} : TopLevelModuleEvaluationJob",
#        r"{EX} : PromiseResolveThenableJob",
#        r"{EX} : PromiseReactionJob",
#    ]:
#        [] = children
#        return (T_proc_, env0)
# ^ obsoleted by PR 1597

#    elif p == r"{EXPR} : a newly created Array exotic object":
#        [] = children
#        return (T_Array_object_, env0)
#
#    elif p == r"{EXPR} : a newly created Integer-Indexed exotic object with an internal slot for each name in {var}":
#        [var] = children
#        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
#        return (T_Integer_Indexed_object_, env1)
# ^ obsoleted by PR #1460

    elif p == r"{EX} : a newly created {ERROR_TYPE} object":
        [error_type] = children
        error_type_name = error_type.source_text()[1:-1]
        return (NamedType(error_type_name), env0)

#    elif p == r"{EXPR} : a newly created bound function exotic object with the internal slots listed in {h_emu_xref}":
#        [emu_xref] = children
#        return (T_bound_function_exotic_object_, env0)

#    elif p == r"{EXPR} : a newly created String exotic object with a {DSBN} internal slot":
#        [dsbn] = children
#        return (T_String_exotic_object_, env0)
# ^ obsoleted by PR #1460

    elif p in [
        r"{EXPR} : a copy of {var}",
        r"{EXPR} : a copy of {DOTTING}",
    ]:
        [var] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        return (t, env1)

    elif p in [
        r"{EXPR} : a copy of the List {var}",
        r"{EXPR} : a new List which is a copy of {var}",
    ]:
        [var] = children
        t = env0.assert_expr_is_of_type(var, T_List)
        return (t, env0)

    elif p == r"{EXPR} : a new List of {var} with {LITERAL} appended":
        [list_var, element] = children
        t = env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(element, t.element_type)
        return (t, env0)

    elif p in [
        r"{EXPR} : the value of the first element of {var}",
        r"{EXPR} : the first element of {var}",
        r"{EXPR} : the second element of {var}",
        r"{EXPR} : the last element in {var}",
    ]:
        # todo: replace with ad hoc record
        [var] = children
        list_type = env0.assert_expr_is_of_type(var, T_List)
        return (list_type.element_type, env0)

    elif p == r"{EXPR} : an implementation-defined Completion value":
        [] = children
        return (T_Tangible_ | T_empty_ | T_throw_, env0)

    elif p == r"{EXPR} : the element of {var} whose {DSBN} is the same as {DOTTING}":
        [list_var, dsbn, dotting] = children
        dsbn_name = dsbn.source_text()[2:-2]
        (list_type, env1) = tc_expr(list_var, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, NamedType)
        fields = fields_for_record_type_named_[et.name]
        whose_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(dotting, whose_type)
        return (et, env1)

    elif p == r"{EXPR} : the three results {var}, {var}, and {LITERAL}":
        [a, b, c] = children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        (b_t, env2) = tc_expr(b, env0); assert env2 is env0
        (c_t, env3) = tc_expr(c, env0); assert env3 is env0
        t = TupleType( (a_t, b_t, c_t) )
        return (t, env0)

    elif p == r"{EXPR} : the two results {EX} and {EX}":
        [a, b] = children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        (b_t, env2) = tc_expr(b, env0); assert env2 is env0
        t = TupleType( (a_t, b_t) )
        return (t, env0)

    elif p == r"{EXPR} : a new Record":
        # Once, in CreateIntrinsics
        [] = children
        return (T_Intrinsics_Record, env0)

    elif p == r"{EXPR} : such an object created in a host-defined manner":
        [] = children
        return (T_Object, env0)

#    elif p == r"{EXPR} : a non-empty Job Queue chosen in an implementation-defined manner. If all Job Queues are empty, the result is implementation-defined":
#        [] = children
#        return (ListType(T_PendingJob), env0)
#
#    elif p == r"{EXPR} : the PendingJob record at the front of {var}":
#        [var] = children
#        env0.assert_expr_is_of_type(var, ListType(T_PendingJob))
#        return (T_PendingJob, env0)
#
#    elif p == r"{NAMED_OPERATION_INVOCATION} : the abstract operation named by {DOTTING} using the elements of {DOTTING} as its arguments":
#        [adotting, bdotting] = children
#        env0.assert_expr_is_of_type(adotting, T_proc_)
#        env0.assert_expr_is_of_type(bdotting, T_List)
#        return (T_Tangible_ | T_empty_ | T_Abrupt, env0)
# ^ obsoleted by PR 1597

    elif p == r"{EXPR} : the canonical {h_emu_not_ref_property_name} of {var} as given in the &ldquo;Canonical {h_emu_not_ref_property_name}&rdquo; column of the corresponding row":
        [_, v, _] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the List of Unicode code points of {var}":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the canonical property value of {var} as given in the &ldquo;Canonical property value&rdquo; column of the corresponding row":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the List, in source text order, of Unicode code points in the source text matched by {PROD_REF}":
        [prod_ref] = children
        return (ListType(T_Integer_), env0)

    # ----

    elif p == r"{EXPR} : the WaiterList that is referenced by the pair ({var}, {var})":
        [sdb, i] = children
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        env0.assert_expr_is_of_type(i, T_Integer_)
        return (T_WaiterList, env0)

    elif p in [
        r"{FACTOR} : msPerDay",
        r"{FACTOR} : msPerMinute",
    ]:
        [] = children
        return (T_Integer_, env0)

    elif p == r"{EXPR} : a reference to the list of waiters in {var}":
        [wl] = children
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        return (ListType(T_agent_signifier_), env0)

    elif p == r"{EXPR} : the first waiter in {var}":
        [wl] = children
        env0.assert_expr_is_of_type(wl, ListType(T_agent_signifier_))
        return (T_agent_signifier_, env0)

    elif p in [
        r"{EX} : *this* value",
        r"{EX} : the *this* value",
    ]:
        return (T_Tangible_, env0)

    elif p in [
        r"{EXPR} : a List consisting of all of the arguments passed to this function, starting with the second argument. If fewer than two arguments were passed, the List is empty",
        r"{EXPR} : a List containing the arguments passed to this function",
        r"{EXPR} : a List whose elements are the arguments passed to this function",
        r"{EXPR} : a List whose elements are, in left to right order, the arguments that were passed to this function invocation",
        r"{EXPR} : a List whose elements are, in left to right order, the portion of the actual argument list starting with the third argument. The list is empty if fewer than three arguments were passed",
        r"{EXPR} : a zero-origined List containing the argument items in order",
        r"{EXPR} : the List of argument values starting with the second argument",
        r"{EXPR} : the List of arguments passed to this function",
    ]:
        [] = children
        return (ListType(T_Tangible_), env0)

    elif p in [
        r"{EXPR} : the actual number of arguments passed to this function",
        r"{EXPR} : the number of actual arguments minus 2",
        r"{EXPR} : the number of actual arguments",
        r"{EXPR} : the number of arguments passed to this function call",
    ]:
        [] = children
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the String value that is the result of normalizing {var} into the normalization form named by {var} as specified in {h_a}":
        [s_var, nf_var, h_a] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(nf_var, T_String)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the String value that is a copy of {var} with both leading and trailing white space removed",
        r"{EXPR} : the String value that is a copy of {var} with leading white space removed",
        r"{EXPR} : the String value that is a copy of {var} with trailing white space removed",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value containing the single code unit {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_String, env0)

# obsoleted by merge of PR #1602:
#    elif p == r"{EXPR} : a substring of {var} consisting of the leftmost code unit that is not a |StrWhiteSpaceChar| and all code units to the right of that code unit. (In other words, remove leading white space.) If {var} does not contain any such code units, let {var} be the empty string":
#        [var1, var2, var3] = children
#        assert same_source_text(var1, var2)
#        env0.assert_expr_is_of_type(var1, T_String)
#        return (T_String, env0)

    elif p == r"{EXPR} : the longest prefix of {var}, which might be {var} itself, that satisfies the syntax of a {nonterminal}":
        [var1, var2, nont] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the integer represented by the four hexadecimal digits at indices {NUM_EXPR}, {NUM_EXPR}, {NUM_EXPR}, and {NUM_EXPR} within {var}":
        [e1, e2, e3, e4, var] = children
        env0.assert_expr_is_of_type(e1, T_Integer_)
        env0.assert_expr_is_of_type(e2, T_Integer_)
        env0.assert_expr_is_of_type(e3, T_Integer_)
        env0.assert_expr_is_of_type(e4, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the integer represented by two zeroes plus the two hexadecimal digits at indices {NUM_EXPR} and {NUM_EXPR} within {var}":
        [i1, i2, var] = children
        env0.assert_expr_is_of_type(i1, T_Integer_)
        env0.assert_expr_is_of_type(i2, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : this Date object":
        [] = children
        return (T_Object | ThrowType(T_TypeError), env0)

    elif p == r"{EXPR} : the List that is {DOTTING}":
        [dotting] = children
        (dotting_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        dotting_type.is_a_subtype_of_or_equal_to(T_List)
        return (dotting_type, env0)

    elif p == r"{EXPR} : the number of leading zero bits in the 32-bit binary representation of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Integer_, env0)

    elif p == r"{EX} : the digits of the decimal representation of {var} (in order, with no leading zeroes)":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (ListType(T_code_unit_), env0)

    elif p == r"{EX} : the remaining {EX} code units of {var}":
        [ex, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        return (T_String, env1)

    elif p == r"{EX} : the first {SUM} code units of {var}":
        [summ, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(summ, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String representation of this Number value using the radix specified by {var}. Letters `a`-`z` are used for digits with values 10 through 35. The precise algorithm is implementation-defined, however the algorithm should be a generalization of that specified in {h_emu_xref}":
        [var, emu_xref] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are, in order, the elements in the List {var}. If {var} is 0, the empty String is returned":
        [list_var, len_var] = children
        env0.assert_expr_is_of_type(len_var, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are, in order, the elements in the List {var}. If {var} has no elements, the empty String is returned":
        [list_var, list_var2] = children
        assert same_source_text(list_var, list_var2)
        env0.assert_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env0)

    elif p == r"{EXPR} : the String value that is made from {var} copies of {var} appended together":
        [n_var, s_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(n_var, T_Integer_)
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value containing {var} consecutive code units from {var} beginning with the code unit at index {var}",
        r"{EXPR} : the String value containing {DOTTING} consecutive code units from {var} beginning with the code unit at index {var}",
    ]:
        [len_expr, s_var, k_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(len_expr, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(k_var, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose length is {EX}, containing code units from {var}, namely the code units with indices {var} through {EX}, in ascending order":
        [len_ex, s_var, start_var, end_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(start_var, T_Integer_)
        env0.assert_expr_is_of_type(end_var, T_Integer_)
        env0.assert_expr_is_of_type(len_ex, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : a value of Number type, whose value is {EXPR}":
        [expr] = children
        env1 = env0.ensure_expr_is_of_type(expr, T_Number)
        return (T_Number, env1)

#    elif p == r"{EXPR} : a List containing in order the code points as defined in {h_emu_xref} of {var}, starting at the first element of {var}":
#        [emu_xref, s_var, s_var2] = children
#        assert same_source_text(s_var2, s_var)
#        env0.assert_expr_is_of_type(s_var, T_String)
#        return (ListType(T_code_point_), env0)
#
#    elif p == r"{EXPR} : a List containing in order the code points of {var} when interpreted as a sequence of UTF-16 encoded code points as described in {h_emu_xref}":
#        [var, emu_xref] = children
#        env0.assert_expr_is_of_type(var, T_String)
#        return (ListType(T_code_point_), env0)
#
#    elif p == r"{EXPR} : a List where the elements are the result of toLowercase({var}), according to the Unicode Default Case Conversion algorithm":
#        [var] = children
#        env0.assert_expr_is_of_type(var, ListType(T_code_point_))
#        return (ListType(T_code_point_), env0)
# ^ obsoleted by PR 1552

    elif p in [
        r"{EX} : the GlobalSymbolRegistry List",
        r"{EX} : the GlobalSymbolRegistry List (see {h_emu_xref})",
    ]:
        return (ListType(T_GlobalSymbolRegistry_Record), env0)

    elif p == r"{EXPR} : a new unique Symbol value whose {DSBN} value is {var}":
        [dsbn, var] = children
        assert dsbn.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String | T_Undefined)
        return (T_Symbol, env0)

    elif p == r"{EXPR} : a String containing one instance of each code unit valid in {nonterminal}":
        [nont] = children
        return (T_String, env0)

    elif p == r"{EXPR} : a String containing one instance of each code unit valid in {nonterminal} plus {STR_LITERAL}":
        [nont, strlit] = children
        env0.assert_expr_is_of_type(strlit, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : a String containing one instance of each code unit valid in {nonterminal} and {nonterminal} plus {STR_LITERAL}":
        [nonta, nontb, strlit] = children
        env0.assert_expr_is_of_type(strlit, T_String)
        return (T_String, env0)

# obsoleted by merge of PR #1602:
#    elif p == r"{EXPR} : a newly created substring of {var} consisting of the first code unit that is not a {nonterminal} and all code units following that code unit. (In other words, remove leading white space.) If {var} does not contain any such code unit, let {var} be the empty string":
#        [var, nont, var2, x] = children
#        assert same_source_text(var2, var)
#        env0.assert_expr_is_of_type(var, T_String)
#        return (T_String, env0)

    elif p == r"{EXPR} : the substring of {var} consisting of all code units before the first such code unit":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the mathematical integer value that is represented by {var} in radix-{var} notation, using the letters <b>A</b>-<b>Z</b> and <b>a</b>-<b>z</b> for digits with values 10 through 35":
        [zvar, rvar] = children
        env0.assert_expr_is_of_type(zvar, T_String)
        env0.assert_expr_is_of_type(rvar, T_Integer_)
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : the String value consisting of repeated concatenations of {EX} truncated to length {var}":
        [ex, var] = children
        env0.assert_expr_is_of_type(ex, T_String)
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : the first agent in {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_agent_signifier_))
        return (T_agent_signifier_, env1)

    elif p == r"{EX} : {backticked_word}":
        [backticked_word] = children
        word = backticked_word.source_text()[1:-1]
        if word in ['add', 'and', 'second', 'or', 'subtract', 'xor', 'compareExchange']:
            return (T_ReadModifyWrite_modification_closure, env0)
        elif word == 'General_Category':
            return (T_Unicode_code_points_, env0)
        else:
            assert 0, word

    elif p == r"{EXPR} : the number of elements of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the Record { {DSBN}, {DSBN} } that is the value of {EX}":
        [dsbna, dsbnb, ex] = children
        assert dsbna.source_text() == '[[Key]]'
        assert dsbnb.source_text() == '[[Value]]'
        env0.assert_expr_is_of_type(ex, T_MapData_record_)
        return (T_MapData_record_, env0)

    elif p == r"{EXPR} : the intrinsic function {percent_word}":
        [percent_word] = children
        return (T_function_object_, env0)

    elif p == r"{EX} : the first {var} code units of {var}":
        [n, s] = children
        env0.assert_expr_is_of_type(n, T_Integer_)
        env0.assert_expr_is_of_type(s, T_String)
        return (ListType(T_code_unit_), env0)

    elif p == r"{EX} : the trailing substring of {var} starting at index {var}":
        [s, n] = children
        env0.assert_expr_is_of_type(s, T_String)
        env0.assert_expr_is_of_type(n, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value equal to the substring of {var} consisting of the code units at indices {var} (inclusive) through {var} (exclusive)":
        [s, start, end] = children
        env0.assert_expr_is_of_type(s, T_String)
        env0.assert_expr_is_of_type(start, T_Integer_)
        env0.assert_expr_is_of_type(end, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : a List whose first element is {var} and whose subsequent elements are the elements of {var}, in order",
        r"{EXPR} : a List whose first element is {var} and whose subsequent elements are the elements of {var}, in order. {var} may contain no elements",
    ]:
        [head_var, tail_var] = children[0:2]
        env0.assert_expr_is_of_type(head_var, T_Tangible_)
        env1 = env0.ensure_expr_is_of_type(tail_var, ListType(T_Tangible_))
        return (ListType(T_Tangible_), env1)

    elif p == r"{EXPR} : a List whose first element is {var} and whose subsequent elements are, in left to right order, the arguments that were passed to this function invocation":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : a new (possibly empty) List consisting of all of the argument values provided after {var} in order":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : the String value for the list-separator String appropriate for the host environment's current locale (this is derived in an implementation-defined way)":
        [] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the larger of 0 and the result of {var} minus the number of elements of {var}":
        [num_var, list_var] = children
        env0.assert_expr_is_of_type(list_var, T_List)
        env1 = env0.ensure_expr_is_of_type(num_var, T_Integer_)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the intrinsic object listed in column one of {h_emu_xref} for {DOTTING}":
        [emu_xref, dotting] = children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_function_object_, env0)

#    elif p == r"{EXPR} : the result of parsing and evaluating {var} as if it was the source text of an ECMAScript {nonterminal}. The extended PropertyDefinitionEvaluation semantics defined in {h_emu_xref} must not be used during the evaluation":
#        [svar, nont, emu_xref] = children
#        env0.assert_expr_is_of_type(svar, T_String)
#        return (T_Tangible_ | T_throw_, env0)
# ^ obsoleted by PR 1552

    elif p == r"{EXPR} : the result of parsing and evaluating {PP_NAMED_OPERATION_INVOCATION} as if it was the source text of an ECMAScript {nonterminal}. The extended PropertyDefinitionEvaluation semantics defined in {h_emu_xref} must not be used during the evaluation":
        [noi, nont, emu_xref] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return (T_Tangible_ | T_throw_, env0)

    elif p == r"{EXPR} : the String value containing {var} occurrences of {code_unit_lit}":
        [n, lit] = children
        env0.assert_expr_is_of_type(lit, T_code_unit_)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value consisting of the first 10 code units of {var}":
        [v] = children
        env0.assert_expr_is_of_type(v, T_String)
        return (T_String, env0)

    elif p == r"{EX} : the current value of {var}":
        [var] = children
        (var_t, var_env) = tc_expr(var, env0); assert var_env is env0
        return (var_t, env0)

    elif p == "{EXPR} : a String in the form of a {nonterminal} ({nonterminal} if {var} contains *\"u\"*) equivalent to {var} interpreted as UTF-16 encoded Unicode code points ({h_emu_xref}), in which certain code points are escaped as described below. {var} may or may not be identical to {var}; however, the Abstract Closure that would result from evaluating {var} as a {nonterminal} ({nonterminal} if {var} contains *\"u\"*) must behave identically to the Abstract Closure given by the constructed object's {DSBN} internal slot. Multiple calls to this abstract operation using the same values for {var} and {var} must produce identical results":
        # XXX
        return (T_String, env0)

    elif p == r"{EX} : NewTarget":
        [] = children
        return (T_constructor_object_ | T_Undefined, env0)

    elif p == r"{EXPR} : the active function object":
        [] = children
        return (T_function_object_, env0)

    elif p == "{EX} : {h_code_quote}":
        [h_code_quote] = children
        return (T_String, env0)
        
    elif p == r"{EXPR} : the {var} that was passed to this function by {DSBN} or {DSBN}":
        [var, dsbna, dsbnb] = children
        assert var.source_text() == '_argumentsList_'
        # It's not a reference to an in-scope variable,
        # it's a reference to a variable at a higher level.
        # It's more of a reminder of where the '_args_' parameter comes from.
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : the Number that is the time value (UTC) identifying the current time":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the time value (UTC) identifying the current time":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of parsing {var} as a date, in exactly the same manner as for the `parse` method ({h_emu_xref})":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the String value of the Constructor Name value specified in {h_emu_xref} for this <var>TypedArray</var> constructor":
        [emu_xref] = children
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the element in {DOTTING} whose {DSBN} is {EX}",
        r"{EXPR} : the element of {DOTTING} whose {DSBN} field is {var}",
    ]:
        [dotting, dsbn, e] = children
        # over-specific:
        if ' in ' in p:
            env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
            assert dsbn.source_text() == '[[AgentSignifier]]'
            env0.assert_expr_is_of_type(e, T_agent_signifier_)
            return (T_Agent_Events_Record, env0)
        elif ' of ' in p:
            env0.assert_expr_is_of_type(dotting, ListType(T_Chosen_Value_Record))
            assert dsbn.source_text() == '[[Event]]'
            env0.assert_expr_is_of_type(e, T_Shared_Data_Block_event)
            return (T_Chosen_Value_Record, env0)
        else:
            assert 0

    elif p == r"{EXPR} : the Agent Events Record in {DOTTING} whose {DSBN} is {PP_NAMED_OPERATION_INVOCATION}":
        [dotting, dsbn, e] = children
        env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
        assert dsbn.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(e, T_agent_signifier_)
        return (T_Agent_Events_Record, env0)

    elif p in [
        r"{EXPR} : an implementation-dependent String source code representation of {var}. The representation must conform to the rules below. It is implementation-dependent whether the representation includes bound function information or information about the target function",
        r"{EXPR} : an implementation-dependent String source code representation of {var}. The representation must conform to the rules below",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0) # XXX: spec should talk about encoding source code in UTF-16?

    elif p in [
        r"{EXPR} : the result of converting {var} to a value in IEEE 754-2019 binary32 format using roundTiesToEven mode",
        r"{EXPR} : the result of converting {var} to a value in IEEE 754-2019 binary64 format",
        r"{EXPR} : the ECMAScript Number value corresponding to {var}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        # XXX The intermediates are not really T_Number
        return (T_Number, env0)

    elif p == r"{EX} : The remainder of dividing {EX} by {EX}":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_Integer_)
        env0.assert_expr_is_of_type(b, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{PAIR} : ({EX}, {EX})":
        [a, b] = children
        # over-specific:
        env0.assert_expr_is_of_type(a, T_event_)
        env0.assert_expr_is_of_type(b, T_event_)
        return (T_event_pair_, env0)

    elif p == "{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}. Additionally, if {var} has an {DSBN} internal slot and {DOTTING} is a String, the portion of the returned String that would be matched by {nonterminal} {nonterminal} must be the value of {DOTTING}":
        var = children[0]
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

    elif p == r"{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}":
        [var, nont] = children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

    elif p == r"{EXPR} : the prefix associated with {var} in {h_emu_xref}":
        [var, xref] = children
        env0.assert_expr_is_of_type(var, T_FunctionKind2_)
        return (T_String, env0)

    # explicit-exotics:
    elif p in [
        r"{EXPR} : the internal slots listed in {h_emu_xref}",
        r"{EXPR} : the internal slots listed in {h_emu_xref}, plus {DSBN} and {DSBN}",
    ]:
        # XXX really, the *names* of the internal slots...
        return (ListType(T_SlotName_), env0)

    # PR 1554 NumericValue:
    elif p == r"{EXPR} : the result of parsing {var} using the goal symbol {nonterminal}. If {var} does not conform to the grammar, or if any elements of {var} were not matched by the parse, return {NUM_LITERAL}":
        [var, nont, var2, var3, numlit] = children
        assert var.children == var2.children
        assert var.children == var3.children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        env0.assert_expr_is_of_type(numlit, T_Number)
        proc_add_return(env0, T_Number, numlit)
        return (T_Parse_Node, env0)

    # PR 1668 privates:
    elif p == r"{EXPR} : a new unique Private Name whose {dsb_word} value is {var}":
        [dsb_word, var] = children
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

    # PR 1515 BigInt:
    elif p == r"{EX} : {PP_NAMED_OPERATION_INVOCATION} treated as a mathematical value, whether the result is a BigInt or Number":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_BigInt | T_Integer_)
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : Type({var})":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number | T_BigInt)
        return (T_LangTypeName_, env0)

    elif p == r"{EX} : {backticked_oth}":
        [_] = children
        return (T_Unicode_code_points_, env0)

    elif p == r"{backticked_oth} : ` [^`]+ `":
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the value that {var} corresponds to in {h_emu_xref}":
        [var, xref] = children
        env0.assert_expr_is_of_type(var, T_Primitive)
        assert xref.source_text() == '<emu-xref href="#table-tobigint"></emu-xref>'
        return (T_BigInt | ThrowType(T_TypeError) | ThrowType(T_SyntaxError), env0)

    elif p == r"{EXPR} : a new Synchronize event":
        [] = children
        return (T_Synchronize_event, env0)

    elif p == r"{SETTABLE} : the Synchronize event in {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (T_Synchronize_event, env0)

    elif p == r"{EXPR} : the Parse Node resulting from the parse":
        [] = children
        return (T_Parse_Node, env0)

    elif p == r"{EXPR} : the result of interpreting each of {var}'s 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors":
        [error_type] = children
        error_type_name = error_type.source_text()[1:-1]
        return (ListType(NamedType(error_type_name)), env0)

    # for PR #1961 compound_assignment
    elif p == r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} in the following table:{_indent_}{nlai}{h_figure}{_outdent_}":
        [table_result_type, var, h_figure] = children
        table_result_type_str = table_result_type.source_text()
        if table_result_type_str == 'sequence of Unicode code points':
            result_type = T_Unicode_code_points_
        elif table_result_type_str == 'abstract operation':
            # result_type = (
            #     ProcType([T_Number, T_Number], T_Number | T_throw_) 
            #     |
            #     ProcType([T_BigInt, T_BigInt], T_BigInt | T_throw_) 
            # )
            result_type = ProcType([T_Number|T_BigInt, T_Number|T_BigInt], T_Number|T_BigInt | T_throw_)
        else:
            assert 0, table_result_type_str
        return (result_type, env0)

    # PR 2109:
    elif p == r"{EXPR} : the number of parameters taken by {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Abstract_Closure)
        return (T_Integer_, env0)

    # elif p == r"{EXPR} : a List containing the 4 bytes that are the result of converting {var} to IEEE 754-2019 binary32 format using &ldquo;Round to nearest, ties to even&rdquo; rounding mode. If {var} is {LITERAL}, the bytes are arranged in big endian order. Otherwise, the bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary32 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value":
    # elif p == r"{EXPR} : a List containing the 8 bytes that are the IEEE 754-2019 binary64 format encoding of {var}. If {var} is {LITERAL}, the bytes are arranged in big endian order. Otherwise, the bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary64 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value":
    # elif p == r"{EXPR} : an implementation-dependent String value that represents {var} as a date and time in the current time zone using a convenient, human-readable form":
    # elif p == r"{EXPR} : the CharSet containing the single character that is {EXPR}":
    # elif p == r"{EXPR} : the CharSet containing the single character {var}":
    # elif p == r"{EXPR} : the ECMAScript Number value corresponding to {var}":
    # elif p == r"{EXPR} : the List (containing the|of) {nonterminal} items in {PROD_REF}, in source text order. If {PROD_REF} is not present, {var} is &laquo; &raquo;":
    # elif p == r"{EXPR} : the List of events {PREFIX_PAREN}":
    # elif p == r"{EXPR} : the String value computed by the concatenation of {EX} and {EX}":
    # elif p == r"{EXPR} : the String value consisting of {EX} followed by {EX}":
    # elif p == r"{EXPR} : the String value consisting solely of {code_unit_lit}":
    # elif p == r"{EXPR} : the String value containing the two code units {var} and {var}":
    # elif p == r"{EXPR} : the String value produced by concatenating {EX} and {EX}":
    # elif p == r"{EXPR} : the String value that is the concatenation of {EX} and {EX}":
    # elif p == r"{EXPR} : the String value that is the result of concatenating {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the String value whose elements are, in order, the elements of {var}":
    # elif p == r"{EXPR} : the character represented by {PROD_REF}":
    # elif p == r"{EXPR} : the character {code_point_lit}":
    # elif p == r"{EXPR} : the concatenation of Strings {EX} and {EX}":
    # elif p == r"{EXPR} : the concatenation of the Strings {EX} and {EX}":
    # elif p == r"{EXPR} : the concatenation of {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the concatenation of the four Strings {EX}, {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the concatenation of the three Strings {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the result of applying the subtraction operation to {var} and {var}. See the note below {h_emu_xref}":
    # elif p == r"{EXPR} : the result of concatenating the strings {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the result of concatenating {EX}, {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the string consisting of the code unit {var} followed by the code unit {var}":
    # elif p == r"{EXPR} : the string consisting of the single code unit {var}":
    # elif p == r"{EXPR} : the string that is the concatenation of {EX} and {EX}":
    # elif p == r"{EXPR} : the two results {EX} and {EX}":
    # elif p == r"{EXPR} : the {nonterminal} component of {var}":
    # elif p == r"{FIELDS} : {FIELDS}, {FIELD}":
    # elif p == r"{FIELDS} : {FIELD}":
    # elif p == r"{FIGURE} : {nlai}<figure>{I_TABLE}{nlai}</figure>":
    # elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. However, an implementation is permitted to extend the behaviour of `\w+` for values of {var} less than {NUM_LITERAL} or greater than {NUM_LITERAL}. In this case `\w+` would not necessarily throw {ERROR_TYPE} for such values.":
    # elif p == r"{IF_OPEN} : If {CONDITION}, then {SMALL_COMMAND}.":
    # elif p == r"{IF_OPEN} : If {CONDITION}, then{IND_COMMANDS}":
    # elif p == r"{IF_OPEN} : If {CONDITION}, {SMALL_COMMAND}.":
    # elif p == r"{I_BULLETS} : {_indent_}{BULLETS}{_outdent_}":
    # elif p == r"{I_TABLE} : {_indent_}{nlai}<table class="lightweight(?:-table)?">(?:.|\n)+?</table>{_outdent_}":
    # elif p == r"{NAMED_OPERATION_INVOCATION} : StringValue of the {nonterminal} of {nonterminal} {var}":
    # elif p == r"{NUM_COMPARAND} : -1":
    # elif p == r"{NUM_COMPARAND} : ({SUM})":
    # elif p == r"{OPN_BEFORE_PAREN} : (ForIn/Of(?:Head|Body)Evaluation|(?!Type\b)[A-Za-z]\w+)":
    # elif p == r"{OPN_BEFORE_PAREN} : {DOTTING}":
    # elif p == r"{OPN_BEFORE_PAREN} : {SAB_FUNCTION}":
    # elif p == r"{OPN_BEFORE_PAREN} : {var}":
    # elif p == r"{OPN_BEFORE_PAREN} : {var}.([A-Z][A-Za-z]+)":
    # elif p == r"{RECORD_CONSTRUCTOR} : (?:the |a |a new )?(Record|Chosen Value Record|ExportEntry Record|ImportEntry Record|Completion|PropertyDescriptor|PendingJob|PromiseCapability|PromiseReaction|ReadModifyWriteSharedMemory|ReadSharedMemory|ResolvedBinding Record|Script Record|Source Text Module Record|WriteSharedMemory) ?{ ?{FIELDS} ?}":
    # elif p == r"{SAB_FUNCTION} : reads-bytes-from":
    # elif p == r"{SAB_RELATION} : agent-order":
    # elif p == r"{SAB_RELATION} : happens-before":
    # elif p == r"{SAB_RELATION} : host-synchronizes-with":
    # elif p == r"{SAB_RELATION} : is agent-order before":
    # elif p == r"{SAB_RELATION} : is memory-order before":
    # elif p == r"{SAB_RELATION} : reads-from":
    # elif p == r"{SAB_RELATION} : synchronizes-with":
    # elif p == r"{SETTABLE} : the {DSBN} field of {var}":
    # elif p == r"{STR_LITERAL} : *"[^*"]*"*":
    # elif p == r"{STR_LITERAL} : the String `","` (a comma)":
    # elif p == r"{STR_LITERAL} : the String `"-"`":
    # elif p == r"{STR_LITERAL} : the empty String":
    # elif p == r"{STR_LITERAL} : the empty String `""`":
    # elif p == r"{STR_LITERAL} : the empty String value":
    # elif p == r"{STR_LITERAL} : the empty string":
    # elif p == r"{STR_LITERAL} : the single-element String `","`": # todo: element of String
    # elif p == r"{STR_LITERAL} : the string `"(not-equal|ok|timed-out)"`":
    # elif p == r"{STR_LITERAL} : the string `":"`":
    # elif p == r"{TERMINAL} : `[a-z]+`":
    # elif p == r"{TERMINAL} : `\\\\`":
    # elif p == r"{TERM} : the number of code units in {var}":
    # elif p == r"{TYPE_NAME} : Boolean":
    # elif p == r"{TYPE_NAME} : Data Block":
    # elif p == r"{TYPE_NAME} : Null":
    # elif p == r"{TYPE_NAME} : Number":
    # elif p == r"{TYPE_NAME} : Object":
    # elif p == r"{TYPE_NAME} : Reference":
    # elif p == r"{TYPE_NAME} : Shared Data Block":
    # elif p == r"{TYPE_NAME} : String":
    # elif p == r"{TYPE_NAME} : Symbol":
    # elif p == r"{TYPE_NAME} : Undefined":
    # elif p == r"{code_point_lit} : &lt;BS&gt; U+0008 (BACKSPACE)":
    # elif p == r"{code_point_lit} : U+0000 (NULL)":
    # elif p == r"{ERROR_TYPE} : *(TypeError|SyntaxError|RangeError|ReferenceError|URIError)*":

    else:
        stderr()
        stderr("tc_expr:")
        stderr('    elif p == %s:' % escape(p))
        # pdb.set_trace()
        sys.exit(0)

# ------------------------------------------------------------------------------

def escape(s):
    if '"' in s:
        return '"' + s.replace('"', r'\"') + '"'
    else:
        return 'r"' + s + '"'

def same_source_text(a, b):
    return (a.source_text() == b.source_text())

# ------------------------------------------------------------------------------

def exes_in_exlist_opt(exlist_opt):
    assert exlist_opt.prod.lhs_s == '{EXLIST_OPT}'
    if exlist_opt.prod.rhs_s == '{EPSILON}':
        return []
    elif exlist_opt.prod.rhs_s == '{EXLIST}':
        [exlist] = exlist_opt.children
        return exes_in_exlist(exlist)
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

def tc_ao_invocation(callee_op_name, args, expr, env0):
    callee_op = operation_named_[callee_op_name]
    assert callee_op.kind == 'abstract operation'
    params = callee_op.parameters_with_types
    env1 = tc_args(params, args, env0, expr)
    return_type = callee_op.return_type
    return (return_type, env1)

def tc_sdo_invocation(op_name, main_arg, other_args, context, env0):
    op = operation_named_[op_name]
    assert op.kind == 'syntax-directed operation'

    env1 = env0.ensure_expr_is_of_type(main_arg, T_Parse_Node)
    # XXX expectation should be specific to what the callee accepts

    env2 = tc_args(op.parameters_with_types, other_args, env1, context)

    # seed:
    # if op_name == 'Evaluation': return (T_Tangible_, env0)
    # 'Contains': T_Boolean

    rt = op.return_type

    if op_name == 'Evaluation':
        # In some (most?) cases, evaluation can't return the full gamut of abrupt completions.
        # So sometimes, we can provide a narrower return type.
        assert T_Abrupt.is_a_subtype_of_or_equal_to(rt)
        mast = main_arg.source_text()
        if mast in [
            '|AsyncArrowFunction|',
            'this |FunctionExpression|', 
            'this |ArrowFunction|',
            'this |GeneratorExpression|',
            'this |AsyncGeneratorExpression|',
            'this |AsyncFunctionExpression|',
            'this |AsyncArrowFunction|',
        ]:
            rt = T_function_object_

        elif mast in [
            '|FunctionStatementList|',
        ]:
            # Might return a throw|return completion, but not continue|break
            (_, narrowed_rt) = rt.split_by(T_continue_ | T_break_)
            rt = narrowed_rt

        elif mast in [
            '_scriptBody_',
            '_body_', # |ScriptBody|
            '_lhs_', 
            '_module_.[[ECMAScriptCode]]',
            '|DestructuringAssignmentTarget|',
            '|PropertyName|',
        ]:
            # Might return a throw completion, but not return|continue|break
            (_, narrowed_rt) = rt.split_by(T_continue_ | T_break_ | T_return_)
            rt = narrowed_rt

    return (rt, env2)

def with_fake_param_names(param_types):
    return [
        ('$%d' % (i+1), t )
        for (i, t) in enumerate(param_types)
    ]
        
def type_corresponding_to_comptype_literal(comptype_literal):
    assert isinstance(comptype_literal, ANode)
    return {
        '~normal~'  : T_Normal,
        '~continue~': T_continue_,
        '~break~'   : T_break_,
        '~return~'  : T_return_,
        '~throw~'   : T_throw_,
    }[comptype_literal.source_text()]

def tc_args( params, args, env0, context ):
    assert len(args) <= len(params)
    out_env = env0
    for ((param_name, param_type), arg) in zip_longest(params, args):

        if param_type == T_TBD:
            # Not much useful checking we can do.
            passed_part_of_param_type     = T_TBD
            not_passed_part_of_param_type = T_TBD
        else:
            (not_passed_part_of_param_type, passed_part_of_param_type) = param_type.split_by(T_not_passed)

        if arg is None:
            # No arg was passed to this parameter.
            if not_passed_part_of_param_type != T_0:
                # but the parameter is optional, so that's okay.
                pass
            else:
                # the parameter is not optional!
                add_pass_error(
                    context,
                    "No arg passed to non-optional param '%s'" % param_name
                )
        else:
            (arg_type, env1) = tc_expr(arg, env0)

            pt = passed_part_of_param_type

            env2 = env1 # overwritten in one case below:

            # Treat T_TBD like Top
            if pt == T_TBD:
                # This should only happen if the called operation
                # is in the same cluster as the calling operation.
                # (In particular, if the operation is calling itself.)
                #
                # Conceivably, we could go to the called operation and tell it
                # that this parameter must be able to accept arg_type.
                # However, let's assume that the current mechanisms will take care of it.
                # That is, by the end of this pass (on this cluster),
                # that pt will be refined,
                # and, in a subsequent pass, we'll be checking against that refined type.
                pass
            elif arg_type == T_TBD:
                env2 = env1.ensure_expr_is_of_type(arg, pt)
            elif arg_type.is_a_subtype_of_or_equal_to(pt):
                # normal case
                pass
            elif arg_type == T_List and isinstance(pt, ListType):
                # XXX: Still need this?
                # This happens when the arg is an List constructor with no items.
                # Not really worth complaining about.
                pass
            else:
                if (
                    # This condition, by focusing on T_throw_, is over-specific,
                    # but I'm guessing it catches the common cases.
                    T_throw_.is_a_subtype_of_or_equal_to(arg_type)
                    and
                    not T_throw_.is_a_subtype_of_or_equal_to(pt)
                ):
                    extra_msg = f' (arg could be abrupt completion?)'
                else:
                    extra_msg = ''

                add_pass_error(
                    arg,
                    "arg %s has type %s, but param %s requires type %s%s"
                    % (arg.source_text(), arg_type, param_name, pt, extra_msg)
                )
                # The parameter-type might be too narrow,
                # or the arg-type might be too wide.
                # We don't know which is the problem.
                # So we just note the mismatch and go on. Hm.

            out_env = env_and(out_env, env2)

    return out_env

# ------------------------------------------------------------------------------

def is_simple_call(ex):
    prefix_paren = ex.is_a('{PREFIX_PAREN}')
    if prefix_paren is None: return None
    if prefix_paren.prod.rhs_s != '{OPN_BEFORE_PAREN}({EXLIST_OPT})': return None
    [opn, exlist_opt] = prefix_paren.children

    if opn.prod.rhs_s in ['{DOTTING}', '{var}', '{var}.{cap_word}']: return None
    op_name = opn.source_text()

    var = exlist_opt.is_a('{var}')
    if var is None: return None

    return (op_name, var)

# ------------------------------------------------------------------------------

def get_field_names(fields):
    return [
        dsbn_name
        for (dsbn_name, ex) in get_field_items(fields)
    ]

def get_field_items(fields):
    for field in get_fields(fields):
        assert str(field.prod) == '{FIELD} : {DSBN}: {EX}'
        [dsbn, ex] = field.children
        dsbn_name = dsbn.source_text()[2:-2]
        yield (dsbn_name, ex)

def get_fields(fields):
    assert fields.prod.lhs_s == '{FIELDS}'
    if fields.prod.rhs_s == '{FIELDS}, {FIELD}':
        [prefields, field] = fields.children
        return get_fields(prefields) + [field]

    elif fields.prod.rhs_s == '{FIELD}':
        [field] = fields.children
        return [field]

    else:
        assert 0

# ------------------------------------------------------------------------------

fields_for_record_type_named_ = {

    'Property Descriptor': { # XXX not modelling this very well
        # table 2
        'Value'       : T_Tangible_,
        'Writable'    : T_Boolean,
        # table 3
        'Get'         : T_Object | T_Undefined, # | T_not_in_record
        'Set'         : T_Object | T_Undefined, # | T_not_in_record
        # common
        'Enumerable'  : T_Boolean,
        'Configurable': T_Boolean,
    },

    #? # 2651: Table 8: Completion Record Fields
    #? 'Completion Record': {
    #?     'Type'   : T_completion_kind_,
    #?     'Value'  : T_Tangible_ | T_empty_,
    #?     'Target' : T_String | T_empty_,
    #? },

    # PR 1668 privates:
    # Table 9:
    'PrivateField' : {
        'PrivateName'      : T_Private_Name,
        'PrivateFieldValue': T_Tangible_,
    },
    # Table 10:
    'ClassFieldDefinition Record' : {
        'Name'                          : T_Private_Name | T_String | T_Symbol,
        'Initializer'                   : T_function_object_ | T_empty_,
        'IsAnonymousFunctionDefinition' : T_Boolean,
    },
    # Table 11:
    'Private Name' : {
        'Description': T_String,
        'Kind'       : T_String,
        'Brand'      : T_Object, # T_Tangible_, XXX
        'Value'      : T_function_object_,
        'Get'        : T_function_object_,
        'Set'        : T_function_object_,
    },

    # 8.1
    'Environment Record': {
        'OuterEnv'         : T_Environment_Record,
    },

    'declarative Environment Record': {
        'OuterEnv' : T_Environment_Record,
    },

    'object Environment Record': {
        'OuterEnv'         : T_Environment_Record,
    },

    # 8.1.1.3 Table 16: Additional Fields of Function Environment Records
    'function Environment Record': {
        'OuterEnv'         : T_Environment_Record,
        'ThisValue'        : T_Tangible_,
        'ThisBindingStatus': T_this_binding_status_, # T_String, # enumeration
        'FunctionObject'   : T_function_object_,
        'HomeObject'       : T_Object | T_Undefined,
        'NewTarget'        : T_Object | T_Undefined,
    },

    # 8.1.1.4 Table 18: Additional Fields of Global Environment Records
    'global Environment Record': {
        'OuterEnv'         : T_Environment_Record,
        'ObjectRecord'     : T_object_Environment_Record,
        'GlobalThisValue'  : T_Object,
        'DeclarativeRecord': T_declarative_Environment_Record,
        'VarNames'         : ListType(T_String),
    },

    'module Environment Record': {
        'OuterEnv'         : T_Environment_Record,
    },

    # 8.2 Realms: Table 21: Realm Record Fields
    'Realm Record': {
        'Intrinsics'  : T_Intrinsics_Record,
        'GlobalObject': T_Object,
        'GlobalEnv'   : T_Environment_Record,
        'TemplateMap' : ListType(T_templateMap_entry_),
        'HostDefined' : T_host_defined_ | T_Undefined,
    },

    # 8.2: NO TABLE
    'templateMap_entry_': {
        'Site'    : T_Parse_Node,
        'Array'   : T_Object,
    },

    # 8.4.1
    'JobCallback Record': {
        'Callback'    : T_function_object_,
        'HostDefined' : T_Top_,
    },

    # 8.6 Agents: Agent Record Fields
    'Agent Record': {
        'LittleEndian': T_Boolean,
        'CanBlock'    : T_Boolean,
        'Signifier'   : T_agent_signifier_,
        'IsLockFree1' : T_Boolean,
        'IsLockFree2' : T_Boolean,
        'IsLockFree8' : T_Boolean,
        'CandidateExecution': T_candidate_execution,
        'KeptAlive'   : ListType(T_Object),
    },

#    # 7343: Table 25: PendingJob Record Fields
#    'PendingJob': {
#        'Job'           : T_proc_,
#        'Arguments'     : T_List,
#        'Realm'         : T_Realm_Record,
#        'ScriptOrModule': T_Script_Record | T_Module_Record,
#        'HostDefined'   : T_host_defined_ | T_Undefined,
#    },
# ^ obsoleted by PR 1597

    # 5515+5660: NO TABLE, not even a mention
    'iterator_record_': {
        'Iterator'  : T_Object, # iterator_object_ ?
        'NextMethod': T_function_object_,
        'Done'      : T_Boolean,
    },

    # 11933: NO TABLE, no mention
    'CodePointAt_record_': {
        'CodePoint'          : T_code_point_,
        'CodeUnitCount'      : T_Integer_,
        'IsUnpairedSurrogate': T_Boolean,
    },

    # PR 1892 (add import.meta):
    # 14234: no table
    'ImportMeta_record_': {
        'Key'   : T_String | T_Symbol,
        'Value' : T_Tangible_,
    },

    # 21275: NO TABLE, no mention
    'methodDef_record_': {
        'Closure' : T_function_object_,
        'Key'     : T_String | T_Symbol,
    },

    # 21832: Script Record Fields
    'Script Record': {
        'Realm'         : T_Realm_Record | T_Undefined,
        'Environment'   : T_Environment_Record | T_Undefined,
        'ECMAScriptCode': T_PTN_Script,
        'HostDefined'   : T_host_defined_ | T_Undefined,
    },

    # 22437: Table 36: Module Record Fields
    'Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
        'Status'          : T_module_record_status_, # T_String, # see Issue 1455
    },

    'other Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
    },

    # 
    'Cyclic Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
        #
        'Status'          : T_module_record_status_, # T_String,
        'EvaluationError'  : T_throw_ | T_Undefined,
        'DFSIndex'         : T_Integer_ | T_Undefined,
        'DFSAncestorIndex' : T_Integer_ | T_Undefined,
        'RequestedModules' : ListType(T_String),
    },

    # 23406: Table 38: Additional Fields of Source Text Module Records
    'Source Text Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
        #
        'Status'          : T_module_record_status_, # T_String,
        'EvaluationError'  : T_throw_ | T_Undefined,
        'DFSIndex'         : T_Integer_ | T_Undefined,
        'DFSAncestorIndex' : T_Integer_ | T_Undefined,
        'RequestedModules' : ListType(T_String),
        #
        'Context'              : T_execution_context | T_empty_, # PR 1670
        'ECMAScriptCode'       : T_Parse_Node,
        'ImportMeta'           : T_Object | T_empty_, # PR 1892
        'ImportEntries'        : ListType(T_ImportEntry_Record),
        'LocalExportEntries'   : ListType(T_ExportEntry_Record),
        'IndirectExportEntries': ListType(T_ExportEntry_Record),
        'StarExportEntries'    : ListType(T_ExportEntry_Record),
    },

    # 23376
    'ResolvedBinding Record': {
        'Module'      : T_Module_Record,
        'BindingName' : T_String,
    },

    # 23490: Table 39: ImportEntry Record Fields
    'ImportEntry Record': {
        'ModuleRequest': T_String,
        'ImportName'   : T_String,
        'LocalName'    : T_String,
    },

    # 23627: Table 41: ExportEntry Record Fields
    'ExportEntry Record': {
        'ExportName'    : T_String | T_Null,
        'ModuleRequest' : T_String | T_Null,
        'ImportName'    : T_String | T_Null,
        'LocalName'     : T_String | T_Null,
    },

    # 24003
    'ExportResolveSet_Record_': {
        'Module'     : T_Module_Record,
        'ExportName' : T_String,
    },

    # 28088: table-44: GlobalSymbolRegistry Record Fields
    'GlobalSymbolRegistry Record': {
        'Key'   : T_String,
        'Symbol': T_Symbol,
    },

    # 38121 24.5.2: JSON.stringify: no table, no mention
    'JSON_Stringify_state_record_': {
        'ReplacerFunction': T_function_object_ | T_Undefined,
        'Stack'           : ListType(T_Object),
        'Indent'          : T_String,
        'Gap'             : T_String,
        'PropertyList'    : ListType(T_String) | T_Undefined,
    },

    # 25.2.3.2 FinalizationRegistry.prototype.register
    'FinalizationRegistryCellRecord_': {
        'WeakRefTarget'  : T_Object,
        'HeldValue'      : T_Tangible_,
        'UnregisterToken': T_Object | T_empty_,
    },

    # 26.6.1.1 PromiseCapability Record Fields
    'PromiseCapability Record': {
        'Promise' : T_Object | T_Undefined,
        'Resolve' : T_function_object_ | T_Undefined,
        'Reject'  : T_function_object_ | T_Undefined,
    },

    # 26.6.1.2 PromiseReaction Record Fields
    'PromiseReaction Record': {
        'Capability' : T_PromiseCapability_Record | T_Undefined,
        'Type'       : T_settlement_type_, # T_String,
        'Handler'    : T_JobCallback_Record | T_empty_,
    },

    # 39099: no table, no mention
    'MapData_record_': {
        'Key'   : T_Tangible_ | T_empty_,
        'Value' : T_Tangible_ | T_empty_,
    },

    # 39328: 28.2 Agent Events Record Fields
    'Agent Events Record' : {
        'AgentSignifier'       : T_agent_signifier_,
        'EventList'            : ListType(T_event_),
        'AgentSynchronizesWith': ListType(T_event_pair_),
    },

    # 39380: Candidate Execution Record Fields
    'candidate execution': {
        'EventsRecords'       : ListType(T_Agent_Events_Record),
        'ChosenValues'        : ListType(T_Chosen_Value_Record),
        'AgentOrder'          : T_Relation,
        'ReadsBytesFrom'      : ProcType([T_event_], ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)),
        'ReadsFrom'           : T_Relation,
        'HostSynchronizesWith': T_Relation,
        'SynchronizesWith'    : T_Relation,
        'HappensBefore'       : T_Relation,
    },

    # 39415: CreateResolvingFunctions NO TABLE, not even mentioned
    # 29803: `Promise.all` Resolve Element Functions NO TABLE, barely mentioned
    'boolean_value_record_': {
        'Value' : T_Boolean,
    },

    # 39438: CreateResolvingFunctions NO TABLE, not even mentioned
    'ResolvingFunctions_record_': {
        'Resolve' : T_function_object_,
        'Reject'  : T_function_object_,
    },

    # 39769: NO TABLE, not even mentioned
    'Job_record_': {
        'Job'  : T_Job,
        'Realm': T_Realm_Record,
    },

    # 39784: PerformPromiseAll NO TABLE, not even mentioned
    'integer_value_record_': {
        'Value' : T_Integer_,
    },

    # 40060 ...
    'Shared Data Block event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
    },

    # repetitive, but easier than factoring out...
    'ReadSharedMemory event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
    },

    'WriteSharedMemory event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
        'Payload'     : ListType(T_Integer_),
    },

    'ReadModifyWriteSharedMemory event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
        'Payload'     : ListType(T_Integer_),
        'ModifyOp'    : T_ReadModifyWrite_modification_closure,
    },

    # 40224: Chosen Value Record Fields
    'Chosen Value Record': {
        'Event'       : T_Shared_Data_Block_event,
        'ChosenValue' : ListType(T_Integer_),
    },
    # 41899: AsyncGeneratorRequest Record Fields
    'AsyncGeneratorRequest Record': {
        'Completion' : T_Tangible_ | T_empty_ | T_return_ | T_throw_,
        'Capability' : T_PromiseCapability_Record,
    },

}


type_of_internal_thing_ = {

    # Ordinary Object Internal Methods and Internal Slots
    'Prototype'  : T_Object | T_Null,
    'Extensible' : T_Boolean,

    # PR 1668 privates:
    'PrivateFieldValues' : ListType(T_PrivateField),
    'PrivateBrands'      : ListType(T_Tangible_),

    # 1188: Table 5: Essential Internal Methods
    # (Properly, this info *should* be taken from the results of STA.)
    'GetPrototypeOf'    : ProcType([                                             ], T_Object | T_Null                   | T_throw_),
    'SetPrototypeOf'    : ProcType([T_Object | T_Null                            ], T_Boolean                           | T_throw_),
    'IsExtensible'      : ProcType([                                             ], T_Boolean                           | T_throw_),
    'PreventExtensions' : ProcType([                                             ], T_Boolean                           | T_throw_),
    'GetOwnProperty'    : ProcType([T_String | T_Symbol                          ], T_Property_Descriptor | T_Undefined | T_throw_),
    'DefineOwnProperty' : ProcType([T_String | T_Symbol, T_Property_Descriptor   ], T_Boolean                           | T_throw_),
    'HasProperty'       : ProcType([T_String | T_Symbol                          ], T_Boolean                           | T_throw_),
    'Get'               : ProcType([T_String | T_Symbol, T_Tangible_             ], T_Tangible_                         | T_throw_),
    'Set'               : ProcType([T_String | T_Symbol, T_Tangible_, T_Tangible_], T_Boolean                           | T_throw_),
    'Delete'            : ProcType([T_String | T_Symbol                          ], T_Boolean                           | T_throw_),
    'OwnPropertyKeys'   : ProcType([                                             ], ListType(T_String | T_Symbol)       | T_throw_),

    # 1328: Table 6: Additional Essential Internal Methods of Function Objects
    'Call'              : ProcType([T_Tangible_, ListType(T_Tangible_)           ], T_Tangible_                         | T_throw_),
    'Construct'         : ProcType([ListType(T_Tangible_), T_Object              ], T_Object                            | T_throw_),

    # 4407
    'NumberData' : T_Number,
    # 4423
    'SymbolData' : T_Symbol,
    # 5994
    'BigIntData' : T_BigInt,

    # 5253: NO TABLE, no mention
    'IteratedList'          : ListType(T_Tangible_),
    'ListNextIndex'         : T_Integer_,

    # 8329: Table 30: Internal Slots of ECMAScript Function Objects
    'Environment'      : T_Environment_Record,
    'PrivateEnvironment' : T_Environment_Record, # PR 1668 privates
    'FormalParameters' : T_Parse_Node,
    'FunctionKind'     : T_FunctionKind2_, # T_String, # could be more specific
    'IsClassConstructor': T_Boolean, # PR 15xx re FunctionKind
    'ECMAScriptCode'   : T_Parse_Node,
    'ConstructorKind'  : T_constructor_kind_, # T_String, # could be more specific
    'Realm'            : T_Realm_Record,
    'ScriptOrModule'   : T_Script_Record | T_Module_Record | T_Null, # XXX must add Null to spec
    'ThisMode'         : T_this_mode,
    'Strict'           : T_Boolean,
    'HomeObject'       : T_Object,
    'SourceText'       : T_Unicode_code_points_,
    'Fields'           : ListType(T_ClassFieldDefinition_Record), # PR 1668 privates
    'ClassFieldInitializer': T_Boolean, # PR 1668
    'PrivateBrand'     : T_Object, # PR 1668: XXX not in table 

    # 8860: 
    'InitialName' : T_Null | T_String,

    # 9078: Table 28: Internal Slots of Exotic Bound Function Objects
    'BoundTargetFunction': T_function_object_,
    'BoundThis'          : T_Tangible_,
    'BoundArguments'     : ListType(T_Tangible_),

    # 9373 NO TABLE
    'StringData' : T_String,

    # 9506: Arguments Exotic Objects NO TABLE
    'ParameterMap' : T_Object,

    # 9735: MakeArgGetter NO TABLE
    'Name' : T_String,
    'Env'  : T_Environment_Record,

    # 9806: Integer Indexed Exotic Objects NO TABLE
    'ViewedArrayBuffer' : T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_, #?
    'ArrayLength'       : T_Integer_,
    'ByteOffset'        : T_Integer_,
    'ContentType'       : T_numeric_primitive_type_, # T_String,
    'TypedArrayName'    : T_String,

    # 10066: Table 29: Internal Slots of Module Namespace Exotic Objects
    'Module'     : T_Module_Record,
    'Exports'    : ListType(T_String),

    # 9.5 Proxy Object Internal Methods and Internal Slots
    'ProxyHandler' : T_Object | T_Null,
    'ProxyTarget'  : T_Object | T_Null,

    # 18100: Properties of For-In Iterator Instances
    'Object'          : T_Object,
    'ObjectWasVisited': T_Boolean,
    'VisitedKeys'     : ListType(T_String),
    'RemainingKeys'   : ListType(T_String),

    # 27137: Properties of Boolean Instances NO TABLE
    'BooleanData' : T_Boolean,

    # 30688
    'DateValue': T_Number,

    # 30738: Table 46: Internal Slots of String Iterator Instances
    'IteratedString' : T_String,
    'StringNextIndex': T_Integer_,

    # 32711: Properties of RegExp Instances NO TABLE
    'RegExpMatcher'  : ProcType([T_String, T_Integer_], T_MatchResult),
    'OriginalSource' : T_String,
    'OriginalFlags'  : T_String,

    # 34123: Table 48: Internal Slots of Array Iterator Instances
    'IteratedArrayLike'      : T_Object,
    'ArrayLikeNextIndex'     : T_Integer_,
    'ArrayLikeIterationKind' : T_iteration_result_kind_, # T_String,

    # 35373 + 37350 NO TABLE
    'ByteLength' : T_Integer_,

    # 35719: Table 50: Internal Slots of Map Iterator Instances
    'IteratedMap'      : T_Object,
    'MapNextIndex'     : T_Integer_,
    'MapIterationKind' : T_iteration_result_kind_, # T_String,

    # 36073: Table 51: Internal Slots of Set Iterator Instances
    'IteratedSet'      : T_Object,
    'SetNextIndex'     : T_Integer_,
    'SetIterationKind' : T_iteration_result_kind_, # T_String,

    # 36630: Table 58: Internal Slots of RegExp String Iterator Instances
    'IteratingRegExp'  : T_Object,
    'IteratedString'   : T_String,
    'Global'           : T_Boolean,
    'Unicode'          : T_Boolean,
    'Done'             : T_Boolean,

    # 36817: Properties of the ArrayBuffer Instances
    # 36973: Properties of the SharedArrayBuffer Instances
    # NO TABLE
    'ArrayBufferData': T_Data_Block | T_Shared_Data_Block | T_Null,
        # XXX but IsSharedArrayBuffer() ensures that ArrayBufferData is a Shared Data Block
    'ArrayBufferByteLength' : T_Integer_,
    'ArrayBufferDetachKey'  : T_Tangible_, # could be anything, really

    # 38581: Table 56: Internal Slots of Generator Instances
    'GeneratorState'  : T_Undefined | T_generator_state_, # T_String,
    'GeneratorContext': T_execution_context,

    # 25.1.1.1 WeakRef ( _target_ ) NO TABLE
    'WeakRefTarget' : T_Object,

    # 25.2.1.1 FinalizationRegistry ( cleanupCallback ) NO TABLE
    'CleanupCallback' : T_function_object_,
    'Cells'           : ListType(T_FinalizationRegistryCellRecord_),

    # 38914: 25.4.1.3.1 ish, NO TABLE
    'Promise'        : T_Object,
    'AlreadyResolved': T_boolean_value_record_,

    # 39021
    'MapData' : ListType(T_MapData_record_),

    # 39034: NO TABLE
    'Capability' : T_PromiseCapability_Record,

    # 39537: Table 59: Internal Slots of Promise Instances
    'PromiseState'           : T_promise_state_, # T_String,
    'PromiseResult'          : T_Tangible_,
    'PromiseFulfillReactions': ListType(T_PromiseReaction_Record) | T_Undefined,
    'PromiseRejectReactions' : ListType(T_PromiseReaction_Record) | T_Undefined,
    'PromiseIsHandled'       : T_Boolean,

    # 39763
    'SetData'    : ListType(T_Tangible_ | T_empty_),

    # 39781 AsyncFunction Awaited Fulfilled/Rejected NO TABLE
    'AsyncContext' : T_execution_context,

    # 39817 `Promise.all` Resolve Element Functions
    'Index'             : T_Integer_,
    'Values'            : ListType(T_Tangible_),
    'Capability'        : T_PromiseCapability_Record,
    'RemainingElements' : T_integer_value_record_,
    'AlreadyCalled'     : T_boolean_value_record_,

    # 40093:
    'WeakMapData' : ListType(T_MapData_record_),

    # 40188: NO TABLE
    'Done'              : T_Boolean,

    # 40254:
    'WeakSetData' : ListType(T_Tangible_ | T_empty_),

    # 40578: NO TABLE
    'Errors' : ListType(T_Tangible_),

    # 41310: Table N: Internal Slots of Async-from-Sync Iterator Instances
    'SyncIteratorRecord' : T_iterator_record_,

    # 41869: Table N: Internal Slots of AsyncGenerator Instances
    'AsyncGeneratorState'   : T_Undefined | T_generator_state_, # T_String,
    'AsyncGeneratorContext' : T_execution_context,
    'AsyncGeneratorQueue'   : ListType(T_AsyncGeneratorRequest_Record),

    # 42071 mention, NO TABLE
    'Generator' : T_AsyncGenerator_object_,

    # 44654 mention
    'Constructor' : T_constructor_object_,
    'OnFinally'   : T_function_object_,

    # 45286 mention
    'RevocableProxy' : T_Proxy_exotic_object_ | T_Null,
}

main()

# vim: sw=4 ts=4 expandtab
