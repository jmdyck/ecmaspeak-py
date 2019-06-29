
# ecmaspeak-py/Section.py:
# Identify "sections" in the spec, and ascertain their 'kind'.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, string

import shared
from shared import stderr, header, msg_at_posn, spec

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def make_and_check_sections():
    _establish_sections(spec.doc_node)
    _infer_section_kinds(spec.doc_node)
    _print_section_kinds(spec.doc_node)
    _check_section_order(spec.doc_node)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _establish_sections(doc_node):
    stderr("_establish_sections...")
    header("checking clause titles...")
    establish_section_r(doc_node, 0, None)

def establish_section_r(node, section_level, section_num):
    node.section_level = section_level
    node.section_num = section_num

    if node.element_name == '#DOC':
        node.section_id = None
        node.section_title = None
        node.section_kind = 'root'
        node.block_children = []
        node.numless_children = []
        node.section_children = [
            child
            for child in node.children
            if child.is_a_section()
        ]

        clause_counter = 0
        annex_counter = 0
        for child in node.section_children:
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
            establish_section_r(child, section_level+1, sn)

    elif node.is_a_section():
        assert not node.inline_child_element_names
        # if node.inline_child_element_names:
        #     msg_at_posn(
        #         node.inner_start_posn,
        #         "'section' node contains inline items"
        #     )

        node.section_id = node.attrs['id']

        assert node.children[0].is_whitespace()
        h1 = node.children[1]
        assert h1.element_name == 'h1'
        # node.section_header_element = h1
        check_section_title(h1, node)
        node.section_title = h1.inner_source_text()

        node.block_children = []
        node.numless_children = []
        node.section_children = []
        child_clause_counter = 0
        for child in node.children[2:]:
            if child.is_whitespace():
                pass
            elif child.element_name == '#COMMENT':
                pass
            elif child.is_a_section():
                node.section_children.append(child)
                child_clause_counter += 1
                sn = section_num + '.' + str(child_clause_counter)
                establish_section_r(child, section_level+1, sn)
            elif child.element_name == 'h2':
                numless = Numless( child.inner_source_text() )
                node.numless_children.append(numless)
            elif node.numless_children:
                node.numless_children[-1].block_children.append(child)
            else:
                node.block_children.append(child)

        assert len(node.block_children) > 0 or len(node.numless_children) > 0 or len(node.section_children) > 0

        # "bcen" = "block children element names"
        node.bcen_list = [
            c.element_name
            for c in node.block_children
        ]
        node.bcen_str = ' '.join(node.bcen_list)
        node.bcen_set = set(node.bcen_list)

    else:
        assert 0, node.element_name

class Numless:
    # A numberless part of a section. Starts with an h2.
    def __init__(self, title):
        self.title = title
        self.block_children = []

def check_section_title(h1, node):
    title = h1.inner_source_text()

    # Check capitalization.
    if node.parent.section_title != 'Terms and Definitions':
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

def _infer_section_kinds(section):
    # We infer a section's kind almost entirely based on its title.

    if section.element_name == '#DOC':
        stderr("_infer_section_kinds...")
        for child in section.section_children:
            _infer_section_kinds(child)
        return

    section.section_kind = select_via_pattern(
        section.section_title,
        [
            (r'Implicit Completion Values',                        'shorthand'),
            (r'Throw an Exception',                                'shorthand'),
            (r'ReturnIfAbrupt',                                    'shorthand'),
            (r'ReturnIfAbrupt Shorthands',                         'shorthand'),
            (r'Await',                                             'shorthand'),
            (r'NormalCompletion',                                  'shorthand'),
            (r'ThrowCompletion',                                   'shorthand'),
            (r'IfAbruptRejectPromise \( _value_, _capability_ \)', 'shorthand'),

            (r'\[\[\w+\]\] ?\([^()]*\)',        'internal_method'),
            (r'Static Semantics: Early Errors', 'early_errors'),

            (r'The Reference Specification Type', 'abstract_operations'), # plural!

            (r'.+ Instances',             'properties_of_instances'),
            (r'Module Namespace Objects', 'properties_of_instances'),

            (r'Properties of Valid Executions', 'catchall'),
            (r'(Additional )?Properties of .+', 'properties_of_an_intrinsic_object'),
            (r'The [\w%]+ Object',              'properties_of_an_intrinsic_object'),

            (r'The \w+ Constructor',               'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The _NativeError_ Constructors',    'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The _TypedArray_ Constructors',     'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The %TypedArray% Intrinsic Object', 'Call_and_Construct_ims_of_an_intrinsic_object'),

            (r'Changes to .+',                     'catchall'),

            (r'((Static|Runtime) Semantics: )?[A-Z][\w/]+ ?\([^()]*\)', 'abstract_operation'),
            (r'(Number|BigInt)::[a-z][a-zA-Z]+ \([^()]*\)',             'abstract_operation'),
            (r'.+ Comparison',                                          'abstract_operation'),

            (r'(Valid Chosen|Coherent|Tear Free) Reads',                'abstract_operation'),
            (r'(Races|Data Races)',                                     'abstract_operation'),

            (r'Static Semantics: TV and TRV',   'syntax_directed_operation'),
            (r'Static Semantics: \w+',          'syntax_directed_operation'),
            (r'Runtime Semantics: \w+',         'syntax_directed_operation'),
            (r'Statement Rules',                'syntax_directed_operation'),
            (r'Expression Rules',               'syntax_directed_operation'),

            (r'_NativeError_ Object Structure', 'loop'),

            (r'.+ Concrete Method',                'module_rec_method'),

            (r'Non-ECMAScript Functions',          'catchall'),
            (r'.+ Functions',      'anonymous_built_in_function'),
            (r'ListIterator next \( \)',           'anonymous_built_in_function'),
            (r'%ThrowTypeError% \( \)',            'anonymous_built_in_function'),
            # ArgGetter
            # ArgSetter

            (r'[gs]et Object.prototype.__proto__', 'accessor_property'), # B.2.2.1.*

            (r'.*',                                'catchall'),
        ]
    )

    # -----------

    if section.parent.section_title == 'Pattern Semantics' and section.section_title not in ['Notation', 'Runtime Semantics: CharacterRangeOrUnion ( _A_, _B_ )']:
        assert section.section_kind == 'catchall'
        section.section_kind = 'syntax_directed_operation'
    elif section.parent.section_title == '%TypedArray%.prototype.set ( _overloaded_ [ , _offset_ ] )':
        # (kludgey)
        assert section.section_kind == 'catchall'
        section.section_kind = 'function_property_overload'

    # ======================================================

    if section.section_kind == 'Call_and_Construct_ims_of_an_intrinsic_object':
        mo = re.fullmatch(r'The (\S+) (Constructors?|Intrinsic Object)', section.section_title)
        assert mo
        thing = mo.group(1)
        if thing == '_NativeError_': thing = 'NativeError' # Looks like a spec bug.

        constructor_alg_children = []
        other_children = []
        for child in section.section_children:
            if child.section_title.startswith(thing):
                assert child.section_title.startswith(thing + ' (')
                constructor_alg_children.append(child)
            else:
                other_children.append(child)

        if len(constructor_alg_children) == 0:
            assert 0
        elif len(constructor_alg_children) == 1:
            csk = 'CallConstruct'
        else:
            csk = 'CallConstruct_overload'
        for child in constructor_alg_children:
            child.section_kind = csk
            for gchild in child.section_children:
                _infer_section_kinds(gchild)

        for child in other_children:
            _infer_section_kinds(child)

    elif section.section_kind.startswith('properties_of_'):
        _set_section_kind_for_properties(section)

    elif section.section_title.endswith(' Environment Records'):
        for child in section.section_children:
            child.section_kind = 'env_rec_method'
            assert len(child.section_children) == 0

    # PR 1477 scope-records:
    elif section.section_title.endswith(' Scope Records'):
        for child in section.section_children:
            child.section_kind = 'env_rec_method' # XXX
            assert len(child.section_children) == 0

    else:
        for child in section.section_children:
            _infer_section_kinds(child)

def _set_section_kind_for_properties(section):
    # `section` contains clauses that declare (some of) the properties of some object.

    # This test is a little kludgey.
    # Properly, you'd look at the body of the section
    # to check whether it's just a cross-reference.
    if re.fullmatch(r'(Constructor|Other) Properties of the Global Object', section.section_title):
        suffix = '_xref'
    else:
        suffix = ''

    for child in section.section_children:
        child.section_kind = select_via_pattern( child.section_title,
            [
                (r'(Value|Function|Constructor|Other) Properties of .+', 'group_of_properties1'),
                (r'URI Handling Functions',                          'group_of_properties2'),
                (r'URI Syntax and Semantics',                        'catchall'),
                (r'get [\w.%]+( ?\[ ?@@\w+ ?\])?',                   'accessor_property'),
                (r'Object.prototype.__proto__',                      'accessor_property'),
                (    r'[\w.%]+( ?\[ ?@@\w+ ?\])? ?\([^()]*\)',       'function_property'),
                (    r'[\w.%]+( ?\[ ?@@\w+ ?\])?',                   'other_property'),
                (                  r'@@\w+',                         'other_property'), # 26.3.1
                (r'Abstract Operations for Atomics',                 'catchall'), # 24.4.1
                (r'Async-from-Sync Iterator Value Unwrap Functions', 'anonymous_built_in_function'), # 25.1.4.2.5
            ]
        ) + suffix

        if child.section_kind.startswith('group_of_properties'):
            _set_section_kind_for_properties(child)
        else:
            for gchild in child.section_children:
                _infer_section_kinds(gchild)

# ----------------------------------------------------------

def select_via_pattern(subject, pattern_results):
    # Return the `result` for the first pattern in `pattern_results`
    # that matches (via re.search) `subject`.
    for (pattern, result) in pattern_results:
        if re.fullmatch(pattern, subject):
            return result
    assert 0, subject
    # If you get here, look at stack trace to see caller

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _print_section_kinds(section):
    global g_sections_f
    if section.element_name == '#DOC':
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

def _check_section_order(section):
    # In some sections, the subsections should be in "alphabetical order".

    if section.element_name == '#DOC':
        stderr("_check_section_order...")
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
