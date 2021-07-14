
# ecmaspeak-py/Section.py:
# Identify "sections" in the spec, and ascertain their 'kind'.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, string
from collections import OrderedDict

import shared
from shared import stderr, header, msg_at_posn, spec

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def make_and_check_sections():
    stderr("make_and_check_sections ...")

    spec.root_section = _make_section_tree(spec.doc_node)
    _set_section_identification_r(spec.root_section, None)
    _set_section_kind_r(spec.root_section)
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

    # "bcen" = "block children element names"
    section.bcen_list = [
        c.element_name
        for c in section.block_children
    ]
    section.bcen_str = ' '.join(section.bcen_list)
    section.bcen_set = set(section.bcen_list)

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

def _set_section_kind_r(section):
    # Set section attributes:
    # .section_kind
    # .section_title
    # .ste

    r = (
        _handle_root_section(section)
        or
        _handle_sdo_section(section)
        or
        _handle_other_op_section(section)
        or
        _handle_other_section(section)
    )
    assert r

    for child in section.section_children:
        _set_section_kind_r(child)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_root_section(section):
    if section.is_root_section:
        return True

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

        # A clause that defines *multiple* SDOs:
        if section.section_title in [
            'Static Semantics: TV and TRV',
        ]:
            sdo_name = 'TV and TRV'

        # A clause that only *partially* defines an SDO:
        elif section.section_title in [
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
        section.ste['parameters'] = parameters

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_other_op_section(section):

    if section.section_id in ['sec-normalcompletion', 'sec-throwcompletion']:
        # The preambles say "The abstract operation NormalCompletion ..."
        # and "The abstract operation ThrowCompletion ..."
        # but currently, they're not defined as abstract operations,
        # they're defined as shorthands.
        return False

    if section.section_title == 'StringToBigInt ( _argument_ )':
        # 7.1.14
        # First <p> isn't a proper preamble, so has to be handled specially.
        p_dict = {
            'kind': 'abstract operation',
            'op_name': 'StringToBigInt',
            'params_str': '_argument_',
        }

    elif section.section_id == 'sec-weakref-execution':
        # 9.10.3
        p_dict = {
            'kind': 'abstract operation',
            'op_name': 'WeakRef emptying thing',
            'params_str': '_S_',
        }

    elif section.section_title in [
        'Valid Chosen Reads',
        'Coherent Reads',
        'Tear Free Reads',
        'Races',
        'Data Races',
    ]:
        # 29.7.*, 29.8, 29.9
        p_dict = {
            'kind': 'abstract operation',
            'op_name': section.section_title,
        }

    else:
        # Over the course of various PRs (latest #2427),
        # the first para ('preamble') of non-SDO operations
        # has become standardized.
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

    _start_ste(section, p_dict)

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _handle_other_section(section):

    check_section_title(section.heading_child, section)

    # We infer a section's kind almost entirely based on its title.
    pattern_results = [
            (r'Implicit Completion Values',                        'shorthand'),
            (r'Throw an Exception',                                'shorthand'),
            (r'ReturnIfAbrupt',                                    'shorthand'),
            (r'ReturnIfAbrupt Shorthands',                         'shorthand'),
            (r'Await',                                             'shorthand'),
            (r'NormalCompletion',                                  'shorthand'),
            (r'ThrowCompletion',                                   'shorthand'),
            (r'IfAbruptRejectPromise \( _value_, _capability_ \)', 'shorthand'),

            (r'Static Semantics: (?P<op_name>Early Errors)', 'early_errors'),

            (r'.+ Instances',             'properties_of_instances'),
            (r'Module Namespace Objects', 'properties_of_instances'),

            (r'Properties of Valid Executions', 'catchall'),
            (r'(Additional )?Properties of .+', 'properties_of_an_intrinsic_object'),
            (r'The [\w%.]+ Object',             'properties_of_an_intrinsic_object'),

            (r'The \w+ Constructor',               'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The _NativeError_ Constructors',    'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The _TypedArray_ Constructors',     'Call_and_Construct_ims_of_an_intrinsic_object'),
            (r'The %TypedArray% Intrinsic Object', 'Call_and_Construct_ims_of_an_intrinsic_object'),

            (r'Changes to .+',                                   'changes'),
            (r'__proto__ Property Names in Object Initializers', 'changes'),
            (r'VariableStatements in Catch Blocks',              'changes'),
            (r'Initializers in ForIn Statement Heads',           'changes'),

            (r'_NativeError_ Object Structure', 'loop'),

            (r'Non-ECMAScript Functions',                          'catchall'),
            (r'URI Handling Functions',                            'group_of_properties2'),
            (r'(?P<prop_path>.+) Functions',                       'anonymous_built_in_function'),
            (r'(?P<prop_path>%ThrowTypeError%) <PARAMETER_LIST>',  'anonymous_built_in_function'),
            (r'(Value|Function|Constructor|Other) Properties of .+', 'group_of_properties1'),

            (r'(?P<prop_path>[A-Z]\w+) \((?P<params_str> \. \. \. )\)', 'function_property_xref'),

            (r'(?P<prop_path>[A-Z]\w+) <PARAMETER_LIST>',   'CallConstruct'),
            (r'(?P<prop_path>_[A-Z]\w+_) <PARAMETER_LIST>', 'CallConstruct'),
            (r'(?P<prop_path>%[A-Z]\w+%) <PARAMETER_LIST>', 'CallConstruct'),

            (r'(?P<prop_path>get <PROP_PATH>)',              'accessor_property'),
            (r'(?P<prop_path>set <PROP_PATH>)',              'accessor_property'),
            (r'(?P<prop_path>Object.prototype.__proto__)',   'accessor_property'),

            (r'(?P<prop_path><PROP_PATH>) <PARAMETER_LIST>', 'function_property'),
            (r'(?P<prop_path>\w+) <PARAMETER_LIST>',         'function_property'),

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
            .replace('<PARAMETER_LIST>', r'\((?P<params_str>[^()]*)\)')
            .replace('<PROP_PATH>',      r'(\w+|%\w+%)(\.\w+| \[ @@\w+ \])+')
        )
        mo = re.fullmatch(pattern, section.section_title)
        if mo:
            break
    else:
        assert 0, section.section_title

    assert isinstance(result, str)
    section.section_kind = result
    _start_ste(section, mo.groupdict())

    if section.section_title == 'Pattern Semantics':
        if section.section_num.startswith('B.'):
            section.section_kind = 'changes'

    if section.parent.section_title == 'Terms and Definitions' and section.section_kind == 'other_property':
        section.section_kind = 'catchall'

    if section.parent.section_title == 'Other Properties of the Global Object':
        assert section.section_kind == 'catchall'
        section.section_kind = 'other_property_xref'

    # -----------

    # Some stuff that isn't in the section_title, but should be?

    if section.section_kind == 'early_errors':
        assert section.ste['op_name'] == 'Early Errors'
        assert 'parameters' not in section.ste
        section.ste['parameters'] = OrderedDict()

    if section.section_title.startswith('get '):
        assert section.section_kind == 'accessor_property'
        # The spec leaves off the empty parameter list
        assert 'params_str' not in section.ste
        section.ste['params_str'] = ''
        section.ste['parameters'] = OrderedDict()

    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _start_ste(section, initial_ste):
    # "ste" = section-title extractions
    section.ste = initial_ste

    # ---------------------------------

    if 'params_str' in section.ste:
        parameter_listing = section.ste['params_str'].strip()

        if parameter_listing == '. . .':
            assert section.section_kind == 'function_property_xref'
            # Doesn't mean anything, might as wel not be there.
            del section.ste['params_str']

        else:

            params_info = OrderedDict()
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

            section.ste['parameters'] = params_info

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

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

            elif section.section_kind == 'abstract_operation':
                if (
                    section.parent.section_title == 'Properties of Valid Executions'
                    or
                    section.parent.section_title == 'Memory Model'
                ):
                    # This isn't an abstract operation in the usual sense.
                    # (The Memory Model clauses are weird.)
                    expected_aoid = None
                else:
                    expected_aoid = op_name

            elif section.section_kind == 'syntax_directed_operation':
                if op_name in [
                    'MV',
                    'TV and TRV',
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
