
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

def _set_section_kind_r(section):
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

def _handle_early_errors_section(section):
    if section.section_title != 'Static Semantics: Early Errors':
        return False

    section.section_kind = 'early_errors'
    section.ste = {'op_name': 'Early Errors', 'parameters': OrderedDict()}
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
        return True

    if section.section_id in [
        'sec-object-environment-records-createimmutablebinding-n-s',
        'sec-module-environment-records-deletebinding-n',
    ]:
        # These are odd cases.
        # The clause exists only to tell us that the concrete method is never used.
        assert 'is never used' in section.block_children[0].inner_source_text()
        # There's roughly two approaches:
        # - Create the thing, but make the body of it be (effectively) "Assert: False."
        # - Don't create the thing. (So if there *is* an attempt to use it, the lookup will fail.)
        # Let's try the latter.
        # I.e., don't create anything, but return True to indicate that we've handled this section.
        section.section_kind = 'env_rec_method_unused'
        section.ste = {}
        return True

    if section.section_id in ['sec-normalcompletion', 'sec-throwcompletion']:
        # The preambles say "The abstract operation NormalCompletion ..."
        # and "The abstract operation ThrowCompletion ..."
        # but currently, they're not defined as abstract operations,
        # they're defined as shorthands.
        return False

    if section.section_id == 'sec-weakref-execution':
        # 9.10.3
        section.section_kind = 'abstract_operation'
        section.ste = {
            'op_name': 'WeakRef emptying thing',
            'type': 'abstract operation',
            'parameters': {'_S_': ''},
        }
        return True

    if section.section_title in [
        'Valid Chosen Reads',
        'Coherent Reads',
        'Tear Free Reads',
    ]:
        # 29.7.*
        section.section_kind = 'abstract_operation'
        assert section.block_children[0].source_text().startswith(
            "<p>A candidate execution _execution_ has "
        )
        section.ste = {
            'op_name': section.section_title,
            'parameters': {'_execution_': ''},
        }
        return True

    if section.section_title in [
        'Races',
        'Data Races',
    ]:
        # 29.8, 29.9
        section.section_kind = 'abstract_operation'
        assert section.block_children[0].source_text().startswith(
            "<p>For an execution _execution_, two events _E_ and _D_ in SharedDataBlockEventSet(_execution_) are in a "
        )
        parameters = {
            '_execution_': '',
            '_E_'        : '',
            '_D_'        : '',
        }
        section.ste = {
            'op_name': section.section_title,
            'parameters': parameters,
        }
        return True

    handled = _handle_header_with_std_preamble(section)
    if not handled:
        return False

    return True

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

    section.ste = {
        'op_name'   : p_dict['op_name'],
        'kind'      : p_dict['kind'],
        'parameters': convert_param_listing_to_dict(p_dict['params_str'])
    }

    # --------------------------------------------------------------------------

    if 1:
        # Complain about the old header, suggest a structured one.

        param_names = [] #XXX

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

        if param_names == []:
            lines.append(f"{ind}  <h1>{name_for_heading} ( )</h1>")
        else:
            lines.append(f"{ind}  <h1>")
            lines.append(f"{ind}    {name_for_heading} (")
            for param_name in param_names:
                optionality = 'optional ' if param_name in optional_params else ''
                param_nature = param_nature_.get(param_name, 'TBD')
                if param_nature == 'TBD': param_nature = 'unknown'
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

def _handle_other_section(section):

    check_section_title(section)

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

            (r'(?P<prop_path>[A-Z]\w+) \( \. \. \. \)', 'function_property_xref'),

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
    p_dict = mo.groupdict()
    section.ste = {
        'prop_path': p_dict.get('prop_path', None),
        'parameters': (
            convert_param_listing_to_dict(p_dict['params_str'])
            if 'params_str' in p_dict
            else None
        ),
    }

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

    if section.section_title.startswith('get '):
        assert section.section_kind == 'accessor_property'
        # The spec leaves off the empty parameter list
        assert 'params_str' not in section.ste
        section.ste['params_str'] = ''
        section.ste['parameters'] = OrderedDict()

    return True

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
