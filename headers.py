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
import Pseudocode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def generate_spec_for_PR_545():
    stderr("generate_spec_for_PR_545 ...")

    write_header_info()

# ------------------------------------------------------------------------------

def oh_warn(*args):
    print(*args, file=oh_inc_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_header_against_prose(hoi, preamble_nodes):
    if preamble_nodes == []:
        # No prose to check
        pass
    else:
        info_holder = extract_info_from_preamble(preamble_nodes)
        poi = info_holder.convert_to_header()
        resolve_oi(hoi, poi)

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

        (An? (?P<name>.+) function) is an (?P<kind>anonymous built-in function) that ((has|is) .+)
        v=!FUNC \4

    # ==========================================================================

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

        (Returns (?P<retn>a new _TypedArray_) .+)
        v=\1

        (Returns (?P<retn>an Array) into .+)
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

        (.+ returns (an Array) containing .+, (or \*null\*) if _string_ did not match.)
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

def extract_info_from_preamble(preamble_nodes):

    info_holder = PreambleInfoHolder()

    para_texts_remaining = []
    for preamble_node in preamble_nodes:
        assert preamble_node.element_name in ['p', 'emu-note', 'pre']
        if preamble_node.element_name != 'p': continue

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
        poi.species = {
            'anonymous built-in function object'        : 'bif: * per realm',
            'anonymous built-in function'               : 'bif: * per realm',
            'accessor property'                         : 'bif: accessor function',
            'constructor'                               : 'bif: value of data property',
            'function'                                  : 'bif: value of data property',
            'method'                                    : 'bif: value of data property',
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
    # Rather than creating a new AlgHeader,
    # modifies {hoi} if appropriate.

    if poi is None:
        # no preamble, so just use info from heading
        return

    # kind
    assert hoi.species is not None
    if poi.species is None:
        pass
    else:
        if hoi.species == poi.species:
            pass
        else:
            stderr(f"mismatch of 'species' in heading/preamble for {hoi.name}: {hoi.species!r} != {poi.species!r}")
            assert 0

    # name
    assert hoi.name is not None
    if True:
        # We prefer to use the heading-name,
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
    elif hoi.for_phrase:
        pass
    else:
        hoi.for_phrase = poi.for_phrase # which might or might not be None

    # param_names
    if hoi.param_names is None:
        # assert poi.param_names is not None
        hoi.param_names = poi.param_names
        hoi.optional_params = poi.optional_params
        hoi.rest_params = poi.rest_params
    elif poi.param_names is None:
        assert hoi.param_names is not None
    else:
        # neither is None

        # When the heading contains a signature,
        # it's deemed authoritative.

        if hoi.param_names != poi.param_names and hoi.name not in [
            'OrdinaryCreateFromConstructor',
            'TriggerPromiseReactions',
        ]:
            oh_warn()
            oh_warn(hoi.name, 'has param name mismatch:')
            oh_warn(hoi.param_names)
            oh_warn(poi.param_names)
        else:
            if hoi.optional_params != poi.optional_params:
                oh_warn()
                oh_warn(hoi.name, 'has param optionality mismatch:')
                oh_warn('h:', sorted(list(hoi.optional_params)))
                oh_warn('p:', sorted(list(poi.optional_params)))

        assert (
            not poi.rest_params
            or
            poi.rest_params == hoi.rest_params
        )

    assert hoi.param_nature_ == {} # heading never has type info
    hoi.param_nature_ = poi.param_nature_

    assert hoi.also is None
    hoi.also = poi.also

    assert hoi.return_nature_normal is None
    hoi.return_nature_normal = poi.return_nature_normal

    assert hoi.return_nature_abrupt is None
    hoi.return_nature_abrupt = poi.return_nature_abrupt

    assert hoi.description_paras == []
    hoi.description_paras = poi.description_paras

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
        self.species = None
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
                species: {self.species}
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

        if self.species == 'op: numeric method':
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

        if self.species.startswith('bif:'):
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

        self.parent_alg = Pseudocode.ensure_alg(self.species, self.name)
        self.parent_alg.headers.append(self)

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
                assert alg_header.species == alg_info.species
                put(f"      --")
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
