#!/usr/bin/python3

# ecmaspeak-py/headers.py:
# This module is primarily concerned with making the version of the spec for PR 545,
# and will probably mostly disappear if/when that PR is merged.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re, pdb
from collections import OrderedDict, defaultdict
from dataclasses import dataclass

import shared
from shared import spec, stderr, DL
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

        This (?P<kind>method) returns (?P<retn>a String value). The contents of the String (are .+)
        v=The contents of the returned String \3

        (`([][@\w.]+)` is an accessor property whose set accessor function is \*undefined\*.) Its get accessor function performs the following steps when called:
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
    # Sentences that start with "It"

        It can take three parameters.

        It performs the following steps when called:

        Its get accessor function performs the following steps when called:

    # ==========================================================================
    # Sentences that start with "The"

        # Don't match "The value of _separator_ may be a String of any length or it may be ..."
        # because it belongs in the description, is misleading for parameter-type.

        (The value of the \[\[\w+\]\] attribute is a built-in function) that (requires|takes) (?P<pl>no arguments|an argument _proto_).
        kind=accessor property

    # ==========================================================================
    # Sentences that start with "This"

        # Note that none of these leave anything for the description.

        This method (.+)
        v=!FUNC \1

    # ==========================================================================
    # Sentences that start with "When"

        # (Ultimately, almost nothing falls through to the description.)

        # -----------------------------------------------------

        # When a|an ...

        When an? (?P<name>.+) function is called with (?P<pl>.+?), the following steps are taken:

    # ==========================================================================
    # Miscellaneous starts:

        Given (?P<pl>zero or more arguments), this function (calls ToNumber .+)
        v=!FUNC \2

    # ==========================================================================
    # Sentences where we don't care how it starts:

        # ----------
        # produces ...

        (.+ produces (?P<retn>a String value) .+)
        v=\1

        (.+ produces (?P<retn>a Number value) .+)
        v=\1

        (.+ produces (?P<retn>an ECMAScript language value).)
        v=\1

        # ----------
        # provides ...

        (.+ provides (?P<retn>a String) representation of .+)
        v=\1

        # ----------
        # returns ...

        (.+ returns (?P<retn>an array) containing .+)
        v=\1

        (.+ returns (?P<retn>a Number) .+)
        v=\1

        (.+ returns the Number .+)
        retn=a Number
        v=\1

        (.+ returns (?P<retn>a new _TypedArray_) .+)
        v=\1

        (.+ returns (?P<retn>an Array) into .+)
        v=\1

        (.+ returns the .+ integral Number value .+)
        retn=an integral Number
        v=\1

        (.+ returns the integral part of the number .+)
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
            'anonymous built-in function'               : 'bif: * per realm',
            'accessor property'                         : 'bif: intrinsic: accessor function',
            'method'                                    : 'bif: intrinsic',
            None                                        : None,
        }[vs]

        poi.name = at_most_one_value('name')

        pl_values = self.fields['pl']
        if len(pl_values) == 0:
            poi.params = None
        elif len(pl_values) == 1:
            get_info_from_parameter_listing_in_preamble(poi, pl_values[0])
        else:
            stderr(f"{poi.name} has multi-pl: {pl_values}")
            assert 0

        poi.return_nature_normal = join_field_values('retn', ' or ')

        poi.return_nature_abrupt = at_most_one_value('reta')

        poi.description_paras = self.fields['desc']

        return poi

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def get_info_from_parameter_listing_in_preamble(oi, parameter_listing):
    # This is only called about 10 times now.

    assert oi.params is None, oi.name

    if parameter_listing == 'no arguments':
        # 27 cases
        oi.params = []
        return

    if parameter_listing in [
        'zero or more arguments',
    ]:
        # 2 cases
        # XXX not sure what to do
        return

    mo = re.fullmatch(r'(an )?argument (_\w+_)', parameter_listing)
    assert mo, parameter_listing
    param_name = mo.group(2)
    punct = ''
    nature = 'unknown'
    oi.params = [ AlgParam(param_name, punct, nature) ]
    return

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
    assert poi.for_phrase is None
    # so just leave hoi.for_phrase as is

    # param_names
    if hoi.params is None:
        # assert poi.params is not None
        hoi.params = poi.params
    elif poi.params is None:
        assert hoi.params is not None
    else:
        # neither is None

        # When the heading contains a signature,
        # it's deemed authoritative.

        if hoi.param_names() != poi.param_names():
            oh_warn()
            oh_warn(hoi.name, 'has param name mismatch:')
            oh_warn(hoi.param_names())
            oh_warn(poi.param_names())
        else:

            for (hoi_param, poi_param) in zip(hoi.params, poi.params):
                assert hoi_param.name == poi_param.name

                if hoi_param.punct != poi_param.punct:
                    oh_warn()
                    oh_warn(f"{hoi.name} parameter {hoi_param.name} has param punct mismatch:")
                    oh_warn('h:', hoi_param.punct)
                    oh_warn('p:', poi_param.punct)

                if hoi_param.nature == 'unknown':
                    hoi_param.nature = poi_param.nature
                else:
                    assert hoi_param.nature == poi_param.nature

    assert hoi.return_nature_node is None
    hoi.return_nature_node = poi.return_nature_node

    assert hoi.description_paras == []
    hoi.description_paras = poi.description_paras

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

@dataclass
class AlgParam:
    name: str
    punct: str # '' | '[]' | '...'
    nature: str
    decl_node: Pseudocode.ANode = None

# ------------------------------------------------

class AlgHeader:
    def __init__(self):
        self.species = None
        self.name = None
        self.for_phrase = None
        self.for_phrase_node = None
        self.params = None
        self.return_nature_node = None
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
                    param.name + ' : ' + param.nature
                    for param in self.params
                    )
                }
                returns: {self.return_nature_node.source_text()}
                # defns: {len(self.u_defns)}
        """

    def __repr__(self):
        return f"AlgHeader(name: {self.name!r})"

    # --------------------------------------------------------------------------

    def param_names(self):
        return [
            param.name
            for param in self.params
        ]

    # --------------------------------------------------------------------------

    def finish_initialization(self):

        self.name_w_markup = self.name
        if self.name.startswith('<'):
            mo = re.fullmatch(r'<dfn [^<>]+>([^<>]+)</dfn>', self.name)
            assert mo
            self.name = mo.group(1)

        # ------------------------------------------------------------

        assert self.params is not None

        assert len([
                param.name
                for param in self.params
                if param.punct == '...'
            ]) in [0,1]

        if self.species.startswith('bif:'):
            for param in self.params:
                if param.nature == 'unknown':
                    if param.punct == '...':
                        param.nature = 'a List of ECMAScript language values'
                    else:
                        param.nature = 'an ECMAScript language value'

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
                # alg_header.params
                # alg_header.return_nature_{normal,abrupt}
                # alg_header.description_paras
                put(f"        {len(alg_header.u_defns)} defns")
                n_defns_via_headers += len(alg_header.u_defns)
                for alg_defn in alg_header.u_defns:
                    assert alg_defn.header is alg_header

            assert n_defns_via_headers == len(alg_info.all_definitions())
            # alg_info.invocations
            # alg_info.callees
            # alg_info.callers
        put()

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
