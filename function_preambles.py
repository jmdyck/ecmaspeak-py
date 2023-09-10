#!/usr/bin/python3

# ecmaspeak-py/function_preambles.py:
# This module is primarily concerned with extracting information from
# the preambles of built-in functions.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re, pdb
from collections import defaultdict

from shared import stderr
from algos import AlgParam, AlgHeader

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def oh_warn(*args):
    print(*args, file=oh_inc_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_header_against_prose(hoi, preamble_nodes):
    assert hoi.species.startswith('bif:')
    assert preamble_nodes
    info_holder = extract_info_from_preamble(preamble_nodes)
    info_holder.compare_to_header(hoi)

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

    def compare_to_header(self, hoi):
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

        # -----
        # kind:

        assert hoi.species is not None

        vs = join_field_values('kind')
        poi.species = {
            'anonymous built-in function'               : 'bif: * per realm',
            'accessor property'                         : 'bif: intrinsic: accessor function',
            'method'                                    : 'bif: intrinsic',
            None                                        : None,
        }[vs]

        if poi.species is None:
            pass
        elif poi.species == hoi.species:
            pass
        else:
            stderr(f"mismatch of 'species' in heading/preamble for {hoi.name}: {hoi.species!r} != {poi.species!r}")
            assert 0

        # -----
        # name:

        assert hoi.name is not None

        poi.name = at_most_one_value('name')

        if (
            poi.name is None
            or
            poi.name == hoi.name
            or
            # heading has spaces around square brackets, but preamble doesn't:
            poi.name == hoi.name.replace(' [ ', '[').replace(' ]', ']')
            or
            # E.g. "Promise Resolve Functions" in heading vs "promise resolve function" in preamble:
            poi.name.lower() == hoi.name.lower()
        ):
            pass
        else:
            oh_warn()
            oh_warn(f'resolve_oi: name in heading ({hoi.name}) != name in preamble ({poi.name})')

        # ---
        # pl:

        pl_values = self.fields['pl']
        if len(pl_values) == 0:
            poi.params = None

        elif len(pl_values) == 1:
            [parameter_listing] = pl_values
            # This only happens about 10 times now.

            if parameter_listing == 'no arguments':
                # 1 case
                poi.params = []

            elif parameter_listing == 'zero or more arguments':
                # 2 cases
                # XXX not sure what to do
                poi.params = None

            else:
                # 7 cases
                mo = re.fullmatch(r'(an )?argument (_\w+_)', parameter_listing)
                assert mo, parameter_listing
                param_name = mo.group(2)
                punct = ''
                nature = 'unknown'
                poi.params = [ AlgParam(param_name, punct, nature) ]

        else:
            stderr(f"{poi.name} has multi-pl: {pl_values}")
            assert 0

        if hoi.params is None:
            assert poi.params is not None
            hoi.params = poi.params
        elif poi.params is None:
            pass
        else:
            # neither is None

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

                    if hoi_param.nature != poi_param.nature:
                        oh_warn()
                        oh_warn(f"{hoi.name} parameter {hoi_param.name} has param nature mismatch:")
                        oh_warn('h:', hoi_param.nature)
                        oh_warn('p:', poi_param.nature)

        # -----------
        # retn + reta:

        poi.return_nature_normal = join_field_values('retn', ' or ')
        poi.return_nature_abrupt = at_most_one_value('reta')
        # TODO: compare to hoi.return_nature_node ?

        # -----
        # desc:

        poi.description_paras = self.fields['desc']
        assert hoi.description_paras == []
        hoi.description_paras = poi.description_paras

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
