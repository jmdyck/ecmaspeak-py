#!/usr/bin/python3

# ecmaspeak-py/intrinsics.py:
# Code that deals with intrinsic objects.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re
from collections import defaultdict
from dataclasses import dataclass
import typing

import shared
from shared import stderr, spec

# ------------------------------------------------------------------------------

def get_pdn(phrase):
    # {phrase} is a string that identifies an intrinsic/global object.
    # Return the PDN (percent-delimited name) for that object.
    #
    # (Generally, this function doesn't know or care whether the object
    # actually exists. It just applies naming conventions.)

    def pc(s): return f"%{s}%"

    if re.fullmatch(r'%[^%]+%', phrase):
        # {phrase} is already a PDN
        return phrase

    # --------------
    # fixed phrases:

    if phrase in ['the global object', 'global object']:
        return '%(global)%'
        # It's questionable to treat the global object like an intrinsic

    result = {
        'the constructor of async function objects': '%AsyncFunction%',
        'the constructor of async iterator objects': '%AsyncGeneratorFunction%',
        'the constructor of Generators':             '%GeneratorFunction%',
        'the super class of all typed Array constructors': '%TypedArray%',
    }.get(phrase)
    if result: return result

    # -----------------------------------------
    # multi-word phrases with 'variable' parts:

    if mo := re.fullmatch(r'the prototype of (.+) [Ii]terator objects', phrase):
        what = mo.group(1)
        return pc(
            ''.join(
                (word[0].upper() + word[1:])
                for word in re.split('[- ]', what)
            ) + 'IteratorPrototype'
        )

    if mo := re.fullmatch(r'(the )?%(\w+)% prototype object', phrase):
        return pc(mo.expand(r'\2.prototype'))

    if mo := re.fullmatch(r'(the )?(\w+) prototype( object)?', phrase):
        path = mo.expand(r'\2.prototype')
        return pc(normalize_property_path(path))
        # normalize_property_path for the "Generator.prototype" check

    if mo := re.fullmatch(r'the (\w+) (constructor|object)', phrase):
        return pc(mo.group(1))

    if mo := re.fullmatch(r'the %(\w+)% (object|intrinsic object)', phrase):
        return pc(mo.group(1))

    if mo := re.fullmatch(r'the (\w+) function', phrase):
        return pc(mo.group(1))

    if mo := re.fullmatch(r'(get|set) (.+)', phrase):
        (get_or_set, path) = mo.groups()
        return pc(normalize_property_path(path) + ':' + get_or_set) # or something

    # -----------------------------------------------
    # Anything left should be just a 'property path'.
    # (If it isn't, normalize_property_path will raise an AssertionError.)

    inner = normalize_property_path(phrase)
    return pc(inner)

# ------------------------------------------------------------------------------

def normalize_property_path(path):
    # --------------
    # special cases:

    if path == 'Generator.prototype':
        return 'GeneratorFunction.prototype.prototype'
    if path == 'AsyncGenerator.prototype':
        return 'AsyncGeneratorFunction.prototype.prototype'

    # --------------------------------
    # base cases (leftmost component):

    if re.fullmatch(r'\w+', path):
        return path

    if mo := re.fullmatch(r'%(\w+)%', path):
        return mo.group(1)

    # ----------------
    # recursive cases:
    # (split off rightmost component of path)

    # property key is a String
    if mo := re.fullmatch(r'(.+)(\.\w+)', path):
        (head, tail) = mo.groups()
        return normalize_property_path(head) + tail

    # property key is a Symbol
    if mo := re.fullmatch(r'(.+) \[ (@@\w+) \]', path):
        (head, tail) = mo.groups()
        return normalize_property_path(head) + f"[{tail}]" # presumably

    # ----------------------------
    # That should cover everything

    assert 0, path

# ------------------------------------------------------------------------------

well_known_intrinsics = {}
global_property_names = set()

# ------------------------------------------------------------------------------

def each_row_in_wki_table(emu_table):
    assert emu_table._caption in [
        'Well-Known Intrinsic Objects',
        'Additional Well-known Intrinsic Objects',
    ]

    assert emu_table._header_row.cell_texts == ['Intrinsic Name', 'Global Name', 'ECMAScript Language Association']

    for row in emu_table._data_rows:
        [percent_name, global_name, assoc] = row.cell_texts

        assert re.fullmatch(r'%\w+%', percent_name)
        assert percent_name not in well_known_intrinsics
        well_known_intrinsics[percent_name] = True

        if global_name == '':
            pass
        else:
            assert re.fullmatch(r"`\w+`", global_name)
            assert global_name[1:-1] == percent_name[1:-1]
            assert global_name not in global_property_names
            global_property_names.add(global_name[1:-1])

        if re.match(r'(A function|An) object that ', assoc):
            phrase = ''
        elif (mo := re.fullmatch(r'The (.+) \(<emu-xref href="[^"]+"></emu-xref>\)', assoc)):
            phrase = 'the ' + mo.group(1)
        else:
            assert 0, assoc

        # --------------------------------------------------

        yield (percent_name, global_name, phrase)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

@dataclass(frozen = True)
class S_InternalSlot:
    name : str
    value: str

    def __str__(self):
        return f"{self.name} with value ({self.value})"


@dataclass # not frozen because may need to change attrs during merging
class S_Property:
    key     : str
    attrs   : dict

    def __init__(self, key, attrs):
        assert isinstance(attrs, dict)
        attr_name_set = set(attrs.keys())
        assert (
            attr_name_set <= set([
                '[[Value]]',
                '[[Writable]]',
                '[[Enumerable]]',
                '[[Configurable]]',
            ])
            or
            attr_name_set <= set([
                '[[Get]]',
                '[[Set]]',
                '[[Enumerable]]',
                '[[Configurable]]',
            ])
        ), attr_name_set

        self.key = key
        self.attrs = attrs

    def kind(self):
        is_data = ('[[Value]]' in self.attrs or '[[Writable]]' in self.attrs)
        is_accessor = ('[[Get]]' in self.attrs or '[[Set]]' in self.attrs)
        assert not (is_data and is_accessor)
        if is_data:
            kind = 'data'
        elif is_accessor:
            kind = 'accessor'
        else:
            kind = 'unknown'
        return kind

    def __str__(self):
        return f"a property with key {self.key} and attributes {self.attrs}"

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def process_intrinsics_facts():
    coalesce_intrinsic_facts()
    print_intrinsic_info()

def coalesce_intrinsic_facts():
    # Go through all the facts,
    # and accumulate facts about each intrinsic object.

    for section in spec.root_section.each_descendant_that_is_a_section():
        for (L, verb, R) in section.intrinsic_facts_cooked:

            L_intrinsic = ensure_intrinsic_named(L)

            if verb == "exists":
                pass

            elif verb == "is":
                kind = R
                if L_intrinsic.kind is None:
                    L_intrinsic.kind = kind
                elif L_intrinsic.kind == kind:
                    # same
                    pass
                elif (
                    L_intrinsic.kind == 'a constructor' and kind == 'a function object'
                    or
                    L_intrinsic.kind == 'a function object' and kind == 'a constructor'
                ):
                    # They're consistent
                    L_intrinsic.kind = 'a constructor'
                else:
                    # inconsistent? 
                    assert L_intrinsic.kind == kind, \
                        f"? {L_intrinsic.name} kind: {L_intrinsic.kind!r} != {kind!r}"

            elif verb == "has-slot":
                slot = R
                if slot.name not in L_intrinsic.slots:
                    L_intrinsic.slots[slot.name] = slot.value
                else:
                    curr_value = L_intrinsic.slots[slot.name]
                    if curr_value == slot.value:
                        pass
                    elif (
                        slot.name == '[[ccb]]'
                        and
                        curr_value.replace('prose in', 'emu-alg in') == slot.value
                    ):
                        L_intrinsic.slots[slot.name] = slot.value
                    else:
                        assert curr_value == slot.value, \
                            f"? {L_intrinsic.name} {slot.name}: {curr_value!r} != {slot.value!r}"

            elif verb == 'has-prop':
                L_intrinsic.ensure_property(R)
                # more TODO

            else:
                assert 0, verb

            if 0:
                if phrase.startswith('*') or phrase == 'the empty String':
                    # It expresses a String/Number/Boolean/Null value
                    continue
                elif phrase in ['a function', 'host-defined']:
                    # hm
                    continue
                ensure_intrinsic_named(phrase)

# ------------------------------------------------------------------------------

def print_intrinsic_info():

    f = shared.open_for_output('intrinsics')
    for intrinsic in sorted(all_intrinsics, key=lambda intr: intr.name):
        intrinsic.dump(f)
    f.close()

    f = shared.open_for_output('intrinsics_anomalies')
    def put(*args): print(*args, file=f)

    for intrinsic in sorted(all_intrinsics, key=lambda intr: intr.name):
        if intrinsic.kind not in [
            'a function object',
            'a constructor',
            'an ordinary object',
            'a String exotic object',
            'an Array exotic object',
            'an immutable prototype exotic object',
        ]:
            put(f"{intrinsic.name} kind = {intrinsic.kind}")

        if intrinsic.kind in ['a function object', 'a constructor']:
            if '[[ccb]]' not in intrinsic.slots:
                put(f"{intrinsic.name} is {intrinsic.kind}, but does not have a [[ccb]] slot")
        else:
            if '[[ccb]]' in intrinsic.slots:
                put(f"{intrinsic.name} is {intrinsic.kind}, but has a [[ccb]] slot")

        for (_, s_prop) in sorted(intrinsic.properties.items()):
            if '[[Value]]' not in s_prop.attrs and '[[Get]]' not in s_prop.attrs:
                put(f"{intrinsic.name} property {s_prop.key}: neither [[Value]] nor [[Get]] is specified")
    f.close()

    # sys.exit(0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

all_intrinsics = []
intrinsic_named_ = {}

# ------------------------------------------

def ensure_intrinsic_named(name):
    if name not in intrinsic_named_:
        S_Intrinsic(name)
    return intrinsic_named_[name]

# ------------------------------------------

class S_Intrinsic:
    # An instance of this class records information about an intrinsic object.
    # It isn't an object itself.

    def __init__(self, name):
        assert re.fullmatch(r'%[^ %]+%', name)
        self.name = name
        self.kind = None
        self.slots = {}
        self.properties = {}

        all_intrinsics.append(self)
        intrinsic_named_[name] = self

    def dump(self, f):
        def put(*args): print(*args, file=f)
        put()
        put('----')
        put(self.name)
        put(f"    kind: {self.kind}")
        put(f"    slots:")
        for (slot_name, slot_value) in sorted(self.slots.items()):
            put(f"        {slot_name}: {slot_value}{check_s_value(slot_value)}")
        put(f"    properties:")
        for (_, s_prop) in sorted(self.properties.items()):
            put(f"        {s_prop.key}")
            if s_prop.attrs is not None:
                put(f"            ({s_prop.kind()} property)")
                for (n,v) in s_prop.attrs.items():
                    if v is not None:
                        put(f"            {n}: {v}{check_s_value(v)}")

    def ensure_property(self, s_prop):
        k = s_prop.key
        if k not in self.properties:
            self.properties[k] = s_prop
        else:
            old_prop = self.properties[k]
            assert old_prop.key == s_prop.key
            old_prop.attrs = merge_propAttrs(old_prop.attrs, s_prop.attrs)

def merge_propAttrs(propAttrs_a, propAttrs_b):
    if propAttrs_a == propAttrs_b: return propAttrs_a

    propAttrs_m = propAttrs_a.copy()
    for (n,v) in propAttrs_b.items():
        if n in propAttrs_m:
            assert v == propAttrs_m[n]
        else:
            propAttrs_m[n] = v
    return propAttrs_m

def merge_values(va, vb):
    if va == vb: return va

    if va is None: return vb
    if vb is None: return va

    if va in intrinsic_named_ and vb in intrinsic_named_:
        ia = intrinsic_named_[va]
        ib = intrinsic_named_[vb]
        if ia is ib: return ia.name

    assert 0, (va, vb)

def check_s_value(v):
    if v in intrinsic_named_:
        return ''
    for pattern in [
        # Undefined:
        r'\*undefined\*',

        # Null:
        r'\*null\*',

        # Boolean:
        r'\*false\*',
        r'\*true\*',

        # Number:
        r'\*NaN\*',
        r'\*\d+\*<sub>\U0001d53d</sub>',
        r'\*\d+\*<sub>\U0001d53d</sub> \(.+\)',
        r'\*-\d+\*<sub>\U0001d53d</sub> \(.+\)',
        r'\*\+0\*<sub>\U0001d53d</sub>',
        r'\*\+&infin;\*<sub>\U0001d53d</sub>',
        r'\*-&infin;\*<sub>\U0001d53d</sub>',
        r'the largest positive finite value of the Number type, .+',
        r'the smallest positive value of the Number type, .+',
        r'[Tt]he Number value for .+',
        r'the Element Size value specified in <emu-xref href="#table-the-typedarray-constructors"></emu-xref> for \w+',

        # String:
        r'the empty String',
        r'the String value \*"[^"]*"\*',
        r'\*"[^"]*"\*',

        # Symbol:
        r'the well[- ]known symbol @@\w+ \(<emu-xref href="#table-well-known-symbols"></emu-xref>\)',
        # space is a SPEC BUG

        # Object:

        # other:
        r'host-defined',
        r'emu-alg in \S+',
        r'prose in \S+',
    ]:
        if re.fullmatch(pattern, v):
            return ''

    return ' [??]'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_references_to_intrinsics():
    stderr("check_references_to_intrinsics...")

    # We can't just scan through spec.text looking for %...%,
    # because that would find occurrences in element IDs,
    # which are lower-cased.
    # Instead, just look in literal (text) nodes.
    # (Note that this skips occurrences of "%<var>Foo</var>Prototype%".)
    for tnode in spec.doc_node.each_descendant_named('#LITERAL'):
        for mo in re.compile(r'%\S+%').finditer(spec.text, tnode.start_posn, tnode.end_posn):
            itext = mo.group(0)
            itext_start = mo.start(0)
            if itext in ['%name%', '%name.a.b%']:
                # placeholders
                continue
            if itext in ['%_NativeError_%', '%_TypedArray_%']:
                # metavariable interpolation
                continue

            base_intrinsic = re.sub(r'\.[^%]+', '', itext)

            if base_intrinsic not in well_known_intrinsics:
                msg_at_posn(itext_start, f"Intrinsic doesn't exist: {base_intrinsic}")

             # XXX We should also check that any ".foo.bar" appended to the base intrinsic
             # also makes sense, but we don't have the necessary info readily available.

# vim: sw=4 ts=4 expandtab
