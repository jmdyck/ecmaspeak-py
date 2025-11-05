
# ecmaspeak-py/algos.py:
# This module declares the classes and some functions
# relating to the Alg->AlgHeader->AlgDefn hierarchy.
#
# Copyright (C) 2023  J. Michael Dyck <jmdyck@ibiblio.org>

import re, typing
from dataclasses import dataclass

import shared
from HTML import HNode
from shared import spec, stderr
import Pseudocode

# An `Alg` has zero or more `AlgHeader`s,
# each of which has zero or more `AlgDefn`s,
# each of which has a chunk of pseudocode.

# In a lot of cases, those "zero or more" are just "one",
# and the Alg -> AlgHeader -> AlgDefn 'hierarchy'
# seems like pointless indirection.
# Here are the exceptions to that generalization...

# Cases where an Alg has multiple AlgHeaders:
#
# - essential internal methods
#   E.g., the spec has 3 definitions of the internal method [[IsExtensible]],
#   one for each of ordinary object, module namespace exotic object, and Proxy exotic object.
#   So there's an Alg for the name '[[IsExtensible]]',
#   and it has 3 AlgHeaders.
# 
# - "concrete methods" of Records
#   E.g., there's an Alg for `CreateImmutableBinding`,
#   and it has 3 AlgHeaders, one for each of
#   Declarative ER, Object ER, and Global ER.
#
# - the two remaining SDOs that are defined over multiple sections:
#   `Evaluation` and `MV`
#
# - Early Errors
#
# - CharacterValue + IsCharacterClass,
#   where the alg has a header in the main body and one in Annex B

# Cases where an Alg has zero AlgHeaders:
#
# - Shorthands
#   (E.g., IfAbruptRejectPromise)
#
# - Operations (mostly numeric) that are defined very briefly
#   (E.g., abs, floor, scf)

# -----

# Cases where an AlgHeader has multiple AlgDefns:
#
# - Most syntax-directed operations.
#   E.g., For 'BoundNames', there's an Alg with a single AlgHeader
#   (because it's defined in only one section), but that AlgHeader
#   has 51 AlgDefns (because there are 51 grammar/algorithm pairs in the section).
#
# - Most Early Errors
#   (because most "Early Errors" sections have multiple grammar/constraint pairs)

# Cases where an AlgHeader has zero AlgDefns:
#
# - CreateImmutableBinding for Object Environment Record
#   and DeleteBinding for Module Environment Record,
#   where the section exists only to say that the method is never called.
#
# - Built-in functions that are just an 'alias' to
#   a function defined elsewhere in the spec.
#   (E.g., Number.parseFloat, Set.prototype.keys, String.prototype.trimLeft)
#
# - Built-in functions that are defined via prose,
#   possibly including a reference to a definition in ECMA-402.
#   (E.g., Number.prototype.toLocaleString, Date.now)
#
# - The first section for 'Evaluation',
#   which exists only to be the landing spot for links.
#
# - Most Host-defined operations
#   (Not all, because a few have a default implementation.)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

spec.alg_info_ = { 'bif': {}, 'op': {} }
# These need to be separate because 'Set' is the name of
# both an abstract operation and a built-in function.

def ensure_alg(alg_species, alg_name):
    bif_or_op = 'bif' if alg_species.startswith('bif:') else 'op'
    iffn = spec.alg_info_[bif_or_op]

    if alg_name in iffn:
        alg_info = iffn[alg_name]
        assert alg_info.name == alg_name
        assert alg_info.species == alg_species
    else:
        alg_info = Alg(alg_name, bif_or_op, alg_species)
        iffn[alg_name] = alg_info

    return alg_info

class Alg:
    # An operation (widely construed) or
    # the algorithmic aspect of a (built-in) function.
    def __init__(self, name, bif_or_op, species):
        self.name = name
        self.bif_or_op = bif_or_op
        self.species = species
        self.invocations = []
        self.callees = set()
        self.callers = set()
        self.headers = []

    def __str__(self):
        return f"{self.bif_or_op}: {self.name}"

    def __lt__(self, other):
        return (
            self.bif_or_op < other.bif_or_op
            or
            self.bif_or_op == other.bif_or_op
            and
            self.name < other.name
        )

    def all_definitions(self):
        return [
            alg_defn
            for alg_header in self.headers
            for alg_defn in alg_header.u_defns
        ]

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
                returns: {self.return_nature_node.source_text() if self.return_nature_node else 'None'}
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

        self.parent_alg = ensure_alg(self.species, self.name)
        self.parent_alg.headers.append(self)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class AlgDefn:
    pass

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
                section = alg_header.section
                put(f"      {section.section_num} {section.section_title}")
                if alg_header.for_phrase: put(f"        for: {alg_header.for_phrase}")
                # alg_header.params
                # alg_header.return_nature_{normal,abrupt}
                # alg_header.description_paras
                put(f"        {len(alg_header.u_defns)} defns")
                n_defns_via_headers += len(alg_header.u_defns)
                for alg_defn in alg_header.u_defns:
                    assert alg_defn.parent_header is alg_header

            assert n_defns_via_headers == len(alg_info.all_definitions())
            # alg_info.invocations
            # alg_info.callees
            # alg_info.callers
        put()

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_alg_consistency():
    stderr("check_alg_consistency ...")

    # (Some of these checks could be performed as each alg_header is created,
    # and maybe should be.)

    f = shared.open_for_output('alg_anomalies')

    def put(*args): print(*args, file=f)

    for bif_or_op in ['op', 'bif']:
        for (_, alg) in sorted(spec.alg_info_[bif_or_op].items()):

            # --------------
            # name, species:

            for alg_header in alg.headers:
                assert alg_header.name == alg.name
                assert alg_header.species == alg.species

            # -----------
            # for_phrase:

            if alg.species == 'shorthand':
                assert len(alg.headers) == 0

            elif alg.species.startswith('op: discriminated by type:'):

                for alg_header in alg.headers:
                    sect = alg_header.section
                    if re.fullmatch(r'Implementation of .*Module Record Abstract Methods', sect.parent.section_title):
                        # Look at the grandparent
                        expected_for_phrase = {
                            'Cyclic Module Records'       : 'a Cyclic Module Record _module_',
                            'Source Text Module Records'  : 'a Source Text Module Record _module_',
                            'Synthetic Module Records'    : 'a Synthetic Module Record _module_',
                        }[sect.parent.parent.section_title]
                    else:
                        # Look at the parent
                        expected_for_phrase = {
                            'Declarative Environment Records'                     : 'a Declarative Environment Record _envRec_',
                            'Object Environment Records'                          : 'an Object Environment Record _envRec_',
                            'Function Environment Records'                        : 'a Function Environment Record _envRec_',
                            'Global Environment Records'                          : 'a Global Environment Record _envRec_',
                            'Module Environment Records'                          : 'a Module Environment Record _envRec_',

                            'Ordinary Object Internal Methods and Internal Slots' : 'an ordinary object _O_',
                            'ECMAScript Function Objects'                         : 'an ECMAScript function object _F_',
                            'Built-in Function Objects'                           : 'a built-in function object _F_',
                            'Bound Function Exotic Objects'                       : 'a bound function exotic object _F_',
                            'Array Exotic Objects'                                : 'an Array exotic object _A_',
                            'String Exotic Objects'                               : 'a String exotic object _S_',
                            'Arguments Exotic Objects'                            : 'an arguments exotic object _args_',
                            'TypedArray Exotic Objects'                           : 'a TypedArray _O_',
                            'Module Namespace Exotic Objects'                     : 'a module namespace exotic object _O_',
                            'Immutable Prototype Exotic Objects'                  : 'an immutable prototype exotic object _O_',
                            'Proxy Object Internal Methods and Internal Slots'    : 'a Proxy exotic object _O_',
                        }[sect.parent.section_title]
                    if alg_header.for_phrase != expected_for_phrase:
                        put()
                        put(f"{sect.section_num} {sect.section_title}")
                        put(f"  unexpected for_phrase")
                        put(f"  expected: {expected_for_phrase}")
                        put(f"       got: {alg_header.for_phrase}")

                assert elements_are_distinct([
                    alg_header.for_phrase
                    for alg_header in alg.headers
                ])
                # TODO: 
                # We should also check that they're mutually exclusive type-wise.
                # (Though I think it's pretty unlikely that they wouldn't be.)

            elif (
                alg.species.startswith('op: discriminated by syntax:') 
                or
                alg.species.startswith('op: singular')
                or
                alg.species.startswith('bif:')
            ):
                # All the for_phrases must be None.
                assert all(
                    alg_header.for_phrase is None
                    for alg_header in alg.headers
                )

            else:
                assert 0, alg.species

            # -------
            # params:

            if len(alg.headers) == 0:
                # Nowhere to get params from
                pass

            else:
                # Copy the params from the first header:
                alg_header = alg.headers[0]
                alg.params = [
                    AlgParam(param.name, param.punct, param.nature)
                    for param in alg_header.params
                ]

                # Check that the params in subsequent headers (if any) are consistent:
                for alg_header in alg.headers[1:]:
                    if len(alg_header.params) != len(alg.params):
                        sect = alg_header.section
                        put()
                        put(f"{sect.section_num} {sect.section_title}")
                        put(f"  gives header for `{alg.name}` with {len(alg_header.params)} params")
                        put(f"  but expected {len(alg.params)} params")
                    for (header_param, alg_param) in zip(alg_header.params, alg.params):
                        assert header_param.name   == alg_param.name
                        assert header_param.punct  == alg_param.punct
                        assert header_param.nature == alg_param.nature

            # -------------------
            # return_nature_node:

            if (
                alg.species.startswith('bif:')
                or
                alg.species == 'op: discriminated by syntax: early error'
            ):
                assert all(
                    alg_header.return_nature_node is None
                    for alg_header in alg.headers
                )

            elif alg.species == 'op: discriminated by syntax: steps' and len(alg.headers) > 1:
                # The first header has a non-None return_nature_node,
                # the rest have None?

                for (i, alg_header) in enumerate(alg.headers):
                    sect = alg_header.section
                    if i == 0:
                        if alg_header.return_nature_node is None:
                            put()
                            put(f"{sect.section_num} {sect.section_title}")
                            put(f"  first header for the alg doesn't have a return_nature_node")
                    else:
                        if alg_header.return_nature_node is not None:
                            put()
                            put(f"{sect.section_num} {sect.section_title}")
                            put(f"  return_nature_node is not None")

            elif alg.species.startswith('op: discriminated by type:'):
                pass
                # TODO:
                # Each alg_header.return_nature_node should denote a type that
                # is a sub-type of (or is equal to)
                # the return-type of the 'abstract' declaration of the alg.

            else:
                for alg_header in alg.headers:
                    if alg_header.return_nature_node is None:
                        sect = alg_header.section
                        put()
                        put(f"{sect.section_num} {sect.section_title}")
                        put(f"  For {alg.name}, return_nature_node is None")

            # -----------
            # TODO:
            # alg.all_definitions()
            # should have mutually exclusive discriminators
            # (bumps up against SDO coverage?)

    f.close()

def elements_are_distinct(L):
    return len(set(L)) == len(L)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
