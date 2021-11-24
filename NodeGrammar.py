# ecmaspeak-py/NodeGrammar.py:
# A data structure for analyzing sequences of HNodes.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re
from dataclasses import dataclass

from shared import msg_at_posn, stderr

class NodeGrammar:
    '''
    A data structure for analyzing sequences of HNodes
    (in practice, the block_children of a section).
    '''

    def __init__(self, units, prep_regex):
        '''
        Each input unit is a tuple (pattern, processor),
        where `pattern` consists of a sequence of atoms,
        and `processor` indicates what to do if the pattern matches.

        A pattern of N atoms matches the next N nodes
        if each atom matches the corresponding node.

        An atom can be simply a string,
        which matches a node if it's the node's element-name.

        An atom can also be a pair (name, regex),
        which matches a node if `name` is the node's element-name,
        and `regex` full-matches the node's inner source text.

        `prep_regex` is a callable to apply to regex before compiling them,
        so that regex (as they appear to the user) can be simpler.
        '''

        self.units = []
        for unit in units:
            (raw_pattern, response) = unit
            compiled_pattern = []
            for raw_atom in raw_pattern:
                if isinstance(raw_atom, str):
                    compiled_atom = raw_atom
                elif isinstance(raw_atom, tuple):
                    (element_name, regex) = raw_atom
                    prepped_regex = prep_regex(regex)
                    compiled_atom = (element_name, re.compile(prepped_regex))
                else:
                    assert 0, unit
                compiled_pattern.append(compiled_atom)
            self.units.append(NodeGrammarUnit(raw_pattern, compiled_pattern, response))

    def scan_section(self, section):
        if section.section_kind in ['syntax_directed_operation', 'early_errors', 'changes']:
            arguments_style = 1
        elif section.section_kind in ['CallConstruct', 'function_property', 'accessor_property', 'other_property']:
            arguments_style = 2
        else:
            assert 0, section.section_kind

        results = []
        hnodes = section.block_children
        next_i = 0
        while next_i < len(hnodes):
            for unit in self.units:
                assert isinstance(unit.compiled_pattern, list)

                n = len(unit.compiled_pattern)
                if next_i + n > len(hnodes):
                    # This pattern is too long to match at this point in hnodes.
                    continue

                match_results = [
                    node_matches_atom(child, element_atom)
                    for (child, element_atom) in zip(hnodes[next_i:], unit.compiled_pattern)
                ]
                if not all(match_results):
                    # pattern didn't match
                    continue

                # pattern matched!
                unit.counter += 1

                matched_nodes = hnodes[next_i : next_i + n]

                if unit.processor is None:
                    pass
                elif unit.processor == 'print':
                    print()
                    for node in matched_nodes:
                        print('>', node.source_text())
                elif callable(unit.processor):
                    # arguments = matched_nodes
                    arguments = []
                    if arguments_style == 2:
                        arguments.append(section)
                    for (matched_node, match_result) in zip(matched_nodes, match_results):
                        # If the atom captured something(s), use that/them as the arguments to the callable.
                        if hasattr(match_result, 'groups') and len(match_result.groups()) > 0:
                            if arguments_style == 1:
                                arguments.extend(match_result.groups())
                            elif arguments_style == 2:
                                arguments.append(match_result)
                        else:
                            arguments.append(matched_node)
                    try:
                        result = unit.processor(*arguments)
                    except TypeError:
                        stderr()
                        stderr()
                        stderr("When trying to invoke processor for pattern:")
                        stderr(unit.raw_pattern)
                        raise
                    if result is None:
                        pass
                    elif isinstance(result, list):
                        results.extend(result)
                    else:
                        results.append(result)
                else:
                    assert 0, unit.processor
                next_i += n
                break
            else:
                msg_at_posn(hnodes[next_i].start_posn, f"At this point, no pattern matches (in {section.section_kind} section)")
                return []
        return results

    def each_unused_pattern(self):
        for unit in self.units:
            if unit.counter == 0:
                yield unit.raw_pattern

@dataclass
class NodeGrammarUnit:
    raw_pattern: list
    compiled_pattern: list
    processor: callable
    counter: int = 0

def node_matches_atom(node, atom):
    if isinstance(atom, str):
        return (node.element_name == atom)
    elif isinstance(atom, tuple):
        (desired_element_name, desired_content_re) = atom
        return (
            node.element_name == desired_element_name
            and
            desired_content_re.fullmatch(node.inner_source_text())
        )
    else:
        assert 0, atom

# vim: sw=4 ts=4 expandtab
