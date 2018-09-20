
# ecmaspeak-py/Tokenizer.py:
# A small tokenizer class.
# (So far, I only use it to parse the content of <emu-grammar> elements.)
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re

class Tokenizer:
    def __init__(self, token_spec):
        self.token_specs = [
            TokenSpec(token_pattern, token_response)
            for (token_pattern, token_response) in token_spec
        ]

    def tokenize(self, r_line):
        tokens = []
        offset = 0
        while offset < len(r_line):
            matches = []
            for token_spec in self.token_specs:
                mo = token_spec.reo.match(r_line, offset)
                if mo:
                    assert mo.start(0) == offset
                    length = mo.end(0) - mo.start(0)
                    matches.append( (length, token_spec, mo) )
            if len(matches) == 0:
                # We call print() rather than report(),
                # because we expect these errors to occur
                # only during debugging of the token_spec.
                print("Tokenization error:")
                print(r_line)
                print('-' * offset + '^')
                raise TokenizationError
            elif len(matches) == 1:
                [(length, token_spec, mo)] = matches
            else:
                # matches.sort(reverse=True)
                # (length, token_spec, mo) = matches[0]
                # assert matches[1][0] < length # i.e. there wasn't a tie for length
                maxlen = max(length for (length,_,_) in matches)
                matches_with_maxlen = [
                    match
                    for match in matches
                    if match[0] == maxlen
                ]
                if len(matches_with_maxlen) == 0:
                    assert 0
                elif len(matches_with_maxlen) == 1:
                    [(length, token_spec, mo)] = matches_with_maxlen
                else:
                    print("Tokenization error (multiple max-length matches):")
                    print(r_line)
                    print('-' * offset + '^')
                    raise TokenizationError

            # We have a match
            token_spec.n_matches += 1

            if token_spec.response is None:
                # skip it
                pass
            elif callable(token_spec.response):
                token = token_spec.response(mo.group)
                tokens.append(token)
            else:
                groups = mo.groups()
                if not groups: groups = (mo.group(0),)
                token = (token_spec.response, groups)
                tokens.append(token)

            offset = mo.end(0)
        return tokens

    def print_unused_paterns(self):
        n_unmatched_patterns = sum(
            token_spec.n_matches == 0
            for token_spec in self.token_specs
        )
        if n_unmatched_patterns == len(self.token_specs):
            print()
            print("Tokenizer was not used?")
        elif n_unmatched_patterns > 0:
            print()
            print("unused Tokenizer patterns:")
            for token_spec in self.token_specs:
                if token_spec.n_matches == 0:
                    print('    ' + token_spec.pattern)

class TokenSpec:
    def __init__(self, pattern, response):
        self.pattern = pattern
        self.response = response
        self.reo = re.compile(pattern)
        self.n_matches = 0

class TokenizationError(Exception):
    pass

# vim: sw=4 ts=4 expandtab
