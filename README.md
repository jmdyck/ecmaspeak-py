<!--
ecmaspeak-py/README.md:

Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>
-->

# ecmaspeak-py

## Elevator pitch

What if the ECMAScript specification were executable?

(To be clear, I don't mean:
"What if the ES spec were rewritten to use an existing programming/specification language?",
but rather:
"What if we accepted (more or less) the notation that the ES spec is currently written in, and made it executable?")

## Introduction

"ECMASpeak" is the unofficial name for the notation
that the ECMAScript specification (tc39/ecma262) uses
to define the ECMAScript language.

Roughly speaking, it consists of
grammar productions + pseudocode + prose.
(The line between pseudocode and prose is fuzzy,
since the pseudocode tends to be fairly prose-y anyway.)

It's an ad hoc notation,
outlined in the ES spec's "Notational Conventions" clause.

*   The grammar notation is BNF plus various extensions.
    [5.1 Syntactic and Lexical Grammars](https://tc39.github.io/ecma262/#sec-syntactic-and-lexical-grammars)
    defines it fairly completely.

*   There are several forms of pseudocode
    (at least 4, by my count: `<emu-alg>`, `<emu-eqn>`, inline SDO defns, and early error rules).
    (Probably some `<emu-table>` elements should also be considered pseudocode.)
    [5.2 Algorithm Conventions](https://tc39.github.io/ecma262/#sec-algorithm-conventions)
    mostly focuses on `<emu-alg>` elements.
    It covers the general appearance of their contents
    (block-structured via significant indentation)
    and gives some low-level constructs/syntax.
    Otherwise, the pseudocode notation is left pretty open-ended.

## This repo

The idea of this repo is to treat ECMASpeak
as if it's a real notation for specifying a programming language,
and to write software that processes
a specification written in ECMASpeak (i.e., the ES spec).

There's 

 *  Static analysis of the ES spec.

    This finds certain kinds of bugs and inconsistencies in the spec.

 *  Execution of the ES spec.

    Roughly speaking, if you execute the ES spec,
    you're running an interpreter for the ES language.
    This would have the benefits of a reference implementation (RI),
    only moreso:

    *   As with any RI, it could answer questions like "How should this code behave?".

        But more than that, because it arises directly from the ES spec,
        it could answer questions like "*Why* should it behave like that?",
        i.e. "What specific lines in the spec cause it to behave that way?".

    *   As with any RI, you could run it against the test suite
        [tc39/test262](https://github.com/tc39/test262/).
        Any resulting test failures might indicate mistakes in the test suite,
        or unclear parts of the ES spec. 

        But more than that, it could record exactly which lines of the spec
        are executed by the tests,
        and so find lines that are not exercised by the test suite.
        In general, you could run coverage analysis on the spec.
        (This might lead to new tests to cover holes,
        or elimination of "dead code" in the spec.)

Moreover, these benefits would also accrue to
proposed revisions of the spec,
assuming they don't introduce new notation.
That is, as long as someone has written the revision in "conforming ECMASpeak",
it should just work for the above purposes.

## Status

Currently, this repo implements the static analysis part,
and has a start at the execution part.

The code is somewhat messy.
Partly this is due to the ad hoc nature of ECMASpeak itself.
Partly it's because I don't always have a firm idea of how to proceed.

If the software complains about something in the spec
(or crashes with an unhandled exception),
there might be something wrong in the spec,
or there might be something wrong in the code,
or it might just be something new in the spec that the code isn't prepared for.
And it might not be obvious which of those applies:
ECMASpeak is an ad hoc notation,
so 'correctness' is sometimes a matter of opinion.

Given the above,
I'm not sure how useful this software
is going to be (right away) for other people.
But it's a start,
and at least it's here in case I get hit by a bus.

<!--
vim: sw=4 ts=4 expandtab
-->
