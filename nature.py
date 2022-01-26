import re

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# TODO:
# There are a bunch of lists here,
# which will have to be updated each time something new is used.
# It would be better to deduce most of these from the spec itself.

def check_nature(nature):
    if mo := re.fullmatch('a List of (.+)', nature):
        elements_nature = mo.group(1)
        if elements_nature in [
            'Agent Events Records',
            'Chosen Value Records',
            'Cyclic Module Records',
            'ECMAScript language values',
            'ExportEntry Records',
            'ImportEntry Records (see <emu-xref href="#table-importentry-record-fields"></emu-xref>)',
            'ImportEntry Records',
            'Objects',
            'Private Names',
            'PromiseReaction Records',
            'Record { [[Site]]: Parse Node, [[Array]]: Object }',
            'Records that have [[Module]] and [[ExportName]] fields',
            'Source Text Module Records',
            'Strings',
            'Unicode code points',
            'WriteSharedMemory or ReadModifyWriteSharedMemory events',
            'byte values',
            'events',
            'internal slot names',
            'names of ECMAScript Language Types',
            'names of internal slots',
            'pairs of Synchronize events',
            'property keys',
        ]:
            pass
        else:
            yield f"unexpected List-element type {elements_nature!r}"

    elif mo := re.fullmatch('a Completion Record whose (.+)', nature):
        sub = mo.group(1)
        if sub in [
            '[[Type]] is ~return~ or ~throw~'
        ]:
            pass
        else:
            yield f"unexpected subordinate condition {sub!r}"

    elif mo := re.fullmatch('(.+), but not (.+)', nature):
        (A, B) = mo.groups()
        yield from check_simple_nature(A)
        yield from check_nature(B)

    elif mo := re.fullmatch(r'a (ReadSharedMemory) or (ReadModifyWriteSharedMemory) event', nature):
        # The 'a' and 'event' are factored out. Should this be allowed?
        yield from check_simple_nature(mo.expand(r'a \1 event'))
        yield from check_simple_nature(mo.expand(r'a \2 event'))

    elif mo := re.fullmatch(r'(an? \w+|a property key) or ([A-Z]\w+|Private Name|ReadModifyWriteSharedMemory event)', nature):
        # The second article is elided. Should this be allowed?
        (an_X, Y) = mo.groups()
        yield from check_simple_nature(an_X)
        yield from check_simple_nature(f'a {Y}')

    elif nature == 'a possibly empty List, each of whose elements is a String or *undefined*':
        pass

    elif ' or ' in nature:
        alts = re.split(r', or |, | or ', nature)

        N = len(alts)
        if N <= 1:
            assert 0, alts
        elif N == 2:
            expected = ' or '.join(alts)
        elif N >= 3:
            expected = ', '.join(alts[:-1]) + ', or ' + alts[-1]
        if expected != nature:
            yield f"comma problem, expected: {expected}"

        for alt in alts:
            yield from check_simple_nature(alt)

    else:
        yield from check_simple_nature(nature)

def check_simple_nature(nature):
    if nature in [
        '*"handle"*',
        '*"reject"*',
        '*NaN*',
        '*null*',
        '*true*',
        '*undefined*',
        '+&infin;',
        '0',
        '1',
        '`&amp;`',
        '`^`',
        '`|`',
        '~Fulfill~',
        '~Init~',
        '~Reject~',
        '~SeqCst~',
        '~Unordered~',
        '~accessor~',
        '~all-but-default~',
        '~all~',
        '~assignment~',
        '~async-iterate~',
        '~asyncGenerator~',
        '~async~',
        '~backward~',
        '~break~',
        '~continue~',
        '~empty~',
        '~end~',
        '~enumerate~',
        '~evaluated~',
        '~evaluating-async~',
        '~evaluating~',
        '~field~',
        '~forward~',
        '~frozen~',
        '~generator~',
        '~initialized~',
        '~iterate~',
        '~key+value~',
        '~key~',
        '~lexical-this~',
        '~lexicalBinding~',
        '~lexical~',
        '~linked~',
        '~linking~',
        '~method~',
        '~namespace-object~',
        '~non-lexical-this~',
        '~normal~',
        '~number~',
        '~return~',
        '~sealed~',
        '~start+end~',
        '~start~',
        '~string~',
        '~symbol~',
        '~sync~',
        '~throw~',
        '~uninitialized~',
        '~value~',
        '~varBinding~',
        '~unlinked~',
        '~unresolvable~',
    ]:
        # a specific value
        pass

    elif nature in [
        "some other definition of a function's behaviour provided in this specification",
        'ECMAScript source text',
        'a BigInt',
        'a Boolean',
        'a CharSet',
        'a ClassFieldDefinition Record',
        'a Completion Record',
        'a Continuation',
        'a Cyclic Module Record',
        'a Data Block',
        'a FinalizationRegistry',
        'a Job Abstract Closure',
        'a JobCallback Record',
        'a List',
        'a Matcher',
        'a Module Record',
        'a Number',
        'a Parse Node',
        'a Private Name',
        'a PrivateElement',
        'a PrivateEnvironment Record',
        'a Promise',
        'a PromiseCapability Record',
        'a PromiseReaction Record',
        'a Property Descriptor',
        'a Proxy exotic object',
        'a ReadModifyWriteSharedMemory event',
        'a ReadSharedMemory event',
        'a Realm Record',
        'a Record whose field names are intrinsic keys and whose values are objects',
        'a Reference Record',
        'a Script Record',
        'a Shared Data Block event',
        'a Shared Data Block',
        'a SharedArrayBuffer',
        'a Source Text Module Record',
        'a State',
        'a String exotic object',
        'a String which is the name of a TypedArray constructor in <emu-xref href="#table-the-typedarray-constructors"></emu-xref>',
        'a String',
        'a Symbol',
        'a TypedArray element type',
        'a TypedArray',
        'a Unicode code point',
        'a WaiterList',
        'a WeakRef',
        'a bound function exotic object',
        'a built-in function object',
        'a candidate execution Record',
        'a candidate execution',
        'a character',
        'a code unit',
        'a constructor',
        'a declarative Environment Record',
        'a function Environment Record',
        'a function object',
        'a global Environment Record',
        'a globally-unique value',
        'a happens-before Relation',
        'a host-synchronizes-with Relation',
        'a mathematical value',
        'a module Environment Record',
        'a module namespace exotic object',
        'a non-negative integer that is evenly divisble by 4',
        'a non-negative integer',
        'a nonterminal in one of the ECMAScript grammars',
        'a positive integer',
        'a property key',
        'a read-modify-write modification function',
        'a reads-bytes-from mathematical function',
        'a reads-from Relation',
        'a sequence of Unicode code points',
        'a set of algorithm steps',
        'a synchronizes-with Relation',
        'a time value',
        'a value that admits equality testing',
        'a |CaseClause| Parse Node',
        'a |FunctionBody| Parse Node',
        'a |MemberExpression| Parse Node',
        'a |ModuleSpecifier| String',
        'a |NewExpression| Parse Node',
        'a |RegularExpressionLiteral| Parse Node',
        'a |ScriptBody| Parse Node',
        'an Abstract Closure with no parameters',
        'an Abstract Closure',
        'an Array exotic object',
        'an Array',
        'an ArrayBuffer',
        'an AsyncGenerator',
        'an ECMAScript execution context',
        'an ECMAScript function object',
        'an ECMAScript function',
        'an ECMAScript language value',
        'an Environment Record',
        'an Integer-Indexed exotic object',
        'an Object that conforms to the <i>IteratorResult</i> interface',
        'an Object that has a [[StringData]] internal slot',
        'an Object',
        'an abrupt completion',
        'an agent signifier',
        'an agent-order Relation',
        'an arguments exotic object',
        'an execution context',
        'an immutable prototype exotic object',
        'an initialized RegExp instance',
        'an instance of a concrete subclass of Module Record',
        'an integer',
        'an object Environment Record',
        'an ordinary object',
        'an |Arguments| Parse Node',
        'an |AssignmentExpression| Parse Node',
        'an |IdentifierName| Parse Node',
        'an |Initializer| Parse Node',
        'anything (default value is *undefined*)',
        'anything (default value is ~empty~)',
        'unknown',
    ]:
        # a set of values
        pass
    else:
        yield f"unexpected nature {nature!r}"

# vim: sw=4 ts=4 expandtab
