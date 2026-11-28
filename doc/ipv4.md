# Source IPv4 and CIDR library

`Soma.IPv4` implements IPv4 dotted-quad/prefix parsing and CIDR membership in
Source. Typed addresses carry `0 <= value < 2^32`; prefixes carry a width no
greater than 32. Binary `Z` values avoid overflowing arithmetic and giant
logical unary address values. Prefix matching compares quotients by
`2^(32-width)`; no native IP membership decision is invoked.

Forty-nine checked results cover CIDR geometry and the parser. Membership is
equivalent to the exact aligned network interval, with subnet containment,
disjoint intervals, `/0` and `/32` laws. The parser's accepted address and
prefix languages are characterized in both directions by byte-level grammars.
All results are closed under the global context: no logical axiom or kernel
word primitive is required.

`decimal_character` specifies ASCII codes 48–57 and their numeric values;
`digit_character_iff` proves the parser's classifier agrees, for every byte.
`decimal_span` specifies those bytes and their left-folded modular value.
`decimal_token` additionally requires a nonempty maximal span and
bounds within the input. `octet_token` excludes leading-zero decimal spellings.
`quad_grammar` requires four such tokens separated by dots, each value in
`[0,255]`, and the exact address polynomial. `prefix_grammar` additionally
requires a slash and a decimal width in `[0,32]`. The whole-input language
theorems require the final position to equal the input length. Successful
parses satisfy these grammars; matching grammar witnesses produce successful
parses with the specified address/width; failure is equivalent to the absence
of any grammar witness. These are content specifications, not equations
restating a scanner step.

The parser follows the installed `ipaddr` implementation's decimal grammar,
leading-zero rejection, error precedence and positions. It explicitly models
63-bit modular decimal accumulation. Thus existing wrapped decimal spellings
remain accepted where the native parser accepts them; this library does not
silently introduce a new input cap or a stricter spelling policy. A separate
strict-decimal security policy would need an explicit contract and tests.
Structured failures retain the information needed to reproduce existing
messages and exception payloads at an effectful caller boundary.

`test-suite/misc/soma_ipv4.sh` extracts actual parser/membership functions and
compares 344,098 cases per backend with `Ipaddr.V4`, including all prefix
widths, boundary octets, exact error messages/order, random binary inputs and
long wrapped decimal spellings. This is implementation-conformance evidence,
separate from the Source acceptance/rejection proofs. Exact failure reasons,
their precedence and messages are tested against the native parser; that
failure-detail refinement is not yet proved. Compiler/extraction refinement
is also not implied by the Source grammar proofs.

`test-suite/misc/soma_ipv4_grammar.sh` rechecks the unchanged library, then
requires six actual parser corruptions to fail their relevant proofs:
a wrong digit classifier, incorrect decimal accumulation, removal of the
octal guard, a wrong address polynomial, a wrong delimiter and ignored trailing
input. The assumptions
fixture checks all forty-nine results individually.

The library is not yet connected to Kykeon's production egress policy. Typed
integration, native exception construction, entry-level security proofs and
versioned runtime/TCB receipts remain outstanding. Compiler/runtime correctness
and native natural-counter representation are also part of the remaining
refinement boundary.
