# Source IPv4 and CIDR library

`Soma.IPv4` implements IPv4 dotted-quad/prefix parsing and CIDR membership in
Source. Typed addresses carry `0 <= value < 2^32`; prefixes carry a width no
greater than 32. Binary `Z` values avoid overflowing arithmetic and giant
logical unary address values. Prefix matching compares quotients by
`2^(32-width)`; no native IP membership decision is invoked.

Sixteen checked results cover block bounds/alignment, equivalence of membership
to the exact network interval, subnet containment, disjoint intervals, `/0`
and `/32`, decimal digit/accumulator ranges and cursor progress. These results
are closed under the global context: no logical axiom or kernel word primitive
is required.

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
not a complete parser-grammar or extraction-refinement proof. The parser
proofs currently establish numeric and cursor bounds, not the full input
language's correctness theorem.

The library is not yet connected to Kykeon's production egress policy. Typed
integration, native exception construction, entry-level security proofs and
versioned runtime/TCB receipts remain outstanding. Compiler/runtime correctness
and native natural-counter representation are also part of the remaining
refinement boundary.
