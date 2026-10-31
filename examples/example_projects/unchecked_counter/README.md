# unchecked_counter

`counter_server` without its parser: the start of each request is what
the address or the cookie says, unchecked, as an `Any`. What would go
wrong, and what Soma says about it, before it runs and when it runs.

```
main.soma            main: serve 8080 answer, a MirageOS image (main.hvt)
pages/               as in counter_server: the language, the state, its proofs
web/
  request.soma       start_of request : Any, from the address, the cookie, or 0
  server.soma        page (start_of request): page takes an N
  server.proof       counter_server's theorem, which still checks
```

The difference from `counter_server` is in `web/request.soma`:

```
start_of (request : string) : Any :=
  match url_count request with
  | Some v => v                    (* a string *)
  | None =>
    match cookie_count request with
    | Some v => v                  (* a string *)
    | None => 0%N                  (* an N *)
    end
  end.
```

and `web/server.soma` gives it to `page`, which takes an `N`. It type
checks: an `Any` is consistent with every type, so a cast from `Any` to
`N` is inserted, to be checked when it runs.

## Before it runs

`soma build main.soma` says what that cast may meet:

```
File "web/server.soma", line 30, characters 0-114:
Warning:
respond: start_of request is an Any that may be
a string (made an Any in start_of), and it is used as an N. A string is never
an N: where it is one, this is a run-time error, "expected an N,
but got a string". It may also be an N (made an Any in start_of), which is
fine. [gradual-may-fail,vernacular,default]
```

Soma follows `start_of request` back into `start_of`, through its
`match`es, to the values that were made `Any`s: two strings, from the
address and the cookie, and an `N`, the 0. A string is never an `N`, so
the cast fails for every request that has a count, `41` as much as `-1`:
a cast checks a type, and never converts. The same warning is on
`served_state_increases` in `server.proof`: the theorem is about an `Any`
that may be a string, so for those requests it says nothing (below).

## When it runs

`soma run main.soma`, then:

| Asked for | Answer | In the image's log |
| --- | --- | --- |
| `/` | the page at 0 | |
| `/?count=41` | nothing: the connection is closed | `Run-time error: expected an N, but got a string.` |
| `/?count=-1` | nothing | `Run-time error: expected an N, but got a string.` |

The server goes on: a request that fails is that request's. But the
person asking gets no answer, where `counter_server` says `400` and why;
and a valid count fails as an invalid one does.

## The proof that still checks

`server.proof` proves `counter_server`'s theorem: the counter's state,
from the start of any request, strictly increases. It checks: it holds
for every `N`, and the start is an `N`, the cast's. But for a request
with a count, that `N` is `raise`, an error, not a number; the theorem is
true of it, and says nothing about what that request is served. In
`counter_server`, the start is a number that the parser accepted, and
`request.proof` says which.

## What the warning looks at

`gradual-may-fail` (`GradualTyping.casts_that_may_fail`) checks each
cast from `Any` to a type `T` in a definition: it follows the value back,
through `match`es, `let`s and the definitions it calls, to the casts that
made it an `Any`, and reports each type it may have been made from that
is not consistent with `T`, with the definition where it was. A value
whose origin is not known, an argument of type `Any`, `?`, is not
reported: that is gradual code doing what it says.
