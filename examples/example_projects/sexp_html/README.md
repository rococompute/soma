# sexp_html

A language of its own for a folder: HTML as s-expressions, which a macro
turns into the elements of JSX.

```
(html
  (head (title "Soma"))
  (body
    (div (attrs (class "page"))
      (h1 "Hello world"))))
```

is the same element as

```
<html>
  <head> <title> "Soma" </title> </head>
  <body> <div class="page"> <h1> "Hello world" </h1> </div> </body>
</html>
```

`pages/home.proof` proves it: `home_is_jsx` states that the page written
one way equals the page written the other.

```
main.soma            Import JSX. Import pages.home. Import pages.counter.
pages/
  pages.lang         the rules of pages/: the sexp macro, and JSX
  home.soma          a page with head and body, and a component
  home.proof         home_is_jsx, and Greeting escaping any name
  counter.soma       a view with events and a data- attribute
```

`soma build -v main.soma` prints both pages as HTML.

## The language

`sexp` takes one s-expression. Soma already reads one: `(div (h1 "Hello
world"))` is `div` applied to `h1 "Hello world"`. The macro receives it as
a tree and builds the element:

| Written | Is |
| --- | --- |
| `(div child ...)` | the element `div`: a lowercase name is a tag |
| `"text"`, `42` | text |
| `name` | its value, an element or a string, as `{name}` in JSX |
| `(attrs (class "page") (on click Increment))` | the attributes and events, among the children |
| `data_id` | the attribute `data-id`: names have no dashes |
| `(Greeting "Soma")` | a call of the component `Greeting`: uppercase, as in JSX |
| `(br _)` | an element without children; `(br)` is the name `br` |

Attribute names cannot be `for`, `in`, `with` or `as`, which Soma keeps
for itself. JSX notation cannot write `data-id` at all; here it is
`data_id`.

Mistakes are reported where the page has them: `(attrs class)` gives
`an attribute is (name value), or (on event action)`, and `(br)` gives
`(br) is the name br; an element without children is written (br _)`.

## Where it applies

`pages/pages.lang` is the rules of the folder `pages/`, so every file under
`pages/` has `sexp`, and nothing else does. `main.soma` is outside
`pages/`: `sexp` is not in scope there, and it imports `JSX` itself for
`render`. The rules export `JSX`, so the pages have `element`, `render`
and JSX notation without importing anything.

The macro is ordinary Soma code in `pages.lang`: functions on `syntax`
(`Var`, `Str`, `App`, ...) that build the code of the element. Changing
the language is changing those functions.
