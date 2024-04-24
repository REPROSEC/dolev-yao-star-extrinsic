# Collaboration

- Discussions of features and bugs should take place in [**GitHub Issues**](https://github.com/REPROSEC/dolev-yao-star-extrinsic/issues). This also has the advantage that we can reference the specific issue in meetings.
- Everybody should **create tasks** in the [GitHub Project](https://github.com/orgs/REPROSEC/projects/1) for their work and assign the tasks to themselves.
    - You can also create tasks from Issues and vice versa
- Every change to DY* has to be developed in a separate branch
- If a feature is ready to be merged into the main branch, you **must create a pull request**, and at least one person must review the code changes.
    - PRs are an essential process to guarantee the code quality of DY*.

# Protocol Analysis

- Protocol analysis should take place in a **separate repository** that can either be public or private.
    - You can integrate DY* and Comparse by either using git submodules (preferred solution) or by referencing folders on your system.
- An **example project** will show how to model a protocol in another repository sometime in the future, and it will be linked here.
- For paper publication, you can either pack all the dependencies into one repository or use git submodules to reference a specific git commit in the public DY* and Comparse repositories.

# Code formatting

Unfortunately, there is no code formatter for F\*.
This section describe formatting guidelines that are used in DY\*.

## Tabulations

DY\* code is tabulated using two spaces.
This should be configured automatically on modern editors using [.editorconfig](https://editorconfig.org/).

## `val` and `let`

In F\*, functions and lemmas can be declared in two ways.

```fstar
let f (x:type1) (y:type2): type3 =
  ...

val f: type1 -> type2 -> type3
let f x y =
  ...
```

The DY\* codebase uses the second style, with separate `val` and `let`.

Furthermore, unless the `val` is short, many newlines are inserted.

```fstar
val f: // one line for the val and the function name
  #bytes:Type0 -> {|bytes_like bytes|} -> // one (or several) lines for implicit arguments
  bytes -> bytes -> // one (or several) lines for explicit arguments
  prop // one line for the return type
```

When there are many implicit or explicit arguments,
newlines can be inserted at sensible places
to group arguments in different categories.

```fstar
val lem:
  #bytes:Type0 -> {|bytes_like bytes|} -> // one line for `bytes`
  #a:Type -> #b:Type -> // one generic types
  x:a -> // one line for parameters specific to the lemma
  f:(a -> b) -> l:list a -> // one line for the arguments of the function we prove
  Lemma // see next section about formatting of Lemmas
  (requires List.Tot.memP x l)
  (ensures List.Tot.memP (f x) (List.Tot.map f l))
```

## Lemmas

In general, lemmas with `requires` and `ensures` should be written like this.

```fstar
val lemma:
  ... -> // implicits
  ... -> // explicits
  Lemma
  (requires ...)
  (ensures ...)
  [SMTPat (...)] //optional
```

When the `requires` or `ensures` are big, they should be written like this.

```fstar
val lemma:
  ... -> // implicits
  ... -> // explicits
  Lemma
  (requires
    ... /\
    ... /\
    ...
  )
  (ensures (
    match ... with
    | ... -> ...
    | ... -> ...
  ))
  [SMTPat (...)] //optional
```

The when the `requires` or `ensures` span multiple lines,
the keywords `requires` and `ensures` live on their own line.
In general the `requires` is a big conjunction,
each hypothesis should be on a separate line.
The `ensures` often contains a `let`, a `match`,
in that case extra parenthesis are needed for F\*'s parser.

When the lemma is very short, it may be written on one line.

```fstar
val lemma:
  x:nat -> y:nat ->
  Lemma (x+y == y+x)
```

If there is no `requires` and the `ensures` is big, it may be written like this.

```fstar
val lemma:
  ... ->
  Lemma
  (ensures (
    ...
  ))
  [SMTPat (...)] //optional
```

## Inside a `match`

When a match case is short, it can be written in one line like this.

```fstar
match ... with
| Some x -> x
...
```

When a match case spans several lines, then the match pattern must live on its own line.

```fstar
match ... with
| Some x -> (
  let ... = ... in
  if ... then (
    ...
  ) else (
    ...
  )
)
| None -> (
  ...
)
```

The outer parenthesis may be omited (like `| Some x -> ...` instead of `| Some x -> (...)`).
However, beware of parsing ambiguities, e.g. in the case of nesting matches.

## Comments and documentation

Sections of the code is separated using comments like this.
In some editors (such as Emacs), it is written in a big font.

```fstar
(*** Section name ***)
```

Documentation should be written like this.

```fstar
...

/// this is some documentation
/// that spans several lines

val f:
  ...
```

To improve the diffs on the documentation,
it should be written using [semantic line breaks](https://sembr.org/).
