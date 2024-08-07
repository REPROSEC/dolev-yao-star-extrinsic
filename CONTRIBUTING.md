# Collaboration

- Discussions of features and bugs should take place in [**GitHub Issues**](https://github.com/REPROSEC/dolev-yao-star-extrinsic/issues). This also has the advantage that we can reference the specific issue in meetings.
- Everybody should **create tasks** in the [GitHub Project](https://github.com/orgs/REPROSEC/projects/1) for their work and assign the tasks to themselves.
    - You can also create tasks from Issues and vice versa
- Every change to DY* has to be developed in a separate branch.
- If a feature is ready to be merged into the main branch, you **must create a pull request**, and at least one person must review the code changes.
    - PRs are an essential process to guarantee the code quality of DY*.
- PRs are merged via GitHub's `Squash and merge` option to keep the commit history clean.
- After merging a PR, the corresponding branch must be deleted to keep the repository tidy.
- Commits in the main branch must use [conventional commits](https://www.conventionalcommits.org/en/v1.0.0/#summary), and be worded using the imperative tense.
- Commits in other branches don't have to follow any rule, only the squashed commit must follow the main branch rule.

# Protocol Analysis

- Protocol analysis should take place in a **separate repository** that can either be public or private.
    - You can integrate DY* and Comparse by either using git submodules (preferred solution) or by referencing folders on your system.
- An **example project** will show how to model a protocol in another repository sometime in the future, and it will be linked here.
- For paper publication, you can either pack all the dependencies into one repository or use git submodules to reference a specific git commit in the public DY* and Comparse repositories.

# Coding style

## Proof hygiene

F\* uses by default a `fuel` and `ifuel` of 8, which is too much.
A good hygiene for doing proofs with F\* is to use a fuel and ifuel as low as possible,
ensuring stable and fast proofs.

DY\* files should start by setting them to a low value, like this.

```fstar
#set-options "--fuel 0 --ifuel 0"
```

If a specific function or lemma need more fuel, do it like this.

```fstar
#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val f: ...
let f = ...
#pop-options
```

If every function of a file need non-zero fuel or ifuel
(e.g. every function and lemma is recursive),
then it is okay to set them to 1 at the beginning of the file.

```fstar
#set-options "--fuel 1 --ifuel 1"
```

## Argument ordering

Function arguments are written in some order,
for example in

```fstar
val map:
  #a:Type ->
  f:(a -> b) -> l:list a ->
  list b
```

the first argument is `#a:Type`,
the second one is `f:(a -> b)`
and the third one is `l:list a`.

Arguments should be ordered from the most generic one to the most specific one.
There are several reasons for that:

- this helps with curryfication,
  which is useful when doing proofs in F\*
  (because it is much easier to do proofs on `map f` than `fun l -> map f l`)
- this helps having a consistent argument order throughout the project

In the example of `map`,
the most generic parameter is `#a:Type`,
because it cannot be changed without changing `f:(a -> b)` or `l:list a`.
The second most generic parameter is `f:(a -> b)`
because often one function is applied to many different lists.
Finally, `l:list a` is the least generic argument (or, the most specific one).
Hence the arguments of the `map` function above are well-ordered.

Often, several arguments may be as generic as other arguments,
in that case some arbitrary order must be chosen between them,
but that order should be consistent across functions.

When there are many arguments with the same genericity,
it is good practice to create a record type for these arguments.
This provides an approximation of named arguments,
to avoid mixing their order when calling the function
(which is crucial when the arguments have the same type
hence are not distinguished by the typechecker).

```fstar
type f_inputs = {
  my_dh_priv_key: bytes;
  their_dh_pub_key: bytes;
  current_ratchet_key: bytes;
}

val f: f_inputs -> ...
```

## Names for Typeclass Instances

Instances of a typeclass are named as "class name" followed by "type", that is the same order as in the instance declaration.
For example:
```fstar
instance integer_encodable_usage: integer_encodable usage = ...
instance bytes_like_bytes: bytes_like bytes = ...
```

If the typeclass has more than one type argument,
all arguments should be explicitly specified in the name of the instance
in the order given in the instance declaration:
```fstar
instance parseable_serializeable_bytes_tagged_state: parseable_serializeable bytes tagged_state = ...
```
unless there is a natural way to combine the type arguments as in
```fstar
instance map_types_pki: map_types pki_key pki_value = ...
```

For typeclasses without arguments,
the typeclass has to be explicitly mentioned in the instance declaration (after the `:`) and
the name of the instance begins with the class name
followed by some identifier:
```fstar
instance crypto_invariants_nsl : crypto_invariants = ...
```

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

When the `requires` or `ensures` span multiple lines,
the keywords `requires` and `ensures` live on their own line.
In general the `requires` is a big conjunction,
each hypothesis should be on a separate line.
The `ensures` often contains a `let`, a `match`,
in that case extra parenthesis are needed for F\*'s parser.
Defining variables with the `let` keyword should be 
replaced by inlining the statement directly into the function that 
requires the variable if it does not blow up the statement too much.

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

# Appendix: git tricks to work with GitHub's Squash and merge


Assume a branch `featureB` builds on `featureA`,
leading to a git tree like this:

```
---o---o  main
        \
         o---o---o---o  featureA
                  \
                   o---o---o  featureB
```

Here is how to squash and merge both branches in `main`.

On GitHub: Squash and merge `featureA` in `main`

Now the git tree is:

```
        featureA
        squashed
           |
           v
---o---o---o  main
        \
         o---o---o---o  featureA
                  \
                   o---o---o  featureB
```

Locally: merge `featureA` in `featureB`

```bash
git checkout featureB
git merge featureA
```

Now the git tree is:

```
       featureA
       squashed
           |
           v
---o---o---o  main
        \
         o---o---o---o------------ featureA
                      \           \
                       o---o---o---o  featureB (last commit is a merge commit)
```

We cannot merge main without conflicts in `featureB`,
because otherwise `featureA` changes would appear twice
(once in the `featureA` commits, once in the squashed `featureA` commit in main).
The solution is the following.

Locally: rebase `featureB` on `main`

```bash
git rebase --onto main featureA
git push --force
```

Now the git tree is:

```
       featureA
       squashed
           |
           v
---o---o---o  main
        \   \
         \   o---o---o  featureB' (the commit hashes will change)
          o---o---o---o  featureA (can be deleted)
```

On GitHub: Squash and merge featureB

Now the git tree is:

```
            featureB
           squashed
               |
       featureA|
       squashed|
           |   |
           v   v
---o---o---o---o  main
        \   \
         \   o---o---o  featureB' (can be deleted)
          o---o---o---o  featureA (can be deleted)
```
