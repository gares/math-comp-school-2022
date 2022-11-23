Main Coqdoc feature were:

## Comments

- Coqdoc comments start with `(** ... *)`
- Sections are:
  + `(** * Title *)`: h1
  + `(** ** Title *)`: h2
  + `(** *** Title *)`: h3
  + `(** **** Title *)`: h4
- Code is enclosed between brackets `[fun x => x]`
- Emphasis `_[fun x => x]_`
- Escaping: `$ latex $`, `# html #`, unfortunately they were discarded in each other.
- Inline code is:
````
[[
code
]]
````
  Note they are required to start a line.

- Verbatim:
````
<<
code
>>
````
- Rules: `----` or more.
- List items: leading dash. It uses whitespace to determine the depth of a new list.

  A list ends when a line of text starts at or before the level of
  indenting of the list’s dash.

  A list item’s dash must always be the first non-space character on
  its line (so, in particular, a list can not begin on the first line
  of a comment - start it on the second line instead).

````
We go by induction on [n]:
 - If [n] is 0...
 - If [n] is [S n'] we require...
   two paragraphs of reasoning, and two subcases:

   - In the first case...
   - In the second case...

So the theorem holds.
````

- Hide/Show

````
(* begin hide *)
some Coq material
(* end hide *)
Conversely, some parts of the source which would be hidden can be shown using such comments:

(* begin show *)
some Coq material
(* end show *)
````

## Extensions

Markdown `(*[md] *)`
