

syntax
======

The character '#' introduces a comment until the end of the line (if it is at the beginning of a word).
Otherwise newlines only matter as whitespace.
The code should consist of a list of words, where some words are pre-defined keywords an other words are user-defined.
A word is something that is separated by whitespaces, e.g. `+-a9a` is a single word.

Groups of words can form an expression.
An expression can be a <type>, <term>, or <theorem>.
A <term> always has a type associated with it.
A theorem usually stands for a <term> of type `bool`,
but not all such terms are theorems.

useage of the program
=====================
The program gets a filename as the argument.
It parses the file by trying to parse a <theorem>.
The file should contain exactly a single <theorem>.

If you have cargo installed and want to verify math_main, you can also use
$ cargo run math_main

creating types
==============

There are two basic types, `bool` and `set`.
If `x` and `y` are types, then `pred x` is a type that describes the predicates on `x` (functions from `x` to `bool`), and `pairs x y` describes the type of (ordered) pairs of `x` and `y`.

creating terms
==============

pairs
-----
`: a b` 
refers to the pair of `a` and `b` and has type
`pairs x y`, where `x` and `y` are the types of `a` and `b`.

`fst c` and `snd c`
refer to the first component and second component of `c`,
where `c` must have a type of the form `pairs x y`
(then `fst c` has type `x` and `snd c` has type `y`).

functions
---------
`. a b` 
refers to the result of the function `a` applied to the input `b`.
If `x` is the type of `b`, then `a` must have type `pred x`.
The expression `. a b` has type `bool`.

`\ v x a`
refers to a function/lambda expression of type `pred x`.
Here, `v` introduces a local variable of type `x`, and `a` is a term of type `bool`
which can use the local variable `v`.

implication
-----------
`->` 
is of type `pred pairs bool bool` and is the implication symbol.
`. -> : a b` means that `a` implies `b`.

for all
-------
`! x`
is of type `pred pred x` and is the symbol for "for all".
The expression `. ! x f`, where `f` is of type `pred x`, 
means that `f a` is true for all `a` of type `x`.


creating theorems
=================


introducing a new variable
--------------------------
`$var v t T`

introduces a variable with name `v` of type `t`.
The variable name has to be new in the current scope (eg local variables elsewhere with the same name are ok).
Then it continuous parsing a theorem `T`, where it can use that new variable `v`.
The result is a theorem `. ! \ v t T`, which states that `T` holds for all `v` of type `t`.

introducing assumptions
-----------------------
`$asm a b T`

introduce an assumption with name `a` (which has to be a new word).
Here, `b` is of type bool and refers to the thing that is being assumed.
Then it continuous parsing a theorem `T`, where it can use the new assumption as a theorem.
The result is a theorem `. -> : b T`, which states that `b` implies `T`.

defining terms
--------------
`$def x a T`

defines `x` to be `a`. Here, `x` has to be a new word.
Then it continuous parsing a theorem `T`, where `x` can be used as a local variable to refer to `a`.
The type `t` of `x` gets inferred from the type of `a`.
The result is a theorem `. \ x t T a`.

proving and matching
--------------------
`$prove b T`

matches a term `b` of type `bool` with a theorem.
This is helpful for reformulating theorems,
or stating a theorem in a legible form before actually proving it.
The matching algorithm is powerful (eg it does things like beta reduction and replacing definitions automatically).


modus ponens
------------
`$mp a p`

Can conclude `q` from "`p` implies "`q`" and `p`.
Tries to deconstruct a theorem `a` into the form `. -> : x y`.
Tries to match `x` with theroem `p`.
If succesful, the result is a theorem that states `y`.

specialization
--------------
`$spec a b`

In a "for-all" theorem, use the concrete value `b`.
Tries to deconstruct a theorem `a` into the form `. ! x f`.
If sucessful, the result is a theorem that states `. f b`.

printing
--------
`$print w T`

prints `w` (which can be a theorem or a term) and continues parsing a theorem.

Quick reference
===============

bool                       ==> <type>   the type `bool`
set                        ==> <type>   the type `set`
pred <type>                ==> <type>   predicates, ie functions from x to `bool`
pairs <type> <type>        ==> <type>   the type of pairs of x and y

. <term, `pred x`> <term, `x`>      ==> <term,`bool`>                    function application
\ <new_word> <type (x)> <term, `x`> ==> <term, `bool`>                   lambda expression
: <term, `x`> <term, `y`>           ==> <term, `pairs x y`>              a pair
fst <term, `pairs x y`>             ==> <term, `x`>                      first component of a pair
snd <term, `pairs x y`>             ==> <term, `y`>                      second component of a pair
->                                  ==> <term, `pred pairs bool bool`>   implication
! <type (x)>                        ==> <term, `pred pred x`>            forall x ...


$var <new_word> <type> <theorem>         ==> <theorem>        introduce a new variable, continues parsing a <theorem>
$asm <new_word> <bool> <theorem>         ==> <theorem>        make an assumption, continues parsing a <theorem>
$thm <new_word> <theorem> <theorem>      ==> <theorem>        defines a named theorem, continues parsing a <theorem>
$def <new_word> <term, `x`> <theorem>    ==> <theorem>        defines a term, continues parsing a <theorem>
$prove <term, `bool`> <theorem>          ==> <theorem>        matches a bool-term to a theorem
$spec <theorem> <term, `x`>              ==> <theorem>        specialization with a term `y` (from `. ! x f` to `. f y)
$mp <theorem> <theorem>                  ==> <theorem>        modus ponens (from `. -> : p q` and `p` to `q`)
$print <known_word> <theorem>            ==> <theorem>        prints a known word (theorem or term) and continues parsing a <theorem>

