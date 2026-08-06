# Lait Language Reference

This page serves as a complete reference for the Lait programming language. For a user-friendly tutorial, see [here](./tutorial.md).

## Overview

Lait is a teaching-oriented programing language embedded in [Lean](https://lean-lang.org), a programming language and platform for custom languages.  
To use Lait, see the installation instructions [here](./tutorial.md).
Lait is a language in the ML family, similar to OCaml in its type system and syntax. 
Every Lait program begins with the following lines:
```lean
import Lait
#lait
```

This document is structured in a number of sections which should be read in order.
Below, we will investigate programs by using the `#eval` command, which evaluates a given expression. 
If you hover over the expression, you can see its type. 
Additionally, if you just want to type check an expression but not evaluate it, you can use the `#check` command.


## Basic Types and Operators

Lait supports the basic data types `Int` (whole numbers), `Bool` (`true` and `false`), `Str` (strings), and `Unit` (the type with only one value, `()`). 

We compute in Lait using _expressions_, which are impure computations that eventually result in _values_. 

### Integers

The values of type `Int` are whole numbers, such as `0`, `1`, `-1`, `42`, etc.
Lait expressions support multiplication, addition, and subtraction for integers. As in ML, arithmetic operators are infix and 
follow the usual rules for precedence.

```lean
#eval 1 + 2 -- 3
#eval 2 * (3 + 4) -- 14
#eval 0 - 5 -- -5
```

> [!NOTE]
> Single-line comments in Lait, inherited from Lean, start with `--`. 
> Multi-line comments begin with `/-` and end with `-/`.



### Booleans

The two values of type `Bool` are `true` and `false`.
We can compute with booleans using the operators `&&` (and), `||` (or), and `!` (negation):

```lean
#eval true && false -- false
#eval true || false -- true
#eval !true -- false
```

We can compare integers using the binary operators `<`, `>`, `<=`, and `>=`:

```lean
#eval 1 < 2 -- true
#eval 1 > 2 -- false
#eval 1 <= 2 -- true
#eval 1 >= 2 -- false
```

Additionally, certain types (including all basic types) support equality and inequality operators `==` and `!=`:

```lean
#eval 1 == 2 -- false
#eval 1 != 2 -- true
#eval true == false -- false
#eval true != false -- true
#eval "hello" == "hello" -- true
#eval "hello" != "world" -- true
#eval () == () -- true
#eval () != () -- false
```

Boolean values can be tested using `if`:

```lean
#eval if true then 1 else 2 -- 1
#eval if false then 1 else 2 -- 2
```


### Strings

Values of type `Str` are given using double quotes.
Strings support one basic operation: _concatenation_, given by `++`, which puts the two strings together.

```lean
#eval "hello" -- "hello"
#eval "hello" ++ "world" -- "helloworld"
```

### Unit

The type `Unit` has only one value, `()`.
It is used to denote a function that doesn't return anything, but is instead used for its _side effects_, such as printing (seen below).

### Function Types

Being an ML language, Lait supports function types. The syntax for function types is `s -> t`, where `s` and `t` are types.

#### Creating Functions

There are a number of ways to create functions in Lait.
We detail here the syntax for _anonymous_ functions. 

The simplest is to write `fun x => e`, where `x` is an identifier and `e` is an expression.
```lean
#check fun x => x + 1 -- Int -> Int
#check fun x => x -- ∀ a. (a -> a) 
```
Above, the first function is inferred to have type `Int -> Int` --- because we take the argument and add one to it. 
The second function has type `∀ a. (a -> a)`, because we simply return the argument; hence, we can pass a value of any type to the function.

If we want to specify the type of an argument, we can as follows:
```lean
#check fun (x : Int) => x + 1 -- Int -> Int
```
Note that we need to put parentheses around the argument and its type. 

Functions in Lait (including recursive functions) can also be created using _definitions_, detailed below.


#### Using Functions

Functions are applied by putting them side by side.
```lean
#eval (fun x => x + 1) 2 -- 3
```
Note that we need parentheses above: if we simply wrote `fun x => x + 1 2`, the expression would fail to type check, as Lait would interpret this as applying the "function" `1` to the argument `2`.


### Product Types

We can put types together to form _product types_, with syntax `t1 * t2`, where `t1` and `t2` are types. A value of type `t1 * t2` is a pair of a value of type `t1` and a value of type `t2`.

We create values of product types using tuples:
```lean
#eval (3, "hello") -- (3, "hello")
```

Given a product type, we can project out the first or second component as follows:
```lean
#eval fst (2, 3) -- 2
#eval snd (2, 3) -- 3
```

## Creating Definitions

To give a name to the result of an expression, we use the `def` keyword:
```lean
def x = 2 + 3
#eval x * 2 -- 10
```

We can give definitions type annotations as follows:

```lean
def x : Int = 2 + 3
```

If we are _inside_ an expression (i.e., not at the top level), we instead use the `let` keyword:

```lean
def foo = let x = 2 + 3 in x * 2
#eval foo -- 10
#eval let y = 2 in y * 2 -- 4
```

### Defining Functions

In addition to anonymous functions -- created using the `fun` keyword -- we can also define functions using the `def` keyword.
Functions created using `def` can be given type annotations.

```lean
def addOne x = x + 1
def addOne' (x : Int) = x + 1
def addOne'' (x : Int) : Int = x + 1
#check addOne -- Int -> Int (same as addOne' and addOne'')
```


Functions in Lait defined using `def` can have multiple arguments:
```lean
def myAdd x y = x + y
def myAdd' (x : Int) (y : Int) : Int = x + y
#check myAdd -- Int -> (Int -> Int) (same as myAdd')
```

Note that `myAdd` has type `Int -> (Int -> Int)`. This can be read in two equivalent ways:
a function taking two arguments of type `Int` and returning an `Int`; or 
a function taking _one_ argument of type `Int` and returning a new function of type `Int -> Int`.


### Recursive Functions

All functions defined using `def` are recursive by default. 
```lean
def fact n = if n == 0 then 1 else n * fact (n - 1)
#eval fact 5 -- 120
```

## Complex Data, Part I: Lists and Option

So far, we have only seen basic data types, such as `Int` and `Bool`, function types, and product types, such as `Int * Int`.
We will now move on more complex data types. 

### Lists
For any type `t`,  `List<t>` is the type of lists of values of type `t`.

#### Creating Lists
To create a list, we have the value `Nil`, which has type `List<t>` for any type `t`, and the function `Cons`, which has type `∀ a. (a -> (List<a> -> List<a>))`; that is, it takes in a value of type `a` and a list of type `List<a>` and returns a list of type `List<a>`.

```lean
#eval Cons 1 (Cons 2 (Cons 3 Nil)) -- Cons(1, Cons(2, Cons(3, Nil()))) 
```

(Note above that the empty list, when evaluated, is written as `Nil()`, not `Nil`. This is because `Nil` is a _constructor_ for a _data type_, which we will discuss in more detail later.)


#### Using Lists

To use a list, we _pattern match_ on it.
```lean
def sumList (xs : List<Int>) : Int  = 
  match xs with
  | Nil => 0
  | Cons h t => h + sumList t
  end

#eval sumList [1, 2, 3] -- 6
```
Every patern match must begin with `match e with`, where `e` is an expression; and must end with `end`.
For lists, pattern matching must analyze two cases: the `Nil` case, and the `Cons` case.

#### Abbreviations for Lists

Since lists are so common, we also have abbreviations. 
First, `Nil` and `Cons` are synonymous with `[]` and `::`.
This can be used both for creating lists and pattern matching on lists.
```lean
#eval 1 :: 2 :: 3 :: [] -- Cons(1, Cons(2, Cons(3, Nil())))

def sumList xs = 
  match xs with
  | [] => 0
  | h :: t => h + sumList t
  end
```


In addition, when making a particular list, we can use the syntax `[e1, e2, ..., en]`, where `e1`, `e2`, ..., `en` are expressions of type `t`:
```lean
#eval [1, 2, 3] -- Cons(1, Cons(2, Cons(3, Nil())))
```
Here, `[1, 2, 3]` is exactly equivalent to `1 :: 2 :: 3 :: []`, which is in turn exactly equivalent to `Cons(1, Cons(2, Cons(3, Nil())))`.

#### Common List Operations

Lait has a number of list operations built in to its standard library.

`List.append : ∀ a. (List<a> -> List<a> -> List<a>)` takes two lists and returns a new list that joins them together:
```lean
#eval List.append [1, 2, 3] [4, 5, 6] -- Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, Nil()))))))
```
Note that the name of the above function is `List.append`, including the `.`. Identifiers in Lait can include periods in the middle of them. 
We use this as a simple form of _namespacing_: instead of having `append`, `length`, and so on --- which might apply to binary trees as well as lists --- we write them as `List.append`, and `List.length`. 

`List.length : ∀ a. (List<a> -> Int)` takes a list and returns its length:
```lean
#eval List.length [1, 2, 3] -- 3
```

`List.member : ∀ a. (List<a> -> a -> Bool)` takes a list and a value and returns `true` if the value is in the list, and `false` otherwise:
```lean
#eval List.member [1, 2, 3] 2 -- true
#eval List.member [1, 2, 3] 4 -- false
```
Note that `List.member` only works for lists of types that can be compared for equality (e.g., `Int`), and will throw an error if the list contains functions.

`List.filter : ∀ a. (List<a> -> (a -> Bool) -> List<a>)` takes a list and a predicate and returns a new list that contains only the elements of the original list that satisfy the predicate:
```lean
#eval List.filter [1, 2, 3] (fun x => x >= 2) -- Cons(2, Cons(3, Nil()))
```

`List.find : ∀ a. (List<a> -> (a -> Bool) -> Option<a>)` takes a list and a predicate and returns the first element of the list that satisfies the predicate, or `None` if no element satisfies the predicate:
```lean
#eval List.find [1, 2, 3] (fun x => x >= 2) -- Some(2)
#eval List.find [1, 2, 3] (fun x => x > 3) -- None
```
(Option types are discussed below.)


### Options

Lists are one example of an _algebraic data type_, which is a data type that is built up using _constructors_ (for lists, `Nil` and `Cons`), and 
examined using pattern matching.
Another common one built in to Lait are _option_ types. 
Given a type `t`, a value of type `Option<t>` is either `None` or `Some(x)`, where `x` is a value of type `t`.
Hence, an option type is used when a value may or may not be present.

```lean
#check None -- ∀ a. Option<a>
#check Some 1 -- Option<Int>
```

To use an option type, we pattern match on it, similar to lists. Below is a worked example:
```lean
def List.getFirst (xs : List<a>) : Option<a> =
  match xs with 
  | [] => None
  | x :: _ => Some x
  end

def List.isFirstPositive (xs : List<Int>) : Bool =
  match List.getFirst xs with 
  | None => false -- List is empty, so head is not positive
  | Some x => x > 0 -- Otherwise, return whether that first element is positive
  end
```
First, we create a function `List.getFirst` that gets the first element of a list, or `None` if the list is empty.
Then, we create a function `List.isFirstPositive` that uses `List.getFirst` to get the first element if it exists; if it does, we return whether it is greater than zero. 

## Side Effects: Printing and Mutation



## Complex Data, Part II: User-Defined Types


## Throwing Errors







