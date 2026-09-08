import Lait.Elab
import Lait.Stdlib

/-!
# Scoping and shadowing

One namespace for terms, one for types.  Top-level names are unique
(TestDuplicate.lean has the clash errors); local binders -- `fun`, `let`, `fix`,
and `match` pattern variables -- may shadow anything, including each other,
top-level `def`s, and constructors.
-/

{lait_decl scopeShadowing
  #include stdlib

  def x := 1

  -- Each binder form shadows.
  #test (fun x => x) 2 === 2
  #test (let x := 3 in x) === 3
  #test x === 1

  -- Innermost wins, and the outer one comes back.
  #test (let x := 2 in (let x := 3 in x) + x) === 5

  -- A parameter shadows a top-level `def` for the whole body.
  def f (x : Int) : Int := x * 10
  #test f 2 === 20
  #test x === 1

  -- ...and a `let` in a body shadows the parameter.
  def g (y : Int) : Int := let y := y + 1 in y * 10
  #test g 1 === 20

  -- Pattern variables shadow too.
  def h (xs : List<Int>) : Int :=
    match xs with
    | [] => x
    | x :: _ => x
    end
  #test h [7] === 7
  #test h [] === 1

  -- `fix` binds its own name.
  #test (fix x. fun (n : Int) => if n == 0 then 0 else x (n - 1)) 3 === 0
}

{lait_decl scopeShadowingConstructors
  #include stdlib

  -- A local binder may shadow a constructor name.  Once shadowed it is an
  -- ordinary variable: no longer applicable as a constructor, and not usable in
  -- a pattern to mean the local value.
  #test (let Some := 5 in Some) === 5
  #test (fun Some => Some + 1) 1 === 2

  -- Unaffected outside the binder.
  #test Some 1 === Some 1

  -- Shadowing a constructor is what makes an application expansive for the
  -- value restriction; see TestValueRestriction.lean.
}

{lait_decl scopeWildcard
  #include stdlib

  -- `_` is legal wherever a name is.
  #test (fun _ => 1) 99 === 1
  #test (let _ := 1 in 2) === 2

  -- Several `_`s in one pattern, and several `def _`s, are fine: `_` is not a
  -- name, so it never clashes.
  def _ := ()
  def _ := ()

  def snd2 (xs : List<Int>) : Int :=
    match xs with
    | [] => 0
    | _ :: t =>
      match t with
      | [] => 0
      | h :: _ => h
      end
    end
  #test snd2 [1, 2, 3] === 2
}

-- CURRENT BEHAVIOR: `_` is not a true wildcard but an ordinary binder whose name
-- is `_`, so it can be read back, and an inner `_` shadows an outer one.  Only
-- the top-level duplicate-name check special-cases it.  REPORT.md P14.
{lait_decl scopeWildcardIsReferenceable
  #test (fun _ => _) 1 === 1
  #test (let _ := 5 in _) === 5
  #test (let _ := 5 in let _ := 6 in _) === 6
}

-- ===== Duplicate binders in a pattern =====

-- CURRENT BEHAVIOR: `| h :: h =>` is accepted, the second `h` shadowing the
-- first, rather than rejected as a repeated binder.  REPORT.md P13.
{lait_decl scopeDuplicatePatternBinder
  #include stdlib
  def f (xs : List<Int>) : Int :=
    match xs with
    | [] => 0
    | h :: h => 1
    end
  #test f [1, 2] === 1
}

-- ===== The two namespaces are separate =====

{lait_decl scopeTermsAndTypes
  #include stdlib

  -- A type and a term may share a name.
  type Box := | MkBox (v : Int)
  def Box := 1
  #test Box === 1
  #test MkBox 1 === MkBox 1
  def useBoxType (b : Box) : Int := match b with | MkBox v => v end
  #test useBoxType (MkBox 2) === 2
}

-- ===== Type variables are scoped to one declaration =====

{lait_decl scopeTypeVariables
  #include stdlib

  -- The `a` in one `def` is unrelated to the `a` in the next.
  def first (p : a * b) : a := fst p
  def second (p : a * b) : b := snd p
  #test first (1, "s") === 1
  #test second (1, "s") === "s"

  -- ...so they instantiate independently.
  #test first ("s", 1) === "s"
}

-- ===== Reserved words =====

-- `true`/`false` are deliberately not reserved tokens, so they can still be used
-- as identifiers in binding positions such as constructor argument names.
{lait_decl scopeBoolNames
  type Flags := | MkFlags (true : Int) (false : String)
  #test (match MkFlags 1 "f" with | MkFlags a b => a end) === 1
  #test (match MkFlags 1 "f" with | MkFlags a b => b end) === "f"
}

-- They are pre-defined term names, so `def true` is rejected...
/-- error: true is already defined -/
#guard_msgs in
{lait_decl scopeDefTrue
  def true := 1
}

-- ...and so, separately, is a `let` binding them, by `checkBannedLetName`.
-- NOTE: TestDuplicate.lean's `shadowBuiltinOk` still asserts the opposite, and
-- is red because of it.  REPORT.md X1.
/-- error: Cannot redefine true here -/
#guard_msgs in
{lait_decl scopeLetTrue
  #test (let true := 1 in 2) === 2
}

/-- error: Cannot redefine false here -/
#guard_msgs in
{lait_decl scopeLetFalse
  #eval let false := 1 in 2
}
