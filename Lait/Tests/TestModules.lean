import Lait.Elab
import Lait.Stdlib

/-!
# Modules and `#include`

A `{lait_decl NAME ... }` block is a named Lait module.  `#include NAME` splices
another module's declarations in, in place.  There is no namespacing and no
selective import: everything the included module defines becomes a top-level
name here, and clashes are errors (TestDuplicate.lean).

`#include` is idempotent, which is what makes diamonds work.
-/

-- ===== A module to include =====

{lait_decl modBase
  #include stdlib

  def base := 1
  type Fruit := | Apple | Pear
  def name (f : Fruit) : String :=
    match f with
    | Apple => "apple"
    | Pear => "pear"
    end
}

{lait_decl modUsesBase
  #include modBase

  -- Everything `modBase` defined is in scope, unqualified.
  #test base === 1
  #test name Apple === "apple"

  -- ...including what `modBase` itself included, transitively.
  #test List.length [1, 2] === 2
  #test Some 1 === Some 1
}

-- ===== Idempotence, and diamonds =====

{lait_decl modMiddleA
  #include modBase
  def middleA := base + 1
}

{lait_decl modMiddleB
  #include modBase
  def middleB := base + 2
}

-- Both branches include `modBase`; the second `#include` is a no-op, so `base`
-- is not defined twice.
{lait_decl modDiamond
  #include modMiddleA
  #include modMiddleB
  #test base === 1
  #test middleA === 2
  #test middleB === 3
}

-- Twice directly is likewise fine.
{lait_decl modIncludeTwice
  #include modBase
  #include modBase
  #test base === 1
}

-- ===== Order matters =====

-- `#include` splices at the point it appears.
/-- error: Variable base not found -/
#guard_msgs in
{lait_decl modIncludeTooLate
  def usesBase := base + 1
  #include modBase
}

{lait_decl modIncludeInTime
  #include modBase
  def usesBase := base + 1
  #test usesBase === 2
}

-- ===== Included names are ordinary top-level names =====

-- They may not be redefined...
/-- error: base is already defined -/
#guard_msgs in
{lait_decl modClash
  #include modBase
  def base := 2
}

-- ...nor a type they declare.
/-- error: Type Fruit is already defined -/
#guard_msgs in
{lait_decl modTypeClash
  #include modBase
  type Fruit := | Cherry
}

-- ...nor a constructor, which is spliced in as a `def`.
/-- error: Apple is already defined -/
#guard_msgs in
{lait_decl modCtorClash
  #include modBase
  def Apple := 1
}

-- A local binder may shadow one freely.
{lait_decl modShadowing
  #include modBase
  #test (let base := 99 in base) === 99
  #test base === 1
  def f (base : Int) : Int := base
  #test f 7 === 7
}

-- ===== Unknown modules =====

/-- error: unknown lait module `noSuchModule` -/
#guard_msgs in
{lait_decl modUnknown
  #include noSuchModule
}

-- ===== Modules are not values =====

-- No qualified access: `modBase.base` is just an identifier with a dot in it.
-- (`List.length` works because that is literally the stdlib `def`'s name.)
/-- error: Variable modBase.base not found -/
#guard_msgs in
{lait_decl modNoQualifiedAccess
  #include modBase
  #eval modBase.base
}
