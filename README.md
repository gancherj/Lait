# lait

## Documentation

The Lait language textbook is built with [Verso](https://github.com/leanprover/verso). See [Verso/README.md](Verso/README.md) for build and preview instructions.

```bash
lake --dir Verso exe lait-book
```

## Roadmap

- [ ] Implement type checker / type inference
   - ML-style type inference
- [ ] Hover info, good delaborators 
- [ ] Add hooks so that the top-level parser is the DSL parser

- Reimplement Steven's HW solutions in Lait

### Notes on inductive datatypes

When we declare a datatype, we can emit builtin operations for the constructors. 
For example, 
```
data List a = Nil | Cons a (List a)
```

We can emit the following builtin ops:
```
nil : List a
cons : a -> List a -> List a
```

We can represent this in Val as 
```
inductive Val where
...
| VConstructor : String -> List Val -> Val
```

Thus `nil` will be represented as `VConstructor "Nil" []` and `cons` will be represented as `VConstructor "Cons" [v1, v2]` where `v1` and `v2` are the arguments to the constructor.

(We will require that the constructor names are unique across all datatypes.)


