# 5 Days Roadmap

1. Delete *everything* in `ast_analysis.rs`
2. Conseptually simplify Name and Path structures
3. Make the node visitor simpler
4. Reimagine a Reslover System with just TWO passes
   (`TypeResolverPass` and `LocalResolverPass`)
5. Simplify multiple files/namespaces
   - Specific (restricted) positions for `use ...` statements
   - Introduction of `unit` keyword
   - No local/inner imports, fuctions, etc ...
   -> Focus on writing everything in a single file for now
      (mulitple file support could arise with the linking process)
6. Create a System where Names are Resolved to thier declaring nodes


## TypeResolutionPass
- Collect all the TopLevel Structs, Functions, etc ...
- Associate `Ident` <-> `NodeId` of `Declaration`
- Build a HashMap for every `Subspace` (types, functions, globals)

## NameResolutionPass
- Visit Items [Globals (Vars, Consts), Types, Functions]
- Resolve Names depending on thier Enviroment (Types, Functions, Variables)
- Drive each QName to a Resolved state 

## Done (If you focus on small steps at a time you can get smth done)

# Passes vs Queries

## How should data flow through the compiler?

### Advantages
- Rust model makes a little bit more sense as not everything has to be structured
  and perfect right then and there.
- Changes (new queries) can simply be added and used. It probably rarely requires
  huge refactorings.
- Data can be nicely abstracted using TyCtxt. It can always be querried right then
  and there, while directly after forgetting that it ever exitsted. As the data is
  interned, it can be forgotten about, until you query it again.

### Disatvantages
- Pass bases sytems are way easier to reason about during the early development of
  the compiler. Less vauge ideas, correleates with more clear momentum.
- Query based sytems aren't really explored (as far as I know: rustc is the only
  one) I don't really know how they perform or scale.
- In a query based system everything kinda has to be thought backwards. But I don't
  realldy know if the current time is really that good for a lot of structural design
  backwards thinking.
- I could easily reason about what passes you might need in order to create a compiler
  but what kind of queries and how to structure them really is a harder challange.

## Do the simplest thing first: passes for now, queries for later

lex -> parse -> resolve -> type normalisation 

# Type Normalisation
Convert all types from ast::TypeExpr into &'tcx types::Ty, in order to NORMALIZE the types

