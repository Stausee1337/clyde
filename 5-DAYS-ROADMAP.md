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
