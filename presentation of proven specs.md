# Presentation of proven specs

## The problem

Very hard to look at a large repo containing Rust source code and Lean proof code (like the lean-dalek project) and know precisely what is proven. 

## The idea

A verso powered page which shows the signature of each spec theorem together with its staus (i.e., what axioms does it depend on). 

- Page is ordered logically so it is easy to find details, see an overview of what is proven. 
- Page also needs to show the custom definitions which are required to understand the statements. 
- Page needs to be live in the sense that if a spec theorem statement is changed of is not proven, then this shows on the page.

## Sources of truth:

- Manifest json which links Rust name of function to Lean name of function and displays the public status of each function
- Lean project contains the spec theorems

- Proof status is obtained from the Lean (i.e., print_axioms).  