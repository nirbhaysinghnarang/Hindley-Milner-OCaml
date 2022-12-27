Hindley-Milner Type System REPL
A simple REPL for a simple programming language that includes integer constants, variables, function applications, and lambda expressions, using the Hindley-Milner type system to infer the types of expressions.

Getting Started
These instructions will get you a copy of the project up and running on your local machine for development and testing purposes.

Prerequisites
You will need an OCaml compiler or interpreter, such as the OCaml toplevel (also known as the OCaml REPL), to run this project. You can download OCaml from the official website (https://ocaml.org/docs/install.html).

Running the REPL
To start the REPL, open a terminal and enter the command ocaml. You should see a prompt like # .

Then, you can load the code for the REPL into the toplevel by copying and pasting it into the toplevel, or by using the #use "filename.ml" directive to load it from a file.

Once the code is loaded, you can start the REPL by calling the repl function, like this:

Copy code
# repl ();;
The REPL will then prompt you for input, and you can enter expressions in the language that the REPL understands. The REPL will parse your input, infer the type of the expression, and print the inferred type.

For example, you might see something like this:

Copy code
> 1
Type: Int
> x
Type: String
> (lam x:Int (plus x 1))
Type: (Int -> Int)
To exit the REPL, you can press Ctrl-D or type #exit;;.