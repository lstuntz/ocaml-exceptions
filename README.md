# ocaml-exceptions
### An extension of the typed lambda calculus to catch and handle exceptions in OCamL. 
#### UVM CS 225 Final Project. Apr. 2018.


Make sure you have ocaml 4.06.0, and ppx_deriving installed.
```
opam switch 4.06.0
opam install ppx_deriving
```
There are two special files in this directory which help merlin and ocamlbuild
know how to build the project.

First, there is a hidden file .merlin which instructs merlin to:
1. find source files in this directory
2. find build files in the _build directory
3. use the ppx_deriving.std package when checking files

Next, there is a special file _tags which instructs ocamlbuild to:
1. use the ppx_deriving.std package when compiling files

There is an included Makefile that will build all *.ml files in the current
directory as the default target:
```
make
```
If you want to execute a file, for example, exceptions.ml, just execute:
```
make exceptions
```
Running either of these commands will generate a bunch of compiled files. These
will get placed in the _build directory, and that directory will be created
automatically if it doesn't already exist. To get rid of the _build directory,
just execute:
```
make clean
```