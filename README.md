# ocaml-alab-mode

## Requires
* OCaml 4.02.1
* Cocoa Emacs / Aquamacs
* ocp-indent

## Install
1. compile the source

`make`

check if you successfully made `expander*`

2. load `hole.el` to your Emacs

## key-words
* `hole`
This is the OCaml expression `exit(*{ }*)`, or the real appearance of `goal`.

* `goal`
This is the appearance after users load their OCaml program using `\C-cg`, looks lile `{ }n` (n: Nat).

## Commands
### insert `hole`: `\C-ch`
The command calls the function `put-hole` in `hole.el`

### Load your OCaml file with hole: `\C-cg`
The command calls the function `agda2-go` in `hole.el`

### Remove the hole that you are in: `\C-cc`
The command calls the function `agda2-forget-this-goal` in `hole.el`

### Put back all `goal`s to `hole`s: `\C-cf`
The command calls the function `agda2-forget-all-goals` in `hole.el`

### Refine goal (without any arguments): `\C-cr`
The command calls the function `refine-goal` in `hole.el`

### Refine goal with an expression: `\C-c,`
The command calls the function `refine-goal-with-argument` in `hole.el`
* Now this function only remove the hole the user are in, and insert the expression the user input.

### Match a variable in the hole: `\C-cm`
The command calls the function `match-variable` in `hole.el`

### Show the type of `goal` and its environment: `\C-cs`
The command calls the function `show-goal` in `hole.el`

