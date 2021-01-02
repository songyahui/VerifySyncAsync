open String
open List
open Printf
open Int32



type ('a, 'b) promise = P | F of 'a | R of 'b

type reaction = Lam | Default

type ('a, 'b) promise_react = (reaction * ('a, 'b) promise ref)

type ('a, 'b) fulfillReactions = (('a, 'b) promise ref * ('a, 'b) promise_react list )

type ('a, 'b) rejectReactions = (('a, 'b) promise ref * ('a, 'b) promise_react list )

type ('a, 'b) queue = (('a, 'b) promise * reaction * ('a, 'b) promise ref) list


exception Foo of string

let () = print_string ("yahui song")