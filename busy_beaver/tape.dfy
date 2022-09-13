// Generic Tape interface with all necessary post-conditions listed.
abstract module TapeInterface {
  type Symbol
  type Tape

  function Blank(init_symbol : Symbol) : Tape
    ensures forall pos :: Read(Blank(init_symbol), pos) == init_symbol

  function Read(tape : Tape, pos : int) : Symbol

  function Write(tape : Tape, pos : int, val : Symbol) : Tape
    ensures Read(Write(tape, pos, val), pos) == val
    ensures forall p2 :: p2 != pos ==>
      Read(Write(tape, pos, val), p2) == Read(tape, p2)
}

// Stack-allocated, non-mutable Tape representation convenient for
// specification
module Tape refines TapeInterface {
  // Generic Symbol type.
  type Symbol

  datatype Tape = Tape(
    data : map<int, Symbol>,
    init_symbol : Symbol
  )

  function Blank(init_symbol : Symbol) : Tape {
    Tape(data := map[], init_symbol := init_symbol)
  }

  function Read(tape : Tape, pos : int) : Symbol {
    if pos in tape.data then tape.data[pos] else tape.init_symbol
  }

  // Return a new Tape with update written.
  function Write(tape : Tape, pos : int, val : Symbol) : Tape {
    Tape(data := tape.data[pos := val],
         init_symbol := tape.init_symbol)
  }
}